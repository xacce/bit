from collections import namedtuple
from itertools import islice
import re

from bit.crypto import double_sha256, sha256
from bit.exceptions import InsufficientFunds
from bit.format import address_to_public_key_hash, TEST_SCRIPT_HASH, MAIN_SCRIPT_HASH
from bit.network import NetworkAPI
from bit.network.rates import currency_to_satoshi_cached
from bit.utils import (
    bytes_to_hex, chunk_data, hex_to_bytes, int_to_unknown_bytes, int_to_varint, script_push, get_signatures_from_script
)

from bit.format import verify_sig
from bit.base58 import b58decode_check

VERSION_1 = 0x01.to_bytes(4, byteorder='little')
SEQUENCE = 0xffffffff.to_bytes(4, byteorder='little')
LOCK_TIME = 0x00.to_bytes(4, byteorder='little')
HASH_TYPE = 0x01.to_bytes(4, byteorder='little')

OP_0 = b'\x00'
OP_CHECKLOCKTIMEVERIFY = b'\xb1'
OP_CHECKSIG = b'\xac'
OP_DUP = b'v'
OP_EQUALVERIFY = b'\x88'
OP_HASH160 = b'\xa9'
OP_PUSH_20 = b'\x14'
OP_RETURN = b'\x6a'
OP_EQUAL = b'\x87'

MESSAGE_LIMIT = 40


class TxIn:
    __slots__ = ('script', 'script_len', 'txid', 'txindex', 'witness', 'amount', 'sequence', 'segwit')

    def __init__(self, script, txid, txindex, witness=b'', amount=0, sequence=SEQUENCE, segwit=False):
        self.script = script
        self.script_len = int_to_varint(len(script))
        self.txid = txid
        self.txindex = txindex
        self.witness = witness
        if amount == 0:
            amount = NetworkAPI.get_tx_amount(bytes_to_hex(self.txid[::-1]), int.from_bytes(self.txindex, byteorder='little')).to_bytes(8, byteorder='little')
        self.amount = amount
        self.sequence = sequence
        self.segwit = segwit

    def __eq__(self, other):
        return (self.script == other.script and
                self.script_len == other.script_len and
                self.txid == other.txid and
                self.txindex == other.txindex and
                self.witness == other.witness and
                self.amount == other.amount and
                self.sequence == other.sequence and
                self.segwit == other.segwit)

    def __repr__(self):
        return 'TxIn({}, {}, {}, {}, {}, {}, {}, {})'.format(
            repr(self.script),
            repr(self.script_len),
            repr(self.txid),
            repr(self.txindex),
            repr(self.witness),
            repr(self.amount),
            repr(self.sequence),
            repr(self.segwit)
        )
    def __bytes__(self):
        return b''.join([
            self.txid,
            self.txindex,
            self.script_len,
            self.script,
            self.sequence
        ])


Output = namedtuple('Output', ('address', 'amount', 'currency'))


class TxOut:
    __slots__ = ('value', 'script_len', 'script')

    def __init__(self, value, script):
        self.value = value
        self.script = script
        self.script_len = int_to_varint(len(script))

    def __eq__(self, other):
        return (self.value == other.value and
                self.script == other.script and
                self.script_len == other.script_len)

    def __repr__(self):
        return 'TxOut({}, {}, {})'.format(
            repr(self.value),
            repr(self.script),
            repr(self.script_len)
        )
    def __bytes__(self):
        return b''.join([
            self.value,
            self.script_len,
            self.script
        ])


class TxObj:
    __slots__ = ('version', 'TxIn', 'input_count', 'TxOut', 'output_count', 'locktime')

    def __init__(self, version, TxIn, TxOut, locktime):
        self.version = version
        self.TxIn = TxIn
        self.input_count = len(TxIn)
        self.TxOut = TxOut
        self.output_count = len(TxOut)
        self.locktime = locktime

    def __eq__(self, other):
        return (self.version == other.version and
                self.TxIn == other.TxIn and
                self.input_count == other.input_count and
                self.TxOut == other.TxOut and
                self.output_count == other.output_count and
                self.locktime == other.locktime)

    def __repr__(self):
        return 'TxObj({}, {}, {}, {})'.format(
            repr(self.version),
            repr(self.TxIn),
            repr(self.TxOut),
            repr(self.locktime)
        )

    def __bytes__(self):
        inp = int_to_varint(len(self.TxIn)) + b''.join(map(bytes, self.TxIn))
        out = int_to_varint(len(self.TxOut)) + b''.join(map(bytes, self.TxOut))
        wit = b''.join(map(lambda w: w.witness, self.TxIn))
        return b''.join([
            self.version,
            inp,
            out,
            wit,
            self.locktime
        ])

def calc_txid(tx_hex):
    return bytes_to_hex(double_sha256(hex_to_bytes(tx_hex))[::-1])


def estimate_tx_fee(n_in, n_out, satoshis, compressed):

    if not satoshis:
        return 0

    estimated_size = (
        n_in * (148 if compressed else 180)
        + len(int_to_unknown_bytes(n_in, byteorder='little'))
        + n_out * 34
        + len(int_to_unknown_bytes(n_out, byteorder='little'))
        + 8
    )

    return estimated_size * satoshis


def deserialize(txhex, sw_dict={}, sw_scriptcode=None):
# sw_dict is a dictionary containing segwit-inputs' txid concatenated with txindex using ":" mapping to information of the amount the input contains.
# E.g.: sw_dict = {'txid:txindex': amount, ...}
    if isinstance(txhex, str) and re.match('^[0-9a-fA-F]*$', txhex):
        return deserialize(hex_to_bytes(txhex), sw_dict, sw_scriptcode)

    if txhex[4:6] == b'\x00\x01':  # ``marker|flag'' == 0001 if segwit-transaction
        segwit = True
    else:
        segwit = False

    pos = [0]

    def read_as_int(bytez):
        pos[0] += bytez
        return int(bytes_to_hex(txhex[pos[0]-bytez:pos[0]][::-1]), base=16)

    def read_var_int():
        pos[0] += 1

        val = int(bytes_to_hex(txhex[pos[0]-1:pos[0]]), base=16)
        if val < 253:
            return val
        return read_as_int(pow(2, val - 252))

    def read_bytes(bytez):
        pos[0] += bytez
        return txhex[pos[0]-bytez:pos[0]]

    def read_var_string():
        size = read_var_int()
        return read_bytes(size)

    def read_segwit_string():
        size = read_var_int()
        return int_to_varint(size)+read_bytes(size)

    version = read_as_int(4).to_bytes(4, byteorder='little')

    if segwit:
        _ = read_as_int(1).to_bytes(1, byteorder='little')  # ``marker`` is read
        _ = read_as_int(1).to_bytes(1, byteorder='little')  # ``flag`` is read

    ins = read_var_int()
    inputs = []
    for i in range(ins):
        txid = read_bytes(32)
        txindex = read_as_int(4).to_bytes(4, byteorder='little')
        script = read_var_string()
        sequence = read_as_int(4).to_bytes(4, byteorder='little')
        # Check if input is segwit:
        tx_input = bytes_to_hex(txid) + ':' + bytes_to_hex(txindex)
        sw = True if (sw_scriptcode == script[1:] or tx_input in sw_dict) else False  # Partially-signed segwit-multisig input or input provided in sw_dict.
        amount = sw_dict[tx_input] if tx_input in sw_dict else 0  # Read ``amount`` from sw_dict if it is provided.
        inputs.append(TxIn(script, txid, txindex, b'', amount, sequence, sw))

    outs = read_var_int()
    outputs = []
    for _ in range(outs):
        value = read_as_int(8).to_bytes(8, byteorder='little')
        script = read_var_string()
        outputs.append(TxOut(value, script))

    if segwit:
        for i in range(ins):
            wnum = read_var_int()
            witness = int_to_varint(wnum)
            for _ in range(wnum):
                witness += read_segwit_string()
            inputs[i].witness = witness

    locktime = read_as_int(4).to_bytes(4, byteorder='little')

    txobj = TxObj(version, inputs, outputs, locktime)

    return txobj


def sanitize_tx_data(unspents, outputs, fee, leftover, combine=True, message=None, compressed=True):

    outputs = outputs.copy()

    for i, output in enumerate(outputs):
        dest, amount, currency = output
        outputs[i] = (dest, currency_to_satoshi_cached(amount, currency))

    if not unspents:
        raise ValueError('Transactions must have at least one unspent.')

    # Temporary storage so all outputs precede messages.
    messages = []

    if message:
        message_chunks = chunk_data(message.encode('utf-8'), MESSAGE_LIMIT)

        for message in message_chunks:
            messages.append((message, 0))

    # Include return address in fee estimate.
    fee = estimate_tx_fee(len(unspents), len(outputs) + len(messages) + 1, fee, compressed)
    total_out = sum(out[1] for out in outputs) + fee

    total_in = 0

    if combine:
        unspents = unspents.copy()
        total_in += sum(unspent.amount for unspent in unspents)

    else:
        unspents = sorted(unspents, key=lambda x: x.amount)

        index = 0

        for index, unspent in enumerate(unspents):
            total_in += unspent.amount

            if total_in >= total_out:
                break

        unspents[:] = unspents[:index + 1]

    remaining = total_in - total_out

    if remaining > 0:
        outputs.append((leftover, remaining))
    elif remaining < 0:
        raise InsufficientFunds('Balance {} is less than {} (including '
                                'fee).'.format(total_in, total_out))

    outputs.extend(messages)

    return unspents, outputs


def construct_outputs(outputs):
    outputs_obj = []

    for data in outputs:
        dest, amount = data

        # Future-TODO: Add BIP-173 bech32 SegWit addresses.
        # P2SH
        if amount and (b58decode_check(dest)[0:1] == MAIN_SCRIPT_HASH or
                       b58decode_check(dest)[0:1] == TEST_SCRIPT_HASH):
            script = (OP_HASH160 + OP_PUSH_20 +
                      address_to_public_key_hash(dest) +
                      OP_EQUAL)

            amount = amount.to_bytes(8, byteorder='little')

        # P2PKH
        elif amount:
            script = (OP_DUP + OP_HASH160 + OP_PUSH_20 +
                      address_to_public_key_hash(dest) +
                      OP_EQUALVERIFY + OP_CHECKSIG)

            amount = amount.to_bytes(8, byteorder='little')

        # Blockchain storage
        else:
            script = (OP_RETURN +
                      len(dest).to_bytes(1, byteorder='little') +
                      dest)

            amount = b'\x00\x00\x00\x00\x00\x00\x00\x00'

        outputs_obj.append(TxOut(amount, script))

    return outputs_obj


def construct_witness_block(inputs):
    witness_block = b''

    for txin in inputs:
        witness_block += txin.witness

    return witness_block


def construct_input_block(inputs):

    input_block = b''
    sequence = SEQUENCE

    for txin in inputs:
        input_block += (
            txin.txid +
            txin.txindex +
            txin.script_len +
            txin.script +
            sequence
        )

    return input_block

def sign_tx(private_key, tx, j=-1):  # Future-TODO: add sw_dict to allow override of segwit input dictionary?
# j is the input to be signed and can be a single index, a list of indices, or denote all inputs (-1)

    if not isinstance(tx, TxObj):
        # Add sw_dict containing unspent segwit txid:txindex and amount to deserialize tx:
        sw_dict = {}
        unspents = private_key.unspents
        for u in unspents:
            if u.segwit:
                tx_input = u.txid+':'+str(u.txindex)
                sw_dict[tx_input] = u.amount
        tx = deserialize(tx, sw_dict, private_key.sw_scriptcode)

    version = tx.version
    marker = b'\x00'
    flag = b'\x01'
    lock_time = tx.locktime
    hash_type = HASH_TYPE

    input_count = int_to_varint(tx.input_count)
    output_count = int_to_varint(tx.output_count)

    output_block = b''
    for i in range(tx.output_count):
        output_block += tx.TxOut[i].value
        output_block += tx.TxOut[i].script_len
        output_block += tx.TxOut[i].script

    hashPrevouts = double_sha256(b''.join([i.txid+i.txindex for i in tx.TxIn]))
    hashSequence = double_sha256(b''.join([i.sequence for i in tx.TxIn]))
    hashOutputs = double_sha256(b''.join([bytes(o) for o in tx.TxOut]))

    if j<0:  # Sign all inputs
        j = range(len(tx.TxIn))
    elif not isinstance(j, list):  # Sign a single input
        j = [j]

    segwit = False  # Global check if at least one input is segwit

    for i in j:
        # Check if input is segwit or non-segwit:
        sw = tx.TxIn[i].segwit
        segwit = segwit or sw  # Global check if at least one input is segwit => Transaction must be of segwit-format

        public_key = private_key.public_key
        public_key_len = script_push(len(public_key))

        scriptCode = private_key.scriptcode
        scriptCode_len = int_to_varint(len(scriptCode))

        if sw == False:
            hashed = sha256(
                version +
                input_count +
                b''.join(ti.txid + ti.txindex + OP_0 + ti.sequence
                         for ti in islice(tx.TxIn, i)) +
                tx.TxIn[i].txid +
                tx.TxIn[i].txindex +
                scriptCode_len +
                scriptCode +
                tx.TxIn[i].sequence +
                b''.join(ti.txid + ti.txindex + OP_0 + ti.sequence
                         for ti in islice(tx.TxIn, i + 1, None)) +
                output_count +
                output_block +
                lock_time +
                hash_type
                )

            input_script_field = tx.TxIn[i].script

        else:
            hashed = sha256(  # BIP-143: Used for Segwit
                version +
                hashPrevouts +
                hashSequence +
                tx.TxIn[i].txid +
                tx.TxIn[i].txindex +
                scriptCode_len +
                scriptCode +
                tx.TxIn[i].amount +
                tx.TxIn[i].sequence +
                hashOutputs +
                lock_time +
                hash_type
                )

            input_script_field = tx.TxIn[i].witness

        signature = private_key.sign(hashed) + b'\x01'

        # ------------------------------------------------------------------
        if private_key.instance == 'MultiSig' or private_key.instance == 'MultiSigTestnet':
            # P2(W)SH input

            script_blob = b''
            sigs = {}
            if input_script_field:  # If tx is already partially signed: Make a dictionary of the provided signatures with public-keys as key-values
                sig_list = get_signatures_from_script(input_script_field)
                if len(sig_list) > private_key.m:
                    raise TypeError('Transaction is already signed with {} of {} needed signatures.').format(len(sig_list), private_key.m)
                for sig in sig_list:
                    for pub in private_key.public_keys:
                        if verify_sig(sig[:-1], hashed, hex_to_bytes(pub)):
                            sigs[pub] = sig
                script_blob += b'\x00' * (private_key.m - len(sig_list)-1)  # Bitcoin Core convention: Every missing signature is denoted by 0x00. Only used for already partially-signed scriptSigs.

            sigs[bytes_to_hex(public_key)] = signature

            witness = b''
            witness_count = 2  # count number of witness items (OP_0 + each signature + redeemscript).
            for pub in private_key.public_keys:  # Sort the signatures according to the public-key list:
                if pub in sigs:
                    sig = sigs[pub]
                    length = int_to_varint(len(sig)) if sw == True else script_push(len(sig))
                    witness += length + sig
                    witness_count += 1

            script_sig = b'\x22' + private_key.sw_scriptcode

            witness = (witness_count.to_bytes(1, byteorder='little') if sw == True else b'') + b'\x00' + witness + script_blob
            witness += (int_to_varint(len(private_key.redeemscript)) if sw == True else script_push(len(private_key.redeemscript))) + private_key.redeemscript

            script_sig = witness if sw == False else script_sig
            witness = b'\x00' if sw == False else witness

        # ------------------------------------------------------------------
        else:
            # P2(W)PKH input

            script_sig = b'\x16' + private_key.sw_scriptcode

            witness = (
                      (b'\x02' if sw == True else b'') +  # witness counter
                      len(signature).to_bytes(1, byteorder='little') +
                      signature +
                      public_key_len +
                      public_key
                     )

            script_sig = witness if sw == False else script_sig
            witness = b'\x00' if sw == False else witness

        tx.TxIn[i].script = script_sig
        tx.TxIn[i].script_len = int_to_varint(len(script_sig))
        tx.TxIn[i].witness = witness

    return bytes_to_hex(
        version +
        (marker if segwit == True else b'') +
        (flag if segwit == True else b'') +
        input_count +
        construct_input_block(tx.TxIn) +
        output_count +
        output_block +
        (construct_witness_block(tx.TxIn) if segwit == True else b'') +
        lock_time
    )
    # Future-TODO: Add return of redeemscript, etc if multisig and not fully signed yet to sign offline or using bitcoin core.


def create_new_transaction(private_key, unspents, outputs):

    version = VERSION_1
    lock_time = LOCK_TIME
    outputs = construct_outputs(outputs)

    # Optimize for speed, not memory, by pre-computing values.
    inputs = []
    for unspent in unspents:
        script = b''  # empty scriptSig for new unsigned transaction.
        txid = hex_to_bytes(unspent.txid)[::-1]
        txindex = unspent.txindex.to_bytes(4, byteorder='little')
        amount = int(unspent.amount).to_bytes(8, byteorder='little')
        sw = unspent.segwit

        inputs.append(TxIn(script, txid, txindex, amount=amount, segwit=sw))

    tx_unsigned = TxObj(version, inputs, outputs, lock_time)

    tx = sign_tx(private_key, tx_unsigned)
    return tx
