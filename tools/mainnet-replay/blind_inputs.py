#!/usr/bin/env python3
"""Blind replay inputs: the checker never receives the values it is graded on.

For one captured chunk this module

1. reads the expected transition outputs from the canonical mainnet chunk (`chunk.borsh`), checks
   that its header hashes to the captured chunk hash and that the same header bytes appear in the
   captured block, and returns them as the expected values;
2. writes a copy of the exported `claim.bin` / `witness.bin` in which every value the transition
   produces is zeroed or emptied: in the endorsed chunk header (both copies) `prev_state_root`,
   `prev_outcome_root`, `encoded_merkle_root`, `encoded_length`, `prev_gas_used`,
   `prev_balance_burnt`, `prev_outgoing_receipts_root`, `prev_validator_proposals`,
   `congestion_info` and `bandwidth_requests`; in the witness the main and every implicit
   transition's `post_state_root`;
3. refuses the case if any real 32-byte output (or the real header) still occurs anywhere in the
   blinded files.

The checker then runs with `--blind` (no comparison against produced values) and the harness compares
its emitted outputs with the expected values from step 1.
"""
import base64
import hashlib
import json
import os
import struct
import sys
from pathlib import Path

ORACLE_TOOLS = Path(__file__).resolve().parents[2] / 'oracle' / 'tools'
sys.path.insert(0, str(ORACLE_TOOLS))
import spec_check_v3 as s3  # noqa: E402
from v3lib.prim import R, encoded_merkle_root  # noqa: E402
from v3lib import near2 as N  # noqa: E402

N.LENIENT = True    # walk every witness shape; this module only locates bytes, it decides nothing

B58 = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'


class BlindError(Exception):
    pass


def sha(b):
    return hashlib.sha256(b).digest()


def b58decode(s):
    n = 0
    for ch in s:
        n = n * 58 + B58.index(ch)
    raw = n.to_bytes((n.bit_length() + 7) // 8, 'big') if n else b''
    return b'\0' * (len(s) - len(s.lstrip('1'))) + raw


def u32(n):
    return struct.pack('<I', n)


def parse_inner(b, start):
    """Parse a tagged ShardChunkHeaderInner at `start`; return field values and byte spans."""
    r = R(b, start)
    tag = r.u8()
    if tag not in (3, 4):
        raise BlindError(f'chunk header inner tag {tag}')
    span = {}

    def field(name, read):
        i = r.i
        v = read()
        span[name] = (i, r.i)
        return v
    v = {'tag': tag}
    v['prev_block_hash'] = field('prev_block_hash', r.hash)
    v['prev_state_root'] = field('prev_state_root', r.hash)
    v['prev_outcome_root'] = field('prev_outcome_root', r.hash)
    v['encoded_merkle_root'] = field('encoded_merkle_root', r.hash)
    v['encoded_length'] = field('encoded_length', r.u64)
    v['height_created'] = field('height_created', r.u64)
    v['shard_id'] = field('shard_id', r.u64)
    v['prev_gas_used'] = field('prev_gas_used', r.u64)
    v['gas_limit'] = field('gas_limit', r.u64)
    v['prev_balance_burnt'] = field('prev_balance_burnt', r.u128)
    v['prev_outgoing_receipts_root'] = field('prev_outgoing_receipts_root', r.hash)
    v['tx_root'] = field('tx_root', r.hash)
    i = r.i
    props = []
    for _ in range(r.u32()):
        j = r.i
        s3.read_validator_stake(r)
        props.append(b[j:r.i])
    span['prev_validator_proposals'] = (i, r.i)
    v['prev_validator_proposals'] = props
    v['congestion_info'] = field('congestion_info', lambda: s3.read_congestion(r))
    v['bandwidth_requests'] = field('bandwidth_requests', lambda: s3.read_bw_requests(r))
    if tag == 4:
        field('proposed_split', lambda: r.option(lambda: (r.account(), r.u64(), r.u64())))
    v['raw'] = b[start:r.i]
    return v, span, r.i


def blind_inner(raw):
    """The header with every produced value zeroed; variable-length outputs become empty."""
    v, span, end = parse_inner(raw, 0)
    if end != len(raw):
        raise BlindError('trailing bytes after chunk header inner')
    out = bytearray(raw)
    for name in ('prev_state_root', 'prev_outcome_root', 'encoded_merkle_root', 'encoded_length',
                 'prev_gas_used', 'prev_balance_burnt', 'prev_outgoing_receipts_root'):
        a, z = span[name]
        out[a:z] = bytes(z - a)
    # Splice the variable-length tail: no proposals, zero congestion, no bandwidth requests.
    a = span['prev_validator_proposals'][0]
    z = span['bandwidth_requests'][1]
    tail = u32(0) + b'\0' + bytes(16 + 16 + 8 + 2) + b'\0' + u32(0)
    return bytes(out[:a]) + tail + bytes(out[z:])


def expected_from_chunk(capture_dir):
    """Expected outputs from the canonical chunk, anchored to the captured chunk hash and block."""
    cap = json.loads((capture_dir / 'capture.json').read_text())
    chunk = (capture_dir / 'chunk.borsh').read_bytes()
    r = R(chunk)
    if r.u8() != 1:
        raise BlindError('chunk.borsh is not ShardChunk::V2')
    stored_hash = r.hash()
    if r.u8() != 2:
        raise BlindError('chunk header is not ShardChunkHeader::V3')
    v, _, _ = parse_inner(chunk, r.i)
    computed = sha(sha(v['raw']) + v['encoded_merkle_root'])
    if computed != stored_hash or computed != b58decode(cap['chunk_hash']):
        raise BlindError('chunk header does not hash to the captured chunk hash')
    if (capture_dir / 'block.borsh').read_bytes().count(v['raw']) < 1:
        raise BlindError('chunk header is not in the captured block')
    return expected_values(v), v


def expected_values(v):
    """The graded outputs of a parsed chunk header inner, in the checker's emitted JSON form."""
    c = v['congestion_info']
    return {
        'stateRoot': v['prev_state_root'].hex(),
        'outcomeRoot': v['prev_outcome_root'].hex(),
        'gasUsed': str(v['prev_gas_used']),
        'balanceBurnt': str(v['prev_balance_burnt']),
        'outgoingReceiptsRoot': v['prev_outgoing_receipts_root'].hex(),
        'proposals': [p.hex() for p in v['prev_validator_proposals']],
        'txRoot': v['tx_root'].hex(),
        'encodedMerkleRoot': v['encoded_merkle_root'].hex(),
        'encodedLength': str(v['encoded_length']),
        'congestion': {'delayedReceiptsGas': str(c[0]), 'bufferedReceiptsGas': str(c[1]),
                       'receiptBytes': str(c[2]), 'allowedShard': str(c[3])},
        'bwRequests': [{'toShard': str(s), 'bitmap': m.hex()} for s, m in v['bandwidth_requests']],
    }


def expected_from_witness(case_dir):
    """Expected outputs from the chunk header that the validator-generated witness endorses.

    For generator corpora there is no separate canonical chunk: nearcore produced this header when
    it applied the chunk, so its `prev_*` fields are the transition outputs. The checker never sees
    them; they are removed from both the claim and the witness before it runs."""
    sw = state_witness(case_dir)
    r = R(sw)
    if r.u8() != 1:
        raise BlindError('ChunkStateWitness tag')
    r.hash()
    if r.u8() != 2:
        raise BlindError('witness chunk header is not V3')
    v, _, _ = parse_inner(sw, r.i)
    return expected_values(v), v


def state_witness(case_dir):
    r = R((case_dir / 'witness.bin').read_bytes())
    r.bytes()                      # format tag
    return r.bytes()


def post_root_spans(sw, reads=None):
    """Byte spans of the main and implicit transitions' `post_state_root` in a state witness.

    With `reads` (a list), also appends each transition's number of revealed trie nodes."""
    r = R(sw)
    if r.u8() != 1:
        raise BlindError('ChunkStateWitness tag')
    r.hash()
    if r.u8() != 2:
        raise BlindError('witness chunk header is not V3')
    s3.read_inner(r)
    r.u64()
    s3.read_signature(r)
    spans = []

    def transition():
        r.hash()
        nodes = s3.read_partial_state(r)
        if reads is not None:
            reads.append(len(nodes))
        spans.append((r.i, r.i + 32))
        r.hash()
    transition()
    for _ in range(r.u32()):
        r.hash()
        r.vec(lambda: N.read_receipt(r))
        r.u64()
        r.u64()
        r.vec(lambda: (r.hash(), r.u8()))
    r.hash()
    r.vec(lambda: N.read_tx(r))
    for _ in range(r.u32()):
        transition()
    r.vec(lambda: N.read_tx(r))
    r.end()
    return spans


def empty_chunk_constants(claim):
    """Header values of a chunk that emits nothing, which are protocol constants, not information.

    * the outgoing-receipts root with no receipts, per layout in the claim (`merklize` over every
      shard of `sha256(shard_id ‖ u32 0)`);
    * the encoded merkle root of the empty body `u32 0 ‖ u32 0` at the claim's Reed–Solomon
      parameters.

    Both legitimately occur in other shards' chunk headers in the segment."""
    r = R(claim)
    r.bytes(); r.bytes(); r.u32(); r.bytes(); r.hash(); r.bytes()
    for _ in range(r.u32()):
        r.u8(); r.hash(); r.bytes(); r.bytes(); r.vec(lambda: (r.bytes(), r.u64()))
    rs_data, rs_total = r.u16(), r.u16()
    roots = {encoded_merkle_root(u32(0) + u32(0), rs_data, rs_total)[0]}
    for _ in range(r.u32()):
        r.hash(); r.u32(); r.u64()
        L = s3.decode_layout(r.bytes())
        r.vec(lambda: (r.bytes(), r.u128()))
        leaves = [sha(sha(struct.pack('<Q', sid) + u32(0))) for sid in L.shard_ids]
        roots.add(s3.merkle_root_of_hashes(leaves))
    return roots


def replace_once(buf, old, new, what):
    if buf.count(old) != 1:
        raise BlindError(f'{what}: real chunk header occurs {buf.count(old)} times, expected once')
    return buf.replace(old, new)


def blind_case(case_dir, capture_dir, out_dir):
    """Write blinded claim/witness to `out_dir`; return (expected outputs, secondary facts).

    Expected values come from the canonical captured chunk, or, with `capture_dir=None`, from the
    nearcore-produced header in the case's own witness (`expected_from_witness`)."""
    if capture_dir is None:
        expected, real = expected_from_witness(case_dir)
    else:
        expected, real = expected_from_chunk(capture_dir)
    inner = real['raw']
    blinded = blind_inner(inner)
    claim = (case_dir / 'claim.bin').read_bytes()
    # claim-v3 encodes chunk_inner as borsh bytes: the u32 length immediately precedes it.
    claim = replace_once(claim, u32(len(inner)) + inner, u32(len(blinded)) + blinded, 'claim.bin')
    wit = (case_dir / 'witness.bin').read_bytes()
    r = R(wit)
    r.bytes()                      # format tag
    sw_start = r.i
    sw = r.bytes()
    rest = wit[r.i:]
    reads = []
    spans = post_root_spans(sw, reads)
    post_roots = [sw[a:z] for a, z in spans]
    swb = bytearray(sw)
    for a, z in spans:
        swb[a:z] = bytes(32)
    swb = replace_once(bytes(swb), inner, blinded, 'state witness')
    wit = wit[:sw_start] + u32(len(swb)) + swb + rest
    secrets = {inner: 'real chunk header'}
    constants = empty_chunk_constants(claim)
    for k in ('prev_state_root', 'prev_outcome_root', 'prev_outgoing_receipts_root',
              'encoded_merkle_root'):
        if real[k] == bytes(32):
            continue
        if k in ('prev_outgoing_receipts_root', 'encoded_merkle_root') and real[k] in constants:
            continue    # an empty-chunk constant; still blinded in the header and compared
        secrets[real[k]] = k
    for i, root in enumerate(post_roots):
        # A transition that reveals no trie node cannot change a non-empty trie: its post root
        # is its pre root, which the inputs carry legitimately (still blinded and compared). A
        # non-genesis shard trie is never empty: it holds at least the system account.
        if root != bytes(32) and reads[i] > 0:
            secrets[root] = f'post_state_root[{i}]'
    for name, data in (('claim.bin', claim), ('witness.bin', wit)):
        for secret, label in secrets.items():
            if secret in data:
                raise BlindError(f'{label} still present in blinded {name}')
    out_dir.mkdir(parents=True, exist_ok=False)
    (out_dir / 'claim.bin').write_bytes(claim)
    (out_dir / 'witness.bin').write_bytes(wit)
    return expected, {'witness_post_state_roots': [p.hex() for p in post_roots],
                      'implicit_transitions': len(post_roots) - 1,
                      'blinded_fields': ['prev_state_root', 'prev_outcome_root',
                                         'encoded_merkle_root', 'encoded_length', 'prev_gas_used',
                                         'prev_balance_burnt', 'prev_outgoing_receipts_root',
                                         'prev_validator_proposals', 'congestion_info',
                                         'bandwidth_requests', 'witness post_state_root x%d'
                                         % len(post_roots)]}


COMPARED = ('stateRoot', 'outcomeRoot', 'gasUsed', 'balanceBurnt', 'outgoingReceiptsRoot',
            'proposals', 'txRoot', 'encodedMerkleRoot', 'encodedLength', 'congestion', 'bwRequests')


def compare_outputs(expected, outputs):
    """Field names whose computed value differs from the chain's (missing output: every field)."""
    if not isinstance(outputs, dict):
        return list(COMPARED)
    return [k for k in COMPARED if outputs.get(k) != expected[k]]


if __name__ == '__main__':
    case, capture, out = map(Path, sys.argv[1:4])
    exp, facts = blind_case(case, capture, out)
    print(json.dumps({'expected': exp, **facts}, indent=2))
