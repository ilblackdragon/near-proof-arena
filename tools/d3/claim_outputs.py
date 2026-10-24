#!/usr/bin/env python3
"""Independently decode a D3 case's `claim.bin` and extract the endorsed chunk header's outputs.

This exists so "Lean's outputs match" can be checked without trusting Lean's own decoder: this script
reads the claim bytes directly from the case directory and prints the same fields the Lean driver
`nearspec-v3-check-d3-out` prints. Comparing the two is a check on Lean's *emission*, independent of
Lean's decoding.

Claim layout (`spec/claim-v3.md`, `NearSpecV3/ClaimV3.lean:166-182`): borsh-ish, with the tag and
statement id first, then protocol_version u32, chain_id (u32 len + bytes), epoch_id 32 bytes, and
chunk_inner (u32 len + bytes). Everything after that is not needed for the outputs.

ChunkInner layout (`NearSpecV3/Wire.lean:171-190`, `pChunkInner`): tag u8, prev_block_hash 32,
prev_state_root 32, prev_outcome_root 32, encoded_merkle_root 32, encoded_length u64, height_created u64,
shard_id u64, prev_gas_used u64, gas_limit u64, prev_balance_burnt u128, prev_outgoing_receipts_root 32,
tx_root 32, then proposals as a u32-length vector of raw ValidatorStake encodings, then congestion.

Only the fields the driver emits are extracted; the tail is left undecoded so this script does not have
to mirror the full decoder. It refuses (exit 2) if the bytes run out, so a layout error is loud.
"""
import json
import struct
import sys


class R:
    def __init__(self, b):
        self.b = b
        self.i = 0

    def u8(self):
        v = self.b[self.i]
        self.i += 1
        return v

    def u32(self):
        v = struct.unpack_from("<I", self.b, self.i)[0]
        self.i += 4
        return v

    def u64(self):
        v = struct.unpack_from("<Q", self.b, self.i)[0]
        self.i += 8
        return v

    def u128(self):
        v = struct.unpack_from("<QQ", self.b, self.i)
        self.i += 16
        return v[0] | (v[1] << 64)

    def take(self, n):
        v = self.b[self.i:self.i + n]
        if len(v) != n:
            raise EOFError(f"wanted {n} bytes at {self.i}, have {len(self.b) - self.i}")
        self.i += n
        return v

    def vec(self):
        return self.take(self.u32())


def decode_claim(claim: bytes):
    r = R(claim)
    r.vec()         # claim format tag  ("near-arena-claim-v3", length-prefixed)
    r.vec()         # statement id tag  ("near/pv86/chunk-validation/v0", length-prefixed)
    protocol_version = r.u32()
    chain_id = r.vec()
    epoch_id = r.take(32)
    chunk_inner = r.vec()
    return {
        "protocol_version": protocol_version,
        "chain_id": chain_id,
        "epoch_id": epoch_id,
        "chunk_inner": chunk_inner,
        "rest_at": r.i,
    }


def decode_chunk_inner(ci: bytes):
    r = R(ci)
    out = {}
    out["tag"] = r.u8()
    out["prev_block_hash"] = r.take(32)
    out["prev_state_root"] = r.take(32)
    out["prev_outcome_root"] = r.take(32)
    out["encoded_merkle_root"] = r.take(32)
    out["encoded_length"] = r.u64()
    out["height_created"] = r.u64()
    out["shard_id"] = r.u64()
    out["prev_gas_used"] = r.u64()
    out["gas_limit"] = r.u64()
    out["prev_balance_burnt"] = r.u128()
    out["prev_outgoing_receipts_root"] = r.take(32)
    out["tx_root"] = r.take(32)
    n = r.u32()
    props = []
    for _ in range(n):
        # ValidatorStake V1: tag u8, account id (u32 len), public key (u8 tag + key), stake u128.
        st = r.u8()
        acct = r.vec()
        pk_tag = r.u8()
        pk_len = {0: 32, 1: 64}.get(pk_tag, 32)
        pk = r.take(pk_len)
        stake = r.u128()
        raw = bytes([st]) + struct.pack("<I", len(acct)) + acct + bytes([pk_tag]) + pk + \
            struct.pack("<QQ", stake & ((1 << 64) - 1), stake >> 64)
        props.append(raw)
    out["proposals"] = props
    out["congestion_at"] = r.i
    return out


def main():
    if len(sys.argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    path = sys.argv[1]
    claim = open(path, "rb").read()
    c = decode_claim(claim)
    ci = decode_chunk_inner(c["chunk_inner"])
    # The driver's "outputs" object, keyed identically so a diff is mechanical.
    outputs = {
        "stateRoot": ci["prev_state_root"].hex(),
        "outcomeRoot": ci["prev_outcome_root"].hex(),
        "gasBurnt": ci["prev_gas_used"],
        "balanceBurnt": ci["prev_balance_burnt"],
        "outgoingReceiptsRoot": ci["prev_outgoing_receipts_root"].hex(),
        "proposals": [p.hex() for p in ci["proposals"]],
        "txRoot": ci["tx_root"].hex(),
        "encodedMerkleRoot": ci["encoded_merkle_root"].hex(),
        "encodedLength": ci["encoded_length"],
    }
    print(json.dumps({"claim": path, "outputs": outputs}, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
