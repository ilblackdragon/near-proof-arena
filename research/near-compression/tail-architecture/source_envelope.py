#!/usr/bin/env python3
"""Research source-path envelope; inner cryptographic proof verification is separate."""
import struct
from audit_source_membership import root_from_digest


def encode(packet, index, path):
    return (b'NPSRC001' + struct.pack('<I', len(packet)) + packet +
            struct.pack('<II', index, len(path)) +
            b''.join(bytes([x['direction']]) + bytes(x['sibling']) for x in path))


def check_membership(envelope, expected_public, expected_sources, expected_own):
    """Return unchanged inner packet after host membership checks.

    expected_sources MUST be derived from the verifier's expected claim, never
    trusted from the envelope. Caller MUST verify returned packet cryptographically
    with the same expected_public and fixed local profile before accepting.
    """
    if len(envelope) > 300000 or len(envelope) < 20 or envelope[:8] != b'NPSRC001':
        raise ValueError('envelope framing')
    size = struct.unpack_from('<I', envelope, 8)[0]
    end = 12 + size
    if size < 24 or end + 8 > len(envelope):
        raise ValueError('packet framing')
    packet = envelope[12:end]
    index, depth = struct.unpack_from('<II', envelope, end)
    if index >= len(expected_sources) or end + 8 + 33*depth != len(envelope):
        raise ValueError('path framing')
    if packet[:8] != b'NPLIST03':
        raise ValueError('inner version')
    public_len = struct.unpack_from('<Q', packet, 16)[0]
    if public_len < 72 or 24 + public_len > len(packet):
        raise ValueError('public framing')
    public = packet[24:24+public_len]
    if public != expected_public or struct.unpack_from('<Q', public, 24)[0] != expected_own:
        raise ValueError('expected public or shard')
    leaf = b''.join(public[i:i+8][::-1] for i in range(40, 72, 8))
    path = [{'direction': envelope[end+8+33*i],
             'sibling': list(envelope[end+9+33*i:end+41+33*i])} for i in range(depth)]
    if root_from_digest(leaf, path) != bytes(expected_sources[index]['root']):
        raise ValueError('source membership')
    return packet
