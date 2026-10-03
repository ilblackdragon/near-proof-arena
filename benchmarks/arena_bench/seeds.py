"""Seed derivation and the per-season commit-reveal of the judge secret.

See docs/BENCHMARK_SPEC.md §8.4 and §11.
"""

from __future__ import annotations

import hashlib
import hmac
import re

SEED_DOMAIN = "near-arena-seed-v1"
SAMPLING_DOMAIN = "near-arena-workload-sample-v1"
COMMIT_DOMAIN = b"near-arena-secret-commit-v1\x00"

_PART_RE = re.compile(r"^[\x21-\x7b\x7d-\x7e]*$")  # printable ASCII, no '|', no space


def _check_part(p: str) -> str:
    if not isinstance(p, str) or not _PART_RE.match(p):
        raise ValueError(f"seed part must be printable ASCII without '|' or space: {p!r}")
    return p


def derive_seed(purpose: str, *parts: str) -> int:
    """Public, recomputable seed: first 8 bytes (big-endian) of
    sha256("near-arena-seed-v1|<purpose>|<part1>|...|<partN>")."""
    msg = "|".join([SEED_DOMAIN, _check_part(purpose), *(_check_part(p) for p in parts)])
    return int.from_bytes(hashlib.sha256(msg.encode("ascii")).digest()[:8], "big")


def commit_secret(secret: bytes) -> str:
    """Season commitment published before the season opens."""
    if len(secret) < 32:
        raise ValueError("judge secret must be at least 32 bytes")
    return "sha256:" + hashlib.sha256(COMMIT_DOMAIN + secret).hexdigest()


def verify_reveal(secret: bytes, commitment: str) -> bool:
    return hmac.compare_digest(commit_secret(secret), commitment)


def derive_sampling_seed(secret: bytes, challenge_id: str, package_digest: str, class_id: str) -> int:
    """Secret workload-sampling seed, computed only AFTER the package digest is frozen:
    first 8 bytes (big-endian) of HMAC-SHA256(key=secret,
    msg="near-arena-workload-sample-v1|<challenge_id>|<package_digest>|<class_id>")."""
    if len(secret) < 32:
        raise ValueError("judge secret must be at least 32 bytes")
    msg = "|".join(
        [SAMPLING_DOMAIN, _check_part(challenge_id), _check_part(package_digest), _check_part(class_id)]
    )
    mac = hmac.new(secret, msg.encode("ascii"), hashlib.sha256).digest()
    return int.from_bytes(mac[:8], "big")
