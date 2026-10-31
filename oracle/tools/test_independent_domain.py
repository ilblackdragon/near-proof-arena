"""Tests for oracle/tools/independent_domain.py, the independent licence for exclusions the corpus
oracle does not label (Gate-B freeze harness, 2026-10-31).

Every predicate is checked on a committed case where it holds and on one where it does not, so a
predicate that always (or never) fires fails here. The two size bounds, which no committed case
crosses, are checked on synthetic bytes. `assert_exclusion` is checked for the refusals that keep a
row failing: an unknown reason, a reason the tier under test decides, a false predicate and an
undecodable case.
"""
import os
from pathlib import Path
import struct
import sys
import unittest

REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "oracle/tools"))
import independent_domain as I  # noqa: E402

EV = REPO / "docs/evidence/lean-chunk-completion"
GENESIS = REPO / "oracle/fixtures/v3/public-d0a/ood/00-h10002-s1"
NOT_GENESIS = REPO / "oracle/fixtures/v3/public-d0a/d0/00-h10004-s3"
MLDSA = EV / "key-family-fixtures/cases/00-h10098-s0"
SECP_TX = EV / "key-family-fixtures/cases/00-h10007-s3"
GCD = EV / "global-cache-fixtures/cases/00-h10007-s3"
GCD_RESHARD = EV / "resharding-fixtures-2/cases/seed67-01-h10068-s4"
CACHE_SERVED = EV / "w08-warm-cache/cases/cc801-00-h10003-s0-code.drop.0"
HONEST_CODE = EV / "w08-warm-cache/cases/cc801-00-h10003-s0"
RACE = EV / "pipeline-race-fixtures/cases/race1201__mutants__00-h10023-s1-code.duplicate"


def holds(fn, case_dir):
    return fn(I.Case.load(str(case_dir)))[0]


def bstr(b):
    return struct.pack("<I", len(b)) + b


def witness_file(sw, codes=()):
    return bstr(I.FORMAT_WITNESS) + bstr(sw) + struct.pack("<I", len(codes)) + b"".join(map(bstr, codes))


class Predicates(unittest.TestCase):
    def test_b2_is_genesis(self):
        self.assertTrue(holds(I.b2_is_genesis, GENESIS))
        self.assertFalse(holds(I.b2_is_genesis, NOT_GENESIS))

    def test_transaction_key_not_ed25519(self):
        self.assertTrue(holds(I.transaction_key_not_ed25519, SECP_TX))
        self.assertFalse(holds(I.transaction_key_not_ed25519, HONEST_CODE))
        self.assertFalse(holds(I.transaction_key_not_ed25519, MLDSA))

    def test_mldsa65_public_key(self):
        self.assertTrue(holds(I.mldsa65_public_key_in_tx_or_receipt, MLDSA))
        self.assertFalse(holds(I.mldsa65_public_key_in_tx_or_receipt, SECP_TX))
        self.assertFalse(holds(I.mldsa65_public_key_in_tx_or_receipt, HONEST_CODE))

    def test_global_contract_distribution_receipt(self):
        self.assertTrue(holds(I.global_contract_distribution_receipt, GCD))
        self.assertTrue(holds(I.global_contract_distribution_receipt, GCD_RESHARD))
        self.assertFalse(holds(I.global_contract_distribution_receipt, HONEST_CODE))

    def test_prestate_code_absent_but_deployed_in_chunk(self):
        self.assertTrue(holds(I.prestate_code_absent_but_deployed_in_chunk, CACHE_SERVED))
        # the same chunk with its code blobs: the witness serves the code
        self.assertFalse(holds(I.prestate_code_absent_but_deployed_in_chunk, HONEST_CODE))

    def test_call_served_by_earlier_in_chunk_deploy(self):
        self.assertTrue(holds(I.call_served_by_earlier_in_chunk_deploy, RACE))
        self.assertFalse(holds(I.call_served_by_earlier_in_chunk_deploy, HONEST_CODE))

    def test_state_witness_size_bound(self):
        at = I.Case(b"", witness_file(b"\0" * I.MAX_STATE_WITNESS_IN_DOMAIN))
        above = I.Case(b"", witness_file(b"\0" * (I.MAX_STATE_WITNESS_IN_DOMAIN + 1)))
        self.assertFalse(I.state_witness_larger_than_8MiB(at)[0])
        self.assertTrue(I.state_witness_larger_than_8MiB(above)[0])

    def test_segment_bound(self):
        class Fake(I.Case):
            def __init__(self, n):
                super().__init__(b"", b"")
                self._claim = {"blocks": [object()] * n}
        self.assertFalse(I.segment_longer_than_32(Fake(32))[0])
        self.assertTrue(I.segment_longer_than_32(Fake(33))[0])
        self.assertTrue(holds(I.segment_longer_than_32, GENESIS) is False)

    def test_lenient_decoding_is_restored(self):
        # compare with the value before the call: other test modules may set N.LENIENT globally
        before = I.N.LENIENT
        holds(I.mldsa65_public_key_in_tx_or_receipt, MLDSA)
        self.assertEqual(I.N.LENIENT, before)


class AssertExclusion(unittest.TestCase):
    def test_licensed_when_the_named_predicate_holds(self):
        d = I.assert_exclusion(str(MLDSA), I.R_MLDSA_KEY, "signed")
        self.assertTrue(d["licensed"])
        self.assertEqual(d["predicate"], "mldsa65_public_key_in_tx_or_receipt")
        self.assertTrue(I.assert_exclusion(str(GENESIS), I.R_NOT_GENESIS, "signed")["licensed"])
        self.assertTrue(I.assert_exclusion(str(RACE), I.R_PREP_RACE, "successor")["licensed"])

    def test_wrong_reason_for_the_case_is_not_licensed(self):
        # an ML-DSA case excluded as "non-ED25519 transaction key", a non-genesis case as not_genesis
        self.assertFalse(I.assert_exclusion(str(MLDSA), I.R_NON_ED25519_TX, "signed")["licensed"])
        self.assertFalse(I.assert_exclusion(str(NOT_GENESIS), I.R_NOT_GENESIS, "signed")["licensed"])
        self.assertFalse(I.assert_exclusion(str(HONEST_CODE), I.R_PREP_RACE, "successor")["licensed"])

    def test_unknown_or_altered_reason_is_not_licensed(self):
        for reason in ("", "out of domain (w.shape)", I.R_MLDSA_KEY + " ", "out of domain (e.float)",
                       "out of domain (c.not_genesis): resharding walk reaches the genesis block"):
            d = I.assert_exclusion(str(MLDSA), reason, "signed")
            self.assertFalse(d["licensed"], reason)

    def test_shape_the_tier_decides_is_not_licensed(self):
        # allFeatures decides genesis segments and ML-DSA keys; the signed tier has no race reason
        self.assertFalse(I.assert_exclusion(str(GENESIS), I.R_NOT_GENESIS, "successor")["licensed"])
        self.assertFalse(I.assert_exclusion(str(MLDSA), I.R_MLDSA_KEY, "successor")["licensed"])
        self.assertFalse(I.assert_exclusion(str(RACE), I.R_PREP_RACE, "signed")["licensed"])
        self.assertFalse(I.assert_exclusion(str(MLDSA), I.R_MLDSA_KEY, "noSuchTier")["licensed"])

    def test_undecodable_case_is_not_licensed(self):
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            for n in ("claim.bin", "witness.bin"):
                with open(os.path.join(td, n), "wb") as f:
                    f.write(b"\x01garbage")
            for reason in (I.R_NOT_GENESIS, I.R_MLDSA_KEY, I.R_WSIZE_8MIB, I.R_GCD):
                d = I.assert_exclusion(td, reason, "signed")
                self.assertFalse(d["licensed"], reason)
            self.assertFalse(I.assert_exclusion(os.path.join(td, "missing"), I.R_GCD, "signed")["licensed"])


if __name__ == "__main__":
    unittest.main()
