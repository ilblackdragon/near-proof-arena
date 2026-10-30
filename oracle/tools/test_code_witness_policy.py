"""Integrity tests for the separate complete-witness policy comparison."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools/d3'))
import check_code_witness_policy as policy


class PolicyTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.code = b'independently supplied contract bytes'
        self.pair = dict(name='drop-code', complete='complete', incomplete='incomplete')
        for kind, codes in [('complete', [self.code]), ('incomplete', [])]:
            p = self.root / kind
            p.mkdir()
            (p / 'claim.bin').write_bytes(b'same claim')
            (p / 'witness.bin').write_bytes(policy.encode_envelope(b'same trie witness', codes))
            (p / 'meta.json').write_text(json.dumps(dict(expected_rel=True,
                nearcore='cold accept', verdict_source='nearcore(cold)', codes=[dict(
                    hash=policy.base58(hashlib.sha256(c).digest()), len=len(c)) for c in codes])))
        self.manifest = self.root / 'pairs.json'
        self.manifest.write_text(json.dumps(dict(pairs=[self.pair])))
        self.binary = self.root / 'binary'
        self.binary.write_bytes(b'fake checker for mocked execution')

    def test_envelope_strict(self):
        encoded = policy.encode_envelope(b'state', [b'code'])
        self.assertEqual(policy.decode_envelope(encoded), (b'state', [b'code']))
        for bad in [encoded[:-1], encoded + b'x', b'']:
            with self.assertRaises(ValueError):
                policy.decode_envelope(bad)

    def test_restoration_preserves_raw_accept(self):
        p = policy.prepare_pair(self.pair, self.root, self.root / 'out')
        self.assertTrue(p['raw_nearcore']['incomplete_expected_rel'])
        self.assertEqual(Path(p['cases']['normalized'], 'witness.bin').read_bytes(),
                         (self.root / 'complete/witness.bin').read_bytes())
        self.assertEqual(Path(p['cases']['incomplete'], 'meta.json').read_bytes(),
                         (self.root / 'incomplete/meta.json').read_bytes())

    def test_claim_change_forbidden(self):
        (self.root / 'incomplete/claim.bin').write_bytes(b'different')
        with self.assertRaisesRegex(ValueError, 'claim'):
            policy.prepare_pair(self.pair, self.root, self.root / 'out')

    def test_registry_hash_verified(self):
        with self.assertRaisesRegex(ValueError, 'hash/length'):
            policy.registry([b'changed'], dict(codes=[dict(hash='wrong', len=7)]))

    @staticmethod
    def rows(command, cases, timeout, tier):
        # the raw cold verdict of the incomplete fixture is an accept (deploy-served code)
        return {str(c): dict(case=str(c), tier=tier, verdict='accept', reason='') for c in cases}

    @staticmethod
    def incomplete_as(verdict, reason):
        def run(command, cases, timeout, tier):
            rows = PolicyTests.rows(command, cases, timeout, tier)
            for row in rows.values():
                if Path(row['case']).name == 'incomplete':
                    row.update(verdict=verdict, reason=reason)
            return rows
        return run

    def raw_reject(self):
        meta = json.loads((self.root / 'incomplete/meta.json').read_text())
        meta.update(expected_rel=False, nearcore='cold MissingTrieValue')
        (self.root / 'incomplete/meta.json').write_text(json.dumps(meta))

    def test_repeated_policy_verdict_matches_raw_cold(self):
        with patch.object(policy, 'run_batch', side_effect=self.rows) as run:
            report = policy.check(self.binary, self.manifest, self.root / 'out')
        self.assertEqual(run.call_count, 2)
        self.assertEqual(report['status'], 'pass')
        self.assertEqual(report['raw_mutant_accepts'], 1)
        self.assertFalse(report['raw_nearcore_mutant_expectations_relabelled'])

    def test_reject_of_raw_cold_accept_fails(self):
        # the pre-2026-10-29 blanket policy: a deterministic deploy-served witness was rejected
        run = self.incomplete_as('reject', policy.POLICY_PREFIX + ' missing code')
        with patch.object(policy, 'run_batch', side_effect=run):
            with self.assertRaisesRegex(ValueError, 'nearcore accepts'):
                policy.check(self.binary, self.manifest, self.root / 'out')

    def test_accept_of_raw_cold_reject_fails(self):
        self.raw_reject()
        with patch.object(policy, 'run_batch', side_effect=self.rows):
            with self.assertRaisesRegex(ValueError, 'nearcore rejects'):
                policy.check(self.binary, self.manifest, self.root / 'out')

    def test_reject_of_raw_cold_reject_passes(self):
        self.raw_reject()
        run = self.incomplete_as('reject', 'invalid: MissingTrieValue (contract code)')
        with patch.object(policy, 'run_batch', side_effect=run):
            self.assertEqual(policy.check(self.binary, self.manifest, self.root / 'out')['status'], 'pass')

    def test_race_exclusion_admitted_other_exclusions_not(self):
        run = self.incomplete_as('out_of_domain', policy.RACE_PREFIX + ' contract preparation pipelined')
        with patch.object(policy, 'run_batch', side_effect=run):
            self.assertEqual(policy.check(self.binary, self.manifest, self.root / 'out')['status'], 'pass')
        run = self.incomplete_as('out_of_domain', 'out of domain (e.wasm-α): something else')
        with patch.object(policy, 'run_batch', side_effect=run):
            with self.assertRaisesRegex(ValueError, 'nearcore accepts'):
                policy.check(self.binary, self.manifest, self.root / 'out2')

    def test_failed_preflight_invalidates_old_pass(self):
        out = self.root / 'out'
        out.mkdir()
        (out / 'report.json').write_text('{"status":"pass"}')
        with self.assertRaises(ValueError):
            policy.check(self.binary, self.manifest, out, repeats=1)
        self.assertEqual(json.loads((out / 'report.json').read_text())['status'], 'fail')

    def test_nonrepeatable_reason_fails(self):
        count = 0
        def unstable(*args):
            nonlocal count
            count += 1
            rows = self.rows(*args)
            for row in rows.values():
                row['reason'] += str(count)
            return rows
        with patch.object(policy, 'run_batch', side_effect=unstable):
            with self.assertRaisesRegex(ValueError, 'non-repeatable'):
                policy.check(self.binary, self.manifest, self.root / 'out')


if __name__ == '__main__':
    unittest.main()
