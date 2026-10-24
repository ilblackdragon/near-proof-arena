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
        return {str(c): dict(case=str(c), tier=tier,
            verdict='reject' if c.name == 'incomplete' else 'accept',
            reason=policy.POLICY_PREFIX + ' missing code' if c.name == 'incomplete' else '')
            for c in cases}

    def test_repeated_policy_verdict_not_raw_expectation(self):
        with patch.object(policy, 'run_batch', side_effect=self.rows) as run:
            report = policy.check(self.binary, self.manifest, self.root / 'out')
        self.assertEqual(run.call_count, 2)
        self.assertEqual(report['status'], 'pass')
        self.assertEqual(report['raw_mutant_accepts'], 1)
        self.assertFalse(report['raw_nearcore_mutant_expectations_relabelled'])

    def test_generic_rejection_is_not_policy_success(self):
        def generic(*args):
            rows = self.rows(*args)
            for row in rows.values():
                if row['verdict'] == 'reject':
                    row['reason'] = 'invalid claim'
            return rows
        with patch.object(policy, 'run_batch', side_effect=generic):
            with self.assertRaisesRegex(ValueError, 'incomplete-witness'):
                policy.check(self.binary, self.manifest, self.root / 'out')

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
