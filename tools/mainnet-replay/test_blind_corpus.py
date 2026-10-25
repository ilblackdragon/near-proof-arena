#!/usr/bin/env python3
import importlib.util
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
spec = importlib.util.spec_from_file_location('blind_corpus', HERE / 'blind_corpus.py')
bc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bc)


def expected(**over):
    e = {'proposals': [], 'bwRequests': [], 'gasUsed': '0', 'balanceBurnt': '0',
         'congestion': {'delayedReceiptsGas': '0', 'bufferedReceiptsGas': '0',
                        'receiptBytes': '0', 'allowedShard': '0'}}
    e.update(over)
    return e


class BlindCorpusTests(unittest.TestCase):
    def test_nearcore_verdict(self):
        self.assertTrue(bc.nearcore_valid({'nearcore': 'ok', 'expected_rel': False}))
        self.assertFalse(bc.nearcore_valid({'nearcore': 'validate: StorageError(..)'}))
        self.assertTrue(bc.nearcore_valid({'expected_rel': True}))
        self.assertIsNone(bc.nearcore_valid({}))

    def test_features_only_nontrivial_values(self):
        self.assertEqual(bc.features(expected(), {'implicit_transitions': 0}), [])
        cong = {'delayedReceiptsGas': '5', 'bufferedReceiptsGas': '0', 'receiptBytes': '7',
                'allowedShard': '3'}
        got = bc.features(expected(proposals=['00'], bwRequests=[{}], congestion=cong),
                          {'implicit_transitions': 2})
        self.assertEqual(got, ['proposals', 'bandwidth_requests', 'congestion_delayed_gas',
                               'congestion_receipt_bytes', 'implicit_transitions'])

    def test_classify(self):
        self.assertEqual(bc.classify('accept', [], 'reject'), 'match')
        self.assertEqual(bc.classify('accept', ['stateRoot'], 'reject'), 'output_mismatch')
        self.assertEqual(bc.classify('accept', [], 'accept'), 'blind_leak')
        self.assertEqual(bc.classify('reject', [], 'reject'), 'mismatch')
        self.assertEqual(bc.classify('out_of_domain', [], 'reject'), 'unsupported')


if __name__ == '__main__':
    unittest.main()
