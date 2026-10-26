import copy
import hashlib
import importlib.util
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
spec = importlib.util.spec_from_file_location('full_observables', HERE / 'full_observables.py')
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def outcome(i, **kw):
    o = {'id': bytes([i]) * 32, 'executor': b'alice'.hex(), 'status': {'kind': 'value', 'value': ''},
         'gasBurnt': '2428', 'tokensBurnt': '242800', 'logs': [], 'receiptIds': [], 'computeUsage': '2428'}
    o['id'] = o['id'].hex()
    o.update(kw)
    return o


def pair():
    outs = [outcome(1, receiptIds=[(b'\x09' * 32).hex()]),
            outcome(2, logs=[b'hello'.hex()], status={'kind': 'value', 'value': 'abcd'}),
            outcome(3, status={'kind': 'failure'})]
    rcpts = [{'id': '11' * 32, 'predecessor': mod.SYSTEM, 'receiver': b'bob'.hex(), 'kind': 'Action',
              'hash': 'aa' * 32}]
    changes = [{'key': '00616c696365', 'valueHash': 'bb' * 32, 'valueLen': '100'},
               {'key': '0162', 'valueHash': None, 'valueLen': None}]
    leaves = [mod.outcome_leaf(o) for o in outs]
    root = mod.merkle_root(leaves).hex()
    exp = {'outcomes': outs, 'outgoing_receipts': rcpts, 'state_changes': changes,
           'compute_usage': '5', 'outcome_root': root, 'gas_used': '7284', 'balance_burnt': '1',
           'header_prev_outcome_root': root, 'store_outcome_ids': [o['id'] for o in outs]}
    lean = {'outcomes': [dict(o, leaf=l.hex()) for o, l in zip(outs, leaves)],
            'outgoingReceipts': [dict(r, kind='action', refund=True) for r in rcpts],
            'stateChanges': changes, 'computeUsage': '7284', 'outcomeRoot': root, 'gasUsed': '7284',
            'balanceBurnt': '1'}
    return lean, exp


class FullObservablesTest(unittest.TestCase):
    def test_merkle_matches_lean_definition(self):
        h = [hashlib.sha256(bytes([i])).digest() for i in range(5)]
        s = lambda a, b: hashlib.sha256(a + b).digest()
        self.assertEqual(mod.merkle_root([]), bytes(32))
        self.assertEqual(mod.merkle_root(h[:1]), h[0])
        # odd last node promoted unchanged (NearSpec.merkleLevel)
        self.assertEqual(mod.merkle_root(h[:3]), s(s(h[0], h[1]), h[2]))
        self.assertEqual(mod.merkle_root(h), s(s(s(h[0], h[1]), s(h[2], h[3])), h[4]))

    def test_leaf_without_logs_is_d0_leaf(self):
        o = outcome(1)
        partial = (mod.u32(0) + (2428).to_bytes(8, 'little') + (242800).to_bytes(16, 'little') +
                   mod.u32(5) + b'alice' + b'\x02' + mod.u32(0))
        want = hashlib.sha256(mod.u32(2) + bytes.fromhex(o['id']) + hashlib.sha256(partial).digest()).digest()
        self.assertEqual(mod.outcome_leaf(o), want)

    def test_identical_sides_match(self):
        lean, exp = pair()
        counts, bad = mod.compare(lean, exp)
        self.assertFalse(any(bad.values()))
        self.assertEqual(counts['outcome.gasBurnt'], 3)
        self.assertTrue(all(mod.recompute_checks(lean, exp).values()))

    def test_every_control_is_detected(self):
        lean, exp = pair()
        res = mod.run_controls(lean, exp)
        self.assertGreaterEqual(len(res), 15)
        self.assertEqual([r['control'] for r in res if not r['detected']], [])

    def test_log_change_breaks_recomputed_root(self):
        lean, exp = pair()
        lean2 = copy.deepcopy(lean)
        lean2['outcomes'][1]['logs'] = []
        self.assertFalse(mod.recompute_checks(lean2, exp)['lean_list_hashes_to_header'])

    def test_distribution_compute_has_no_outcome(self):
        # a fresh GlobalContractDistribution adds compute without an outcome (encoding difference)
        lean, exp = pair()
        exp['state_changes'].append({'key': '1200aa', 'valueHash': 'cc' * 32, 'valueLen': '345',
                                     'causes': ['ReceiptProcessing { receipt_hash: X }']})
        lean['stateChanges'] = exp['state_changes']
        self.assertEqual(mod.expected_compute(exp), str(7284 + 20_086_250_000_000))
        lean['computeUsage'] = str(7284 + 20_086_250_000_000)
        self.assertEqual(mod.compare(lean, exp)[1]['computeUsage'], 0)
        lean['computeUsage'] = '7284'
        self.assertEqual(mod.compare(lean, exp)[1]['computeUsage'], 1)

    def test_receipt_kind_mapping(self):
        self.assertEqual(mod.norm_receipt({'id': '', 'predecessor': '', 'receiver': '', 'kind': 'ActionV2',
                                           'hash': ''})['kind'], 'action')


if __name__ == '__main__':
    unittest.main()
