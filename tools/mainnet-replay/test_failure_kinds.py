"""Unit tests of the W01 failure-kind canonicalization and per-receipt attribution comparison."""
import importlib.util
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import failure_kinds as fk  # noqa: E402

spec = importlib.util.spec_from_file_location('full_observables', HERE / 'full_observables.py')
fo = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fo)


class Canonical(unittest.TestCase):
    def test_action_error_struct(self):
        e = 'ActionError(ActionError { index: Some(0), kind: AccountDoesNotExist { account_id: AccountId("s0a01") } })'
        self.assertEqual(fk.canonical_expected(e), 'ActionError[0].AccountDoesNotExist')

    def test_index_none(self):
        e = ('ActionError(ActionError { index: None, kind: LackBalanceForState { account_id: AccountId("x"), '
             'amount: NearToken { inner: 5 } } })')
        self.assertEqual(fk.canonical_expected(e), 'ActionError[None].LackBalanceForState')
        self.assertEqual(fk.canonical_lean('ActionError[None].LackBalanceForState'),
                         'ActionError[None].LackBalanceForState')

    def test_invalid_tx_nested(self):
        self.assertEqual(fk.canonical_expected('InvalidTxError(InvalidAccessKeyError(RequiresFullAccess))'),
                         'InvalidTxError.InvalidAccessKeyError.RequiresFullAccess')
        self.assertEqual(fk.canonical_expected('InvalidTxError(ActionsValidation(GasKeyInvalidNumNonces { requested_nonces: 0, limit: 1024 }))'),
                         'InvalidTxError.ActionsValidation.GasKeyInvalidNumNonces')

    def test_execution_error_display_resolved(self):
        e = ('ActionError(ActionError { index: Some(1), kind: FunctionCallError(ExecutionError('
             '"Smart contract panicked: a, \\"b\\" (c)")) })')
        self.assertEqual(fk.canonical_expected(e), 'ActionError[1].FunctionCallError.HostError.GuestPanic')
        e = ('ActionError(ActionError { index: Some(0), kind: FunctionCallError(ExecutionError('
             '"WebAssembly trap: An `unreachable` opcode was executed.")) })')
        self.assertEqual(fk.canonical_expected(e), 'ActionError[0].FunctionCallError.WasmTrap.Unreachable')
        e = 'ActionError(ActionError { index: Some(0), kind: FunctionCallError(ExecutionError("Exceeded the prepaid gas.")) })'
        self.assertEqual(fk.canonical_expected(e), 'ActionError[0].FunctionCallError.HostError.GasExceeded')

    def test_lean_vm_errors(self):
        self.assertEqual(fk.canonical_lean('ActionError[0].FunctionCallError(HostError(GuestPanic { panic_msg: "a, b" }))'),
                         'ActionError[0].FunctionCallError.HostError.GuestPanic')
        self.assertEqual(fk.canonical_lean('ActionError[2].FunctionCallError(CompilationError(CodeDoesNotExist))'),
                         'ActionError[2].FunctionCallError.CompilationError.CodeDoesNotExist')
        self.assertEqual(fk.canonical_lean('ActionError[0].FunctionCallError(LinkError { msg: "x" })'),
                         'ActionError[0].FunctionCallError.LinkError')

    def test_lean_display_host_errors(self):
        self.assertEqual(fk.canonical_lean('ActionError[0].FunctionCallError(HostError(AltBn128 invalid input: invalid point))'),
                         'ActionError[0].FunctionCallError.HostError.AltBn128InvalidInput')
        self.assertEqual(fk.canonical_lean('ActionError[1].FunctionCallError(HostError(BLS12-381 invalid input: Incorrect input length for x: 1 is not divisible by 2))'),
                         'ActionError[1].FunctionCallError.HostError.BLS12381InvalidInput')

    def test_kinds_differ(self):
        self.assertNotEqual(fk.canonical_expected('InvalidTxError(InvalidNonce { tx_nonce: 1, ak_nonce: 2 })'),
                            fk.canonical_expected('InvalidTxError(NonceTooLarge { tx_nonce: 1, upper_bound: 2 })'))


def b58(hexstr):
    n = int(hexstr, 16)
    s = ''
    while n:
        n, r = divmod(n, 58)
        s = fo._B58[r] + s
    return s


class Attribution(unittest.TestCase):
    R1, R2 = 'aa' * 32, 'bb' * 32

    def exp(self, changes):
        return {'state_changes': changes}

    def test_b58_roundtrip(self):
        self.assertEqual(fo.b58_to_hex(b58(self.R1)), self.R1)

    def test_effective_and_grouping(self):
        c1 = 'ReceiptProcessing { receipt_hash: %s }' % b58(self.R1)
        c2 = 'ReceiptProcessing { receipt_hash: %s }' % b58(self.R2)
        exp = self.exp([
            # written by R1 then R2: both effective
            {'key': '00', 'pre': {'absent': True}, 'changes': [
                {'cause': c1, 'valueHash': '01' * 32, 'valueLen': '3'},
                {'cause': c2, 'valueHash': '02' * 32, 'valueLen': '3'}]},
            # rewritten with its pre-state value by R1: not effective
            {'key': '01', 'pre': {'valueHash': '05' * 32, 'valueLen': '7'}, 'changes': [
                {'cause': c1, 'valueHash': '05' * 32, 'valueLen': '7'}]},
            # chunk-level cause only: never attributed
            {'key': '07', 'pre': {'absent': True}, 'changes': [
                {'cause': 'UpdatedDelayedReceipts', 'valueHash': '09' * 32, 'valueLen': '1'}]},
        ])
        groups = [([self.R1], {}, {}), ([self.R2], {}, {})]
        got, wrote, unattributed, errors = fo.expected_attribution(exp, groups)
        self.assertEqual(got, {0: {'00': ('01' * 32, '3')}, 1: {'00': ('02' * 32, '3')}})
        self.assertEqual(wrote[0]['01'], ('05' * 32, '7'))
        self.assertFalse(unattributed)
        self.assertEqual(errors, 0)
        lean = {'receiptStateChanges': [
            {'ids': [self.R1], 'changes': [{'key': '00', 'valueHash': '01' * 32, 'valueLen': '3'}]},
            {'ids': [self.R2], 'changes': [{'key': '00', 'valueHash': '02' * 32, 'valueLen': '3'}]}]}
        counts, bad = fo.Counter(), fo.Counter()
        fo.compare_attribution(lean, exp, counts, bad)
        self.assertEqual(sum(bad.values()), 0)
        # a change attributed to the wrong receipt is a mismatch
        lean['receiptStateChanges'][1]['changes'] = []
        lean['receiptStateChanges'][0]['changes'] = [{'key': '00', 'valueHash': '02' * 32, 'valueLen': '3'}]
        counts, bad = fo.Counter(), fo.Counter()
        fo.compare_attribution(lean, exp, counts, bad)
        self.assertGreater(bad['attrib.entry'], 0)

    def test_unknown_pre_and_queue_keys(self):
        c1 = 'ReceiptProcessing { receipt_hash: %s }' % b58(self.R1)
        c2 = 'ActionReceiptProcessingStarted { receipt_hash: %s }' % b58(self.R2)
        exp = self.exp([
            # rewritten with its unchanged pre-state value: nearcore sees no change
            {'key': '01', 'pre': {'valueHash': '05' * 32, 'valueLen': '7'}, 'changes': [
                {'cause': c1, 'valueHash': '05' * 32, 'valueLen': '7'}]},
            # outgoing buffer written after R1's commit, logged under R2's first commit
            {'key': '0d', 'pre': {'absent': True}, 'changes': [
                {'cause': c2, 'valueHash': '07' * 32, 'valueLen': '9'}]},
        ])
        lean = {'receiptStateChanges': [
            {'ids': [self.R1], 'preKnown': True, 'changes': [{'key': '0d', 'valueHash': '07' * 32, 'valueLen': '9'}]},
            {'ids': [self.R1], 'preKnown': False, 'changes': [{'key': '01', 'valueHash': '05' * 32, 'valueLen': '7'}]},
            {'ids': [self.R2], 'preKnown': True, 'changes': []}]}
        counts, bad = fo.Counter(), fo.Counter()
        fo.compare_attribution(lean, exp, counts, bad)
        self.assertEqual(sum(bad.values()), 0)
        self.assertEqual(counts['attrib.unknownPre'], 1)
        # an unknown-pre key nearcore never wrote in that entry is a mismatch
        lean['receiptStateChanges'][1]['changes'][0]['valueHash'] = '06' * 32
        counts, bad = fo.Counter(), fo.Counter()
        fo.compare_attribution(lean, exp, counts, bad)
        self.assertEqual(bad['attrib.key'], 1)

    def test_postponed_then_completed(self):
        D = 'cc' * 32
        post = 'PostponedReceipt { receipt_hash: %s }' % b58(self.R1)
        start = 'ActionReceiptProcessingStarted { receipt_hash: %s }' % b58(self.R1)
        exp = self.exp([{'key': '06', 'pre': {'absent': True}, 'changes': [
            {'cause': post, 'valueHash': '01' * 32, 'valueLen': '1'},
            {'cause': start, 'valueHash': None, 'valueLen': None}]}])
        lean = {'receiptStateChanges': [
            {'ids': [self.R1], 'changes': [{'key': '06', 'valueHash': '01' * 32, 'valueLen': '1'}]},
            {'ids': [D, self.R1], 'changes': [{'key': '06', 'valueHash': None, 'valueLen': None}]}]}
        counts, bad = fo.Counter(), fo.Counter()
        fo.compare_attribution(lean, exp, counts, bad)
        self.assertEqual(sum(bad.values()), 0)

    def test_unknown_id_reported(self):
        c = 'ReceiptProcessing { receipt_hash: %s }' % b58(self.R2)
        exp = self.exp([{'key': '00', 'pre': {'absent': True}, 'changes': [{'cause': c, 'valueHash': '01' * 32, 'valueLen': '1'}]}])
        lean = {'receiptStateChanges': [{'ids': [self.R1], 'changes': []}]}
        counts, bad = fo.Counter(), fo.Counter()
        fo.compare_attribution(lean, exp, counts, bad)
        self.assertEqual(bad['attrib.unattributed'], 1)


if __name__ == '__main__':
    unittest.main()
