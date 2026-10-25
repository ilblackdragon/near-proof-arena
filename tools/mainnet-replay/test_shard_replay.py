"""Offline diagnostic-report controls; synthetic inputs are not mainnet evidence."""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).with_name('shard_replay.py')
spec = importlib.util.spec_from_file_location('shard_replay', SCRIPT)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


class DiagnosticTests(unittest.TestCase):
    def test_classification(self):
        for native, lean, expected in [('accept','accept','match'), ('accept','reject','mismatch'),
                                      ('accept','out_of_domain','unsupported'), ('reject','accept','native_reject'),
                                      ('accept','io_error','error')]:
            with self.subTest(native=native, lean=lean):
                self.assertEqual(mod.classify(native, lean), expected)

    def test_blind_classification(self):
        for native, lean, diffs, control, expected in [
                ('accept', 'accept', [], 'reject', 'match'),
                ('accept', 'accept', ['stateRoot'], 'reject', 'output_mismatch'),
                ('accept', 'accept', [], 'accept', 'blind_leak'),
                ('accept', 'reject', [], 'reject', 'mismatch'),
                ('accept', 'out_of_domain', [], 'reject', 'unsupported'),
                ('reject', 'accept', [], 'reject', 'native_reject')]:
            with self.subTest(lean=lean, diffs=diffs, control=control):
                self.assertEqual(mod.classify_blind(native, lean, diffs, control), expected)

    def test_blind_compare_outputs(self):
        exp = {k: 'x' for k in mod.blind_inputs.COMPARED}
        self.assertEqual(mod.blind_inputs.compare_outputs(exp, dict(exp)), [])
        self.assertEqual(mod.blind_inputs.compare_outputs(exp, {**exp, 'gasUsed': 'y'}), ['gasUsed'])
        self.assertEqual(mod.blind_inputs.compare_outputs(exp, None), list(mod.blind_inputs.COMPARED))

    def test_blind_inner_zeroes_outputs(self):
        # A synthetic V5 inner: every produced value nonzero, one proposal-free header.
        b = mod.blind_inputs
        inner = (bytes([4]) + b'\x01' * 32 + b'\x02' * 32 + b'\x03' * 32 + b'\x04' * 32 +
                 b.struct.pack('<QQQQQ', 9, 7, 13, 5, 1000) + (77).to_bytes(16, 'little') +
                 b'\x06' * 32 + b'\x07' * 32 + b.u32(0) + b'\0' + (1).to_bytes(16, 'little') +
                 bytes(16) + b.struct.pack('<QH', 3, 2) + b'\0' + b.u32(1) + b.struct.pack('<H', 2) +
                 b'\x1f' * 5 + b'\0')
        v, _, end = b.parse_inner(b.blind_inner(inner), 0)
        self.assertEqual(end, len(b.blind_inner(inner)))
        for k in ('prev_state_root', 'prev_outcome_root', 'encoded_merkle_root',
                  'prev_outgoing_receipts_root'):
            self.assertEqual(v[k], bytes(32), k)
        self.assertEqual((v['prev_gas_used'], v['prev_balance_burnt'], v['encoded_length']), (0, 0, 0))
        self.assertEqual(v['congestion_info'], (0, 0, 0, 0))
        self.assertEqual(v['bandwidth_requests'], [])
        # Inputs the checker needs are kept.
        self.assertEqual((v['prev_block_hash'], v['shard_id'], v['gas_limit'], v['tx_root']),
                         (b'\x01' * 32, 13, 1000, b'\x07' * 32))

    def run_fixture(self, verdicts, missing=False, bad_output=False):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);captures=root/'captures';cases=root/'cases';cases.mkdir()
            rows=[]
            for i,verdict in enumerate(verdicts):
                source=captures/str(i);source.mkdir(parents=True)
                (source/'capture.json').write_text(json.dumps({'shard_id':13,'block_height':100+i}))
                for name in ['state_witness.borsh','block.borsh','chunk.borsh']:(source/name).write_bytes(b'test-only')
                if missing and i==0:continue
                case=cases/str(i);case.mkdir()
                (case/'claim.bin').write_text(verdict);(case/'witness.bin').write_bytes(b'test-only')
                row={'source':str(source),'case':str(case),'native_verdict':'accept'}
                (case/'export.json').write_text(json.dumps(row));rows.append(row)
            (cases/'exports.json').write_text(json.dumps(rows))
            binary=root/'fake-checker'
            binary.write_text('#!/usr/bin/env python3\nimport json,sys\nfrom pathlib import Path\np=Path(sys.argv[3])\n'+
                              ('print("invalid output")\n' if bad_output else
                               'print(json.dumps({"case":str(p),"tier":sys.argv[2],"verdict":(p/"claim.bin").read_text(),"reason":"test"}))\n'))
            binary.chmod(0o755)
            out=root/'out'
            r=subprocess.run(['python3',str(SCRIPT),'--captures',str(captures),'--cases',str(cases),
                              '--binary',str(binary),'--native-binary',str(binary),'--out',str(out)],capture_output=True,text=True)
            self.assertTrue((out/'report.json').exists(),r.stderr)
            return r.returncode,json.loads((out/'report.json').read_text())

    def test_mismatch_and_unsupported_denominators(self):
        code,r=self.run_fixture(['accept','reject','out_of_domain'])
        self.assertEqual(code,1);self.assertEqual(r['mismatch_percent'],50)
        self.assertAlmostEqual(r['replay_coverage_percent'],200/3)
        self.assertEqual(r['counts'],{'match':1,'mismatch':1,'unsupported':1})
        self.assertFalse(r['w13_gate_pass'])

    def test_single_shard_success_never_passes_full_gate(self):
        code,r=self.run_fixture(['accept'])
        self.assertEqual(code,0);self.assertTrue(r['diagnostic_pass']);self.assertFalse(r['w13_gate_pass'])

    def test_missing_export_cannot_disappear(self):
        code,r=self.run_fixture(['accept'],missing=True)
        self.assertEqual(code,1);self.assertEqual(r['counts'],{'missing_case':1})
        self.assertIsNone(r['mismatch_percent']);self.assertEqual(r['replay_coverage_percent'],0)

    def test_malformed_output_fails(self):
        code,r=self.run_fixture(['accept'],bad_output=True)
        self.assertEqual(code,1);self.assertEqual(r['counts'],{'error':1})
        self.assertIsNone(r['mismatch_percent'])


if __name__ == '__main__':
    unittest.main()
