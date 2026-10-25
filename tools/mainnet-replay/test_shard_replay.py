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
