"""Negative controls for the artifact/parameter audit (stdlib unittest)."""
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from audit_g2 import audit, GATE, FORMAL


class AuditG2Tests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='g2-audit-')
        self.addCleanup(self.tmp.cleanup)
        self.gate = Path(self.tmp.name) / 'gate'
        shutil.copytree(GATE, self.gate)

    def test_recorded_inputs_pass_without_establishing_security(self):
        report = audit(self.gate)
        self.assertTrue(report['artifact_checks_pass'])
        self.assertFalse(report['security_established'])
        self.assertEqual(report['final_proof_bytes'], 293077)

    def test_altered_proof_is_rejected(self):
        path = self.gate / 'FINAL.proof'
        data = bytearray(path.read_bytes())
        data[0] ^= 1
        path.write_bytes(data)
        self.assertIn('proof digest: FINAL.proof', audit(self.gate)['failures'])

    def test_one_fewer_query_fails_exact_target(self):
        path = self.gate / 'run.log'
        path.write_text(path.read_text().replace('37140791, 41, true', '37140791, 40, true'))
        self.assertIn('final/0: exact query target', audit(self.gate)['failures'])

    def test_missing_subfold_certificate_is_rejected(self):
        formal = Path(self.tmp.name) / 'formal'
        for name in ['calc/dkt_certs_o2.json', 'lean/DKTCertsO2_big.keys']:
            (formal / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(FORMAL / name, formal / name)
        path = formal / 'calc/dkt_certs_o2.json'
        certs = json.loads(path.read_text())
        del certs['1006632960,524288,18570396,1']
        path.write_text(json.dumps(certs))
        failures = audit(self.gate, formal)['failures']
        self.assertTrue(any('non-excluded certificate 1006632960,524288,18570396,1' in f for f in failures))


if __name__ == '__main__':
    unittest.main()
