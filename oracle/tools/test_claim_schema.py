"""Schema gate for the versioned claim/witness envelope (spec/claim-v3-versioning.md).

Runs on the committed fixtures only, so it needs no corpora: every committed claim/witness must
pass the structural v3 check under the legacy rule, its version-3 envelope must pass too and
round-trip to the same bytes, and malformed variants (unsupported version or encoding, a wrong
format tag, a trailing byte, truncation) must be rejected.
"""
import glob
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/d3"))
import claim_schema as cs  # noqa: E402

CASES = sorted({str(Path(p).parent) for p in glob.glob(
    str(ROOT / "docs/evidence/lean-chunk-completion/**/claim.bin"), recursive=True)
    if (Path(p).parent / "witness.bin").exists()})


class SchemaGate(unittest.TestCase):
    def test_population_nonempty(self):
        self.assertGreaterEqual(len(CASES), 500, "committed fixture population vanished")

    def test_self_test(self):
        self.assertEqual(cs.self_test(), 0)

    def test_committed_fixtures_legacy_and_envelope(self):
        for d in CASES:
            for name, want in (("claim.bin", "claim"), ("witness.bin", "witness")):
                data = (Path(d) / name).read_bytes()
                info = cs.check_file(data, want)
                self.assertEqual(info["schema_version"], 3)
                self.assertTrue(info["rule"].startswith("legacy"), d)
                env = cs.to_versioned(data)
                self.assertNotEqual(env, data)
                self.assertEqual(cs.check_file(env, want)["rule"], "explicit")
                self.assertEqual(cs.to_legacy(env), data)

    def test_malformed_rejected(self):
        d = Path(CASES[0])
        claim = (d / "claim.bin").read_bytes()
        wit = (d / "witness.bin").read_bytes()
        env_c, env_w = cs.to_versioned(claim), cs.to_versioned(wit)
        bad = [
            env_c[:20] + (4).to_bytes(4, "little") + env_c[24:],     # claim schema version 4
            env_w[:22] + (2).to_bytes(4, "little") + env_w[26:],     # witness schema version 2
            env_w[:26] + b"\x07" + env_w[27:],                       # witness encoding 7
            claim + b"\x00",                                         # trailing byte
            claim[:-1],                                              # truncated
            b"\x13\x00\x00\x00near-arena-claim-v9" + claim[23:],     # unknown tag
        ]
        for data in bad:
            with self.assertRaises(cs.SchemaError):
                cs.check_file(data)

    def test_environment_manifest(self):
        self.assertEqual(cs.check_env(str(ROOT / "spec/environment-v3.json")), [])
        doc = json.loads((ROOT / "spec/environment-v3.json").read_text())
        doc["architectures"]["aarch64"]["status"] = "maybe"
        tmp = ROOT / "spec/.env-negative.json"
        try:
            tmp.write_text(json.dumps(doc))
            self.assertTrue(cs.check_env(str(tmp)))
        finally:
            tmp.unlink()


if __name__ == "__main__":
    unittest.main()
