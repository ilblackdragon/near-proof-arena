"""Run the pinned crate on zbound-vectors.json and record `crate_verdict` per case.
usage: python3 add_crate_verdict.py VECTORS.json [ORACLE]"""
import json, subprocess, sys
p = sys.argv[1]
oracle = sys.argv[2] if len(sys.argv) > 2 else "/tmp/claude-1002/sp/bin/oracle-mldsa"
out = json.loads(subprocess.run([oracle, "mldsa-vectors", "--verify", p], check=True,
                                capture_output=True, text=True).stdout)
d = json.load(open(p))
v = {o["name"]: o["verdict"] for o in out}
for c in d["cases"]:
    c["crate_verdict"] = v[c["name"]]
    print(c["name"], c["maxz"], "expect", c["expect"], "crate", c["crate_verdict"])
d["crate"] = "aws-lc-rs 1.16.2 via near_crypto::Signature::verify (nearcore 44f7ae6c); expect = FIPS 204"
json.dump(d, open(p, "w"), separators=(",", ":"))
print("agree", sum(c["expect"] == c["crate_verdict"] for c in d["cases"]), "/", len(d["cases"]))
