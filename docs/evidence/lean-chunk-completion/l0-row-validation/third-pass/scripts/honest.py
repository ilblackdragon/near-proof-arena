"""Honest cases of the gas-key runs whose chunk executed the injected contract (d3float slot):
list them with nearcore's outcome for the target call; write honest-<pass>.txt."""
import json, glob, sys
p = sys.argv[1] if len(sys.argv) > 1 else "p1"
out = []
for m in sorted(glob.glob(f"/data/illia/nearproof-deps/l0-validate/b4/gk/{p}-*/*/*/meta.json")):
    if "/mutants/" in m:
        continue
    d = json.load(open(m))
    if any(e.get("name") == "d3float" for e in d.get("executed_contracts", [])):
        ar = [a for a in d.get("action_results", []) if "FunctionCall" in a]
        out.append(m[:-len("/meta.json")])
        print(m.split("/gk/")[1][:-10], d.get("nearcore"), [a for a in ar if "InvalidMethodName" in a or "fail" in a][:2])
open(f"/data/illia/nearproof-deps/l0-validate/b4/gk/honest-{p}.txt", "w").write("\n".join(out) + "\n")
print(len(out))
