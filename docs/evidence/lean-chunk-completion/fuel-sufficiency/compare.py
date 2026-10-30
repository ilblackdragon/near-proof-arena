import json, collections, sys, os
S = "/tmp/claude-1002/-data-illia-nearproof/e268603b-12da-4c61-ab1c-70f2a15e868f/scratchpad"
def load(f):
    d = {}
    for l in open(os.path.join(S, f)):
        l = l.strip()
        if not l.startswith("{"):
            continue
        r = json.loads(l)
        d[r.get("case") or r.get("dir")] = r
    return d
def pop(c):
    p = c.split("/corpora/")
    return p[1].split("/")[0] if len(p) > 1 else "fixtures"
def key(r):
    return (r.get("verdict"), r.get("reason"))
b, a = load("rows-before.jsonl"), load("rows-after.jsonl")
tab = collections.defaultdict(lambda: collections.Counter())
diff = []
for c in sorted(set(a) | set(b)):
    rb, ra = b.get(c), a.get(c)
    p = pop(c)
    tab[p]["cases"] += 1
    if rb is None or ra is None:
        tab[p]["missing"] += 1; diff.append(c); continue
    tab[p]["before_" + str(rb.get("verdict"))] += 1
    tab[p]["after_" + str(ra.get("verdict"))] += 1
    if key(rb) != key(ra):
        tab[p]["moved"] += 1; diff.append(c)
for p in sorted(tab):
    print(p, dict(tab[p]))
print("moved/missing", len(diff), diff[:5])
if os.path.exists(os.path.join(S, "rows-broken.jsonl")):
    k = load("rows-broken.jsonl")
    cnt = collections.Counter()
    for c, r in k.items():
        ra = a.get(c)
        fc = "fuel_certificate" in str(r.get("reason"))
        cnt[(str(ra.get("verdict")) if ra else "?", str(r.get("verdict")), fc)] += 1
    print("broken control (after-verdict, broken-verdict, reason=fuel_certificate):")
    for x, n in sorted(cnt.items()):
        print(" ", x, n)
