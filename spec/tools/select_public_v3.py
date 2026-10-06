#!/usr/bin/env python3
"""Coverage-select a public fixture subset of a D1 / D2 / D3 oracle corpus (difftest layout:
CORPUS/d<k>/, CORPUS/ood/, CORPUS/mutants/) into SEL/ (same layout, symlinks), for
`near-arena-oracle-v3-d{1,3} arena-layout --domain d<k> --in SEL --out FIXTURES --accepted-mutants`.

  select_public_v3.py d1|d2|d3 CORPUS SEL [--per-class N] [--per-family M] [--seed S]

Selection (deterministic for a seed):
* positives: per workload class (`arena::class_of`, mirrored by `class_of` below) up to N honest
  in-domain cases, first one per distinct coverage signature (features that matter for the
  domain), then by a seeded shuffle;
* accepted mutants (nearcore accepts, in domain: the witness's degrees of freedom): up to M per
  mutation family;
* rejections: up to M per rejected mutation family and up to M per out-of-domain violation family.
"""
import json, os, random, sys

G_ALPHA = (1 << 22) * 822756


def num(v):
    try:
        return int(v)
    except (TypeError, ValueError):
        return 0


def class_of(dom, m):
    f = m.get("features", {})
    if dom == "d1":
        tr = m.get("tx_results", [])
        if not tr:
            return "d1-receipts"
        return "d1-transfers" if all(r.startswith("success") for r in tr) else "d1-mixed"
    if dom == "d2":
        if num(f.get("n_epochs")) > 1 or num(f.get("validator_updates")) > 0:
            return "d2-epoch"
        if any(num(f.get(k)) > 0 for k in ("delayed_queue_pre", "delayed_queue_post", "buffered_pre", "buffered_post")):
            return "d2-queues"
        return "d2-actions"
    if dom == "d3":
        if num(f.get("fc_gas_burnt_for_function_call")) * 2 >= G_ALPHA:
            return "d3-maxgas"
        if num(f.get("n_callbacks")) > 0:
            return "d3-callbacks"
        if num(f.get("n_function_calls")) > 0:
            return "d3-calls"
        return "d3-nonwasm"
    raise SystemExit("domain d1|d2|d3")


def signature(dom, m):
    f = m.get("features", {})
    base = (len(f.get("rs", [])) and tuple(f["rs"]), num(f.get("n_shards")), num(f.get("n_implicit")) > 0)
    if dom == "d1":
        return base + (tuple(sorted(set(m.get("tx_labels", [])))), bool(m.get("new_tx_labels")))
    if dom == "d2":
        return base + (tuple(sorted({a.split(" =>")[0].split(":")[-1] for a in m.get("action_results", [])}))[:6],
                       num(f.get("n_epochs")) > 1, num(f.get("validator_updates")) > 0)
    return base + (tuple(sorted(f.get("contracts_ran", []))), tuple(sorted(f.get("fc_failure_kinds", {}))),
                   num(f.get("code_blobs")), num(f.get("deployed_in_chunk")) > 0, num(f.get("n_callbacks")) > 0)


def family(m):
    mu = m.get("mutation", "")
    parts = mu.split(".")
    return ".".join(parts[:2]) if len(parts) > 1 else mu


def main():
    dom, corpus, sel = sys.argv[1:4]
    args = sys.argv[4:]
    opt = lambda n, d: int(args[args.index(n) + 1]) if n in args else d
    per_class, per_family, seed = opt("--per-class", 36), opt("--per-family", 2), opt("--seed", 1)
    rng = random.Random(seed)
    key = "expected_rel_" + dom
    pick = {"pos": [], "acc": [], "rej": []}
    # positives
    by_class = {}
    for c in sorted(os.listdir(os.path.join(corpus, dom))):
        m = json.load(open(os.path.join(corpus, dom, c, "meta.json")))
        if m.get(key):
            by_class.setdefault(class_of(dom, m), []).append((c, m))
        else:
            pick["rej"].append((dom, c))
    for cls, items in sorted(by_class.items()):
        rng.shuffle(items)
        seen, first, rest = set(), [], []
        for c, m in items:
            s = signature(dom, m)
            (rest if s in seen else first).append(c)
            seen.add(s)
        chosen = (first + rest)[:per_class]
        pick["pos"] += [(dom, c) for c in sorted(chosen)]
        print(f"{cls}: {len(chosen)} of {len(items)} ({len(first)} signatures)", file=sys.stderr)
    # mutants and out-of-domain chunks
    fams = {}
    for c in sorted(os.listdir(os.path.join(corpus, "mutants"))):
        m = json.load(open(os.path.join(corpus, "mutants", c, "meta.json")))
        fams.setdefault((bool(m.get(key)), family(m)), []).append(c)
    for (acc, fam), cs in sorted(fams.items()):
        rng.shuffle(cs)
        pick["acc" if acc else "rej"] += [("mutants", c) for c in sorted(cs[:per_family])]
    oods = {}
    for c in sorted(os.listdir(os.path.join(corpus, "ood"))):
        m = json.load(open(os.path.join(corpus, "ood", c, "meta.json")))
        v = "+".join(m.get(dom + "_violations", [])) or "?"
        oods.setdefault(v, []).append(c)
    for v, cs in sorted(oods.items()):
        rng.shuffle(cs)
        pick["rej"] += [("ood", c) for c in sorted(cs[:per_family])]
    for sub, c in pick["pos"] + pick["acc"] + pick["rej"]:
        os.makedirs(os.path.join(sel, sub), exist_ok=True)
        dst = os.path.join(sel, sub, c)
        if not os.path.exists(dst):
            os.symlink(os.path.abspath(os.path.join(corpus, sub, c)), dst)
    if os.path.exists(os.path.join(corpus, "summary.json")):
        s = json.load(open(os.path.join(corpus, "summary.json")))
        s["public_selection"] = {"per_class": per_class, "per_family": per_family, "seed": seed,
                                 "positives": len(pick["pos"]), "accepted_mutants": len(pick["acc"]),
                                 "rejections": len(pick["rej"])}
        json.dump(s, open(os.path.join(sel, "summary.json"), "w"), indent=1, sort_keys=True)
    print({k: len(v) for k, v in pick.items()}, file=sys.stderr)


if __name__ == "__main__":
    main()
