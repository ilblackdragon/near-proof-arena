#!/usr/bin/env python3
"""Bind opt-in nearcore `yield` / `storage-limits` scenario runs to observed outcomes and cases.

Input is a run directory of `oracle/v3-successor` (`NEAR_SUCCESSOR_SCENARIO=yield|storage-limits`)
with its `scenario-<chain>.json`. Every expectation below is checked against nearcore's own
recorded outcome tree (transaction, receipts, yield callbacks and their execution heights), never
against a label or against Lean. A violated expectation fails the collection unless it is listed
as timing-dependent (chunk-alignment) and the run has missing chunks.

Each scenario step is mapped to the honest cases whose main transition applied it: the chunk that
included the transaction (its label is in `tx_labels`) and, for each later receipt, the first
case of the executor's shard created after the execution height (the witness for chunk H+1
validates the application of chunk H; missing chunks shift this to the next produced chunk).
"""
import argparse
import collections
import hashlib
import json
from pathlib import Path
import re
import sys

PER_RECEIPT_LIMIT = 4_000_000
SOFT_LIMIT = 4_000_000


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def index_cases(run):
    """(shard -> sorted [(height, case_dir)]), label -> [case_dir], case_dir -> meta"""
    by_shard = collections.defaultdict(list)
    by_label = collections.defaultdict(list)
    metas = {}
    for meta_path in sorted(run.glob("*/*/meta.json")):
        meta = json.loads(meta_path.read_text())
        if meta.get("kind") != "honest":
            continue
        rel = str(meta_path.parent.relative_to(run))
        m = re.fullmatch(r"(\d+)-h(\d+)-s(\d+)", meta_path.parent.name)
        by_shard[m.group(3)].append((int(m.group(2)), rel))
        metas[rel] = meta
        for label in meta.get("tx_labels", []):
            by_label[label].append(rel)
    for v in by_shard.values():
        v.sort()
    return by_shard, by_label, metas


def case_after(by_shard, shard, height):
    for h, rel in by_shard[shard]:
        if h > height:
            return rel
    return None


def status_of(o):
    st = o["status"]
    if isinstance(st, dict) and "SuccessValue" in st:
        return "value", st["SuccessValue"]
    if isinstance(st, dict) and "SuccessReceiptId" in st:
        return "receipt", st["SuccessReceiptId"]
    return "failure", st


# --------------------------------------------------------------------------------------------
# yield
# --------------------------------------------------------------------------------------------

def hx(s):
    return s.encode().hex()


# label suffix -> expectation on (fc = the yield-account function-call receipt, cb = its callback)
#   ret: exact hex return of fc; fail: substring of fc failure; cb: hex prefix of the callback
#   return ([status] ++ payload); cb_fail: substring of a failing callback; no_cb: no callback ran;
#   cb_delay: callback height - fc height; note: a cross-shard note receipt executed
YIELD_EXPECT = {
    "00.create-later": dict(ret_len=32, cb="01" + hx("later-chunk")),
    "01.create-timeout": dict(ret_len=32, cb="02", cb_delay=201),
    "02.create-resume-same-receipt": dict(ret="01", cb="01" + hx("same-receipt"), cb_delay=1),
    "03.create-same-chunk": dict(ret_len=32, cb="01" + hx("same-chunk"), cb_delay=1),
    "04.resume-same-chunk": dict(ret="01", same_height_as="03.create-same-chunk"),
    "05.resume-later-chunk": dict(ret="01"),
    "06.create-dup-same-receipt": dict(ret_len=32, cb="01" + hx("twice")),
    "07.resume-twice-same-receipt": dict(ret="0101"),
    "08.create-dup-separate": dict(ret_len=32, cb="01" + hx("first")),
    "09.resume-dup-first": dict(ret="01"),
    "10.resume-dup-second-same-chunk": dict(ret="01", same_height_as="09.resume-dup-first"),
    "11.resume-after-completion": dict(ret="00"),
    "12.resume-wrong-data-id": dict(ret="00"),
    "13.resume-malformed-data-id": dict(fail="malformed"),
    "14.create-payload-max": dict(ret_len=32, cb="01" + "77" * 1024),
    "15.create-payload-over": dict(ret_len=32, cb="02", cb_delay=201),
    "16.resume-payload-1024": dict(ret="01"),
    "17.resume-payload-1025": dict(fail="1024 byte limit"),
    "18.cross-shard-create": dict(ret_len=32, cb="01" + hx("from-shard-1"), note=True, cross=True),
    "19.cross-shard-create-timeout": dict(ret_len=32, cb="02", cb_delay=201, note=True, cross=True),
    "20.cross-shard-resume": dict(ret="01", cross=True),
    "21.create-then-fail": dict(fail="panicked", no_cb=True),
    "22.createid": dict(ret="0000000000000000", cb="01" + hx("by-id")),
    "23.createid-duplicate": dict(ret="ffffffffffffffff", same_height_as="22.createid", no_cb=True),
    "24.resumeid": dict(ret="01"),
    "25.resumeid-unknown": dict(ret="00"),
    "26.create-returned": dict(ret_receipt=True, cb="01" + hx("returned")),
    "27.resume-returned": dict(ret="01"),
    "28.create-callback-panics": dict(ret_len=32, cb_fail="panicked"),
    "29.resume-callback-panics": dict(ret="01"),
    "30.create-race": dict(ret_len=32, cb="01" + hx("race"), cb_delay=201),
    "31.createid-timeout": dict(ret="0000000000000000", cb="02", cb_delay=201),
    "32.resume-at-timeout": dict(ret="01", height_after="30.create-race", delay=200),
    "33.resume-after-timeout": dict(ret="00"),
    # the timeout resume is cancelled (status ResumeInitiated) by a local resume in the chunk after
    # the timeout loop; the callback receives the payload one chunk later than a timeout would
    "34.create-race-cancel": dict(ret_len=32, cb="01" + hx("cancel"), cb_delay=202),
    "35.resume-after-timeout-fired": dict(ret="01", height_after="34.create-race-cancel", delay=201),
}
TIMING = {"cb_delay", "same_height_as", "height_after"}


def yield_steps(sc, by_shard, by_label, timing_ok):
    shards = sc["shards"]
    rows, problems, timing = [], [], []
    fc_height = {}
    for sub in sc["submitted"]:
        label = sub["label"]
        key = label.removeprefix("successor.yield.")
        exp = YIELD_EXPECT.get(key)
        if exp is None:
            problems.append(f"no expectation for {label}")
            continue
        outs = sub["outcomes"]
        if not outs or not all(o["executed"] for o in outs):
            problems.append(f"{label}: unexecuted outcome")
            continue
        tx = outs[0]
        fc = next(o for o in outs[1:] if o["executor"] == "s0yield")
        fc_height[key] = fc["height"]
        children = [o for o in outs if o["id"] in fc["receipt_ids"]]
        # the callback is the executed yield receipt: the child of fc that returns a status byte
        # or fails; zero-value refunds return an empty value
        cbs = [o for o in children if o["executor"] == "s0yield" and status_of(o) != ("value", "")]
        notes = [o for o in outs if o["executor"] == "s2ynote"]
        kind, val = status_of(fc)
        got = dict(tx_height=tx["height"], fc_height=fc["height"], fc_status=kind,
                   fc_value=val if kind != "failure" else None, fc_failure=val if kind == "failure" else None,
                   callbacks=[dict(height=o["height"], status=status_of(o)[0],
                                   value=status_of(o)[1] if status_of(o)[0] == "value" else None,
                                   failure=status_of(o)[1] if status_of(o)[0] == "failure" else None)
                              for o in cbs],
                   notes=[o["height"] for o in notes])
        def check(cond, what):
            if not cond:
                (timing if what in TIMING else problems).append(f"{label}: {what}")
        if "ret" in exp:
            check(kind == "value" and val == exp["ret"], "ret")
        if "ret_len" in exp:
            check(kind == "value" and len(val) == 2 * exp["ret_len"], "ret_len")
        if exp.get("ret_receipt"):
            check(kind == "receipt", "ret_receipt")
        if "fail" in exp:
            check(kind == "failure" and exp["fail"] in val, "fail")
        if "cb" in exp:
            check(len(cbs) == 1 and status_of(cbs[0])[0] == "value" and status_of(cbs[0])[1] == exp["cb"], "cb")
        if "cb_fail" in exp:
            check(len(cbs) == 1 and status_of(cbs[0])[0] == "failure" and exp["cb_fail"] in status_of(cbs[0])[1], "cb_fail")
        if exp.get("no_cb"):
            check(not cbs, "no_cb")
        if "cb_delay" in exp and cbs:
            check(cbs[0]["height"] - fc["height"] == exp["cb_delay"], "cb_delay")
        if exp.get("note"):
            check(len(notes) == 1 and status_of(notes[0])[0] == "value", "note")
        if exp.get("cross"):
            check(tx["executor"] == "s1ycall" and shards["s1ycall"] != shards["s0yield"], "cross")
        if "same_height_as" in exp:
            check(fc_height.get(exp["same_height_as"]) == fc["height"], "same_height_as")
        if "height_after" in exp:
            check(fc["height"] - fc_height.get(exp["height_after"], -10**9) == exp["delay"], "height_after")
        # cases: inclusion chunk, fc execution, each callback and the timeout chunk before it
        cases = dict(included=sorted(set(by_label.get(label, []))),
                     fc=case_after(by_shard, shards["s0yield"], fc["height"]),
                     callbacks=[case_after(by_shard, shards["s0yield"], o["height"]) for o in cbs],
                     notes=[case_after(by_shard, shards["s2ynote"], h) for h in got["notes"]])
        if "cb_delay" in exp and exp["cb_delay"] == 201 and cbs:
            # the yield-timeout loop ran in the chunk applied just before the callback
            cases["timeout"] = case_after(by_shard, shards["s0yield"], cbs[0]["height"] - 1)
        rows.append(dict(label=label, call=sub["call"], submitted_height=sub["height"], nearcore=got,
                         expectation=exp, cases=cases))
    missing = sorted(set(YIELD_EXPECT) - {r["label"].removeprefix("successor.yield.") for r in rows})
    problems += [f"missing step {m}" for m in missing]
    if timing and not timing_ok:
        problems += timing
    return rows, problems, timing


# --------------------------------------------------------------------------------------------
# storage limits
# --------------------------------------------------------------------------------------------

def storage_probes(sc, by_shard, by_label, metas):
    shards = sc["shards"]
    lanes, problems = [], []
    for lane in sc["lanes"]:
        acct = "s0zlim" if lane["kind"] == "Receipt" else "s1zsoft"
        if lane["phase"] != "Done":
            problems.append(f"{lane['kind']} lane unfinished ({lane['phase']})")
        probes = []
        for p in lane["probes"]:
            a0 = p["a"][0]
            inc = sorted(set(by_label.get(a0["label"], [])))
            case = inc[0] if inc else None
            meta = metas.get(case, {})
            f = meta.get("features", {})
            probes.append(dict(
                label=p["label"], pad=p["t"], pass_=p["pass"], probe_height=p["probe_height"],
                probes=[dict(program=x["program"], ok=x["ok"], height=x["height"], status=x["status"]) for x in p["a"]],
                incoming=[dict(ok=x["ok"], height=x["height"]) for x in p["b"]],
                incoming_deferred=p["incoming_deferred"], case=case,
                deferred_case=[case_after(by_shard, shards[acct], x["height"] - 1) for x in p["b"] if x["height"] > p["probe_height"]],
                base_state_bytes=f.get("base_state_bytes"), witness_bytes=f.get("witness_bytes"),
                delayed_queue_post=f.get("delayed_queue_post"), nearcore=meta.get("nearcore")))
        # the decisive boundary facts (nearcore outcomes only)
        at = lane["boundary_pad"]
        fin = {p["label"]: p for p in probes}
        ok = (at is not None and fin.get("final-below", {}).get("pass_") is True
              and fin.get("final-at", {}).get("pass_") is True and fin.get("final-above", {}).get("pass_") is False
              and fin["final-at"]["pad"] + 1 == fin["final-above"]["pad"])
        if not ok:
            problems.append(f"{lane['kind']} lane: final below/at/above do not bracket the boundary")
        out = dict(kind=lane["kind"], account=acct, shard=shards[acct], boundary_pad=at,
                   removal_boundary_pad=lane.get("removal_boundary_pad"), iterations=lane["iterations"],
                   probes=probes)
        if lane["kind"] == "Receipt":
            rm = lane.get("removal_boundary_pad")
            out["removal_shift_bytes"] = (at - rm) if (at is not None and rm is not None) else None
            # value length of `big` + the pad length is the knob; the remaining overhead is fixed
            out["fixed_overhead_bytes"] = PER_RECEIPT_LIMIT - sc["sizes"]["big_receipt"] - at if at is not None else None
        else:
            above = fin.get("final-above", {})
            atp = fin.get("final-at", {})
            # with the incoming receipt deferred, the chunk's recording stops right after the probe
            out["deferral_chunk_recorded_bytes"] = above.get("base_state_bytes")
            out["at_chunk_recorded_bytes"] = atp.get("base_state_bytes")
            if above.get("base_state_bytes") != SOFT_LIMIT + 1:
                problems.append("soft lane: deferral chunk does not record exactly limit + 1 bytes")
            # yield-timeout resolution and the soft limit (`resolve_promise_yield_timeouts`)
            for name, want in (("timeout-below", True), ("timeout-above", False)):
                tp = fin.get(name)
                if tp is None or tp["pass_"] is not want:
                    problems.append(f"soft lane: {name} probe missing or pass != {want}")
            for p_raw, p in zip(lane["probes"], probes):
                if p_raw.get("anchor"):
                    p["anchor"] = p_raw["anchor"]
                    p["anchor"]["callback_case"] = case_after(by_shard, shards["s1zyield"], p_raw["anchor"]["callback_height"] - 1)
        lanes.append(out)
    return lanes, problems


def misc_steps(sc, by_shard, by_label):
    rows = []
    for sub in sc["submitted"]:
        if ".misc." not in sub["label"] and ".code." not in sub["label"]:
            continue
        outs = [o for o in sub["outcomes"][1:] if o["executed"]]
        fc = outs[0] if outs else None
        rows.append(dict(label=sub["label"], call=sub["call"],
                         status=status_of(fc)[0] if fc else "unexecuted",
                         failure=status_of(fc)[1] if fc and status_of(fc)[0] == "failure" else None,
                         height=fc["height"] if fc else None,
                         cases=sorted(set(by_label.get(sub["label"], [])))))
    return rows


MISC_EXPECT = {
    "code.call-small-code-near-limit": "value", "code.deploy-large": "value",
    "code.call-large-code-near-limit": "value", "code.call-large-code-repeated-read": "value",
    "code.deploy-and-call-same-receipt": "value", "code.call-large-code-read-then-fail": "failure",
    "misc.delete-reinsert": "value", "misc.delete-missing": "value", "misc.delete-29": "value",
    "misc.reinsert-29-then-fail": "failure", "misc.repeated-shared-reads": "value",
    "misc.delete-big-reinsert": "value", "misc.read-reinserted-big": "value",
}


def collect(run):
    sc_path = next(run.glob("scenario-*.json"))
    sc = json.loads(sc_path.read_text())
    by_shard, by_label, metas = index_cases(run)
    summary = json.loads((run / "summary.json").read_text())
    p_missing = re.search(r"p_missing: ([0-9.]+)", summary["chains"][0])
    timing_ok = p_missing is not None and float(p_missing.group(1)) > 0
    out = dict(run=str(run), scenario=sc["scenario"], scenario_json_sha256=sha(sc_path),
               chain_params=summary["chains"], honest=summary["honest_witnesses"],
               honest_accepted_by_nearcore=summary["honest_accepted_by_nearcore"],
               mutants=summary["mutants"], shards=sc["shards"], contracts=sc["contracts"])
    problems = []
    if summary["honest_witnesses"] != summary["honest_accepted_by_nearcore"]:
        problems.append("an honest witness was rejected by the cold validator")
    if sc["scenario"] == "Yield":
        rows, p, timing = yield_steps(sc, by_shard, by_label, timing_ok)
        out.update(steps=rows, timing_deviations=timing)
        problems += p
    else:
        lanes, p = storage_probes(sc, by_shard, by_label, metas)
        misc = misc_steps(sc, by_shard, by_label)
        for m in misc:
            key = m["label"].removeprefix("successor.storage-limits.")
            if MISC_EXPECT.get(key) != m["status"]:
                p.append(f"{m['label']}: {m['status']} (expected {MISC_EXPECT.get(key)})")
        missing = set(MISC_EXPECT) - {m["label"].removeprefix("successor.storage-limits.") for m in misc}
        p += [f"missing misc step {k}" for k in sorted(missing)]
        out.update(sizes=sc["sizes"], lanes=lanes, misc=misc)
        problems += p
    out["problems"] = problems
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--source", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    out = collect(a.source)
    a.out.write_text(json.dumps(out, indent=1) + "\n")
    for p in out["problems"]:
        print("PROBLEM:", p, file=sys.stderr)
    return 1 if out["problems"] else 0


if __name__ == "__main__":
    sys.exit(main())
