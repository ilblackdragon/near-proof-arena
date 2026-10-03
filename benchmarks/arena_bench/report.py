"""Markdown benchmark report renderer (docs/BENCHMARK_SPEC.md §13).

Input: a "bench report bundle" JSON object:

  {
    "submission_id": "sub_...", "challenge_id": "chl_...", "tier": "formal",
    "result": <arena_types::BenchmarkResult>,
    "schedule_seed": "<u64 decimal string>",          (optional)
    "calibration": {<DriftVerdict fields>},           (optional)
    "outliers": {"<class_id>": {<OutlierReport fields>}}, (optional)
    "tripwire": {"<class_id>": {<TripwireResult fields>}}, (optional)
    "host": <arena-host-profile-v1>,                  (optional)
    "second_machine": {"hardware_profile": "...", "score_milli": N} (optional)
  }

All text originating from the bundle is escaped; numbers are formatted with
integer arithmetic only (no float formatting differences between hosts).
"""

from __future__ import annotations

from typing import Any, Mapping, Optional

_ESC = str.maketrans({"|": "\\|", "<": "&lt;", ">": "&gt;", "`": "\\`", "\n": " ", "\r": " ", "*": "\\*", "_": "\\_", "[": "\\[", "]": "\\]"})


def esc(s: Any) -> str:
    return str(s).translate(_ESC)[:200]


def code(s: Any) -> str:
    """Inline code span: content is literal in Markdown, so only strip what could end it."""
    t = str(s).replace("`", "'").replace("\n", " ").replace("\r", " ").replace("|", "/")[:200]
    return f"`{t}`"


def fmt_milli(m: Optional[int]) -> str:
    if m is None:
        return "—"
    return f"{m // 1000}.{m % 1000:03d}"


def fmt_ns(ns: Optional[int]) -> str:
    """ns -> human string with 3 decimals in the largest unit >= 1."""
    if ns is None:
        return "—"
    for unit, div in (("s", 1_000_000_000), ("ms", 1_000_000), ("µs", 1_000)):
        if ns >= div:
            q = ns * 1000 // div
            return f"{q // 1000}.{q % 1000:03d} {unit}"
    return f"{ns} ns"


def fmt_bytes(b: Optional[int]) -> str:
    if b is None:
        return "—"
    for unit, div in (("GiB", 1 << 30), ("MiB", 1 << 20), ("KiB", 1 << 10)):
        if b >= div:
            q = b * 100 // div
            return f"{q // 100}.{q % 100:02d} {unit}"
    return f"{b} B"


def speedup_milli(baseline_ns: int, cand_ns: int) -> Optional[int]:
    if not cand_ns:
        return None
    return (baseline_ns * 1000 + cand_ns // 2) // cand_ns


def render(bundle: Mapping[str, Any]) -> str:
    r = bundle["result"]
    tier = bundle.get("tier", "unknown")
    L: list[str] = []
    L.append(f"# Benchmark report — {esc(bundle.get('submission_id', '?'))}")
    L.append("")
    if tier != "formal":
        L.append(f"> **{esc(str(tier).upper())} tier** — diagnostic numbers only, not an official ranking.")
        L.append("")
    if bundle.get("host") and not bundle["host"].get("governed", False):
        L.append("> **Non-governed host** — numbers are not comparable to official results.")
        L.append("")
    L.append(f"* Challenge: {code(bundle.get('challenge_id', '?'))}")
    L.append(f"* Hardware profile: {code(r.get('hardware_profile'))}  · suite revision: {code(r.get('suite_revision'))}")
    L.append(f"* Measured by: {code(r.get('measured_by'))}")
    if "schedule_seed" in bundle:
        L.append(f"* Run-order seed: {code(bundle['schedule_seed'])}")
    sm, ci = r.get("score_milli"), r.get("score_ci_milli")
    if sm is None:
        L.append("* **Score: none** (not accepted, or score undefined)")
    else:
        lo = sm - ci if ci is not None else None
        hi = sm + ci if ci is not None else None
        ci_s = f" (95% bootstrap CI ≈ {fmt_milli(lo)} – {fmt_milli(hi)})" if ci is not None else ""
        L.append(f"* **Score: {fmt_milli(sm)}**{ci_s} — baseline = 100.000")
    L.append(
        f"* Public preprocessing (`prepare`, reported separately, not in score): {fmt_ns(r.get('prepare_ns'))}, "
        f"public artifacts {fmt_bytes(r.get('public_artifact_bytes'))}"
    )
    L.append("")
    L.append("Result statement: *best measured on this challenge, hardware profile and suite revision* — not \"provably fastest\".")
    L.append("")
    L.append("## Per-class (steady state, median of measured runs)")
    L.append("")
    L.append("| class | weight | runs | median | MAD | cold | baseline | speedup | verify median | max proof | peak RSS | flagged |")
    L.append("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    outl = bundle.get("outliers", {}) or {}
    for c in sorted(r.get("classes", []), key=lambda c: str(c.get("class_id")).encode()):
        cid = c.get("class_id")
        o = outl.get(cid)
        flagged = str(len(o.get("flagged_indices", []))) if o else "—"
        sp = speedup_milli(c.get("baseline_ns", 0), c.get("median_ns", 0))
        L.append(
            "| {} | {} ppm | {} | {} | {} | {} | {} | {}× | {} | {} | {} | {} |".format(
                esc(cid),
                c.get("weight_ppm"),
                len(c.get("runs_ns", [])),
                fmt_ns(c.get("median_ns")),
                fmt_ns(c.get("mad_ns")),
                fmt_ns(c.get("cold_ns")),
                fmt_ns(c.get("baseline_ns")),
                fmt_milli(sp),
                fmt_ns(c.get("verify_median_ns")),
                fmt_bytes(c.get("proof_bytes_max")),
                fmt_bytes(c.get("peak_rss_bytes")),
                flagged,
            )
        )
    L.append("")
    cal = bundle.get("calibration")
    if cal:
        L.append("## Calibration")
        L.append("")
        status = "OK" if cal.get("ok") else "FAILED → session discarded as INFRA, re-run"
        L.append(f"* Status: **{status}**")
        L.append(
            f"* pre {fmt_ns(cal.get('pre_median_ns'))}, post {fmt_ns(cal.get('post_median_ns'))}, "
            f"session drift {cal.get('session_drift_ppm')} ppm"
        )
        if cal.get("reference_ns") is not None:
            L.append(f"* host reference {fmt_ns(cal.get('reference_ns'))}, drift {cal.get('reference_drift_ppm')} ppm")
        if cal.get("reasons"):
            L.append(f"* reasons: {', '.join(esc(x) for x in cal['reasons'])}")
        L.append("")
    trip = bundle.get("tripwire") or {}
    if trip:
        L.append("## Fresh-input tripwire")
        L.append("")
        for cid in sorted(trip, key=lambda s: s.encode()):
            t = trip[cid]
            mark = "**CACHING_SUSPECTED**" if t.get("suspected") else "ok"
            L.append(f"* {esc(cid)}: {mark} (fresh {fmt_ns(t.get('fresh_median_ns'))} vs steady {fmt_ns(t.get('measured_median_ns'))}, +{t.get('slowdown_ppm')} ppm)")
        L.append("")
    if outl:
        notes = [(cid, o) for cid, o in sorted(outl.items()) if o.get("flagged_indices") or o.get("notes")]
        if notes:
            L.append("## Outliers (flagged, never dropped)")
            L.append("")
            for cid, o in notes:
                L.append(
                    f"* {esc(cid)}: runs {list(o.get('flagged_indices', []))} beyond {o.get('k')}·MAD"
                    + (f"; notes {', '.join(esc(n) for n in o.get('notes', []))}" if o.get("notes") else "")
                    + (" — **excessive, class re-run**" if o.get("excessive") else "")
                )
            L.append("")
    sec = bundle.get("second_machine")
    if sec:
        L.append("## Independent re-run")
        L.append("")
        L.append(f"* {esc(sec.get('hardware_profile'))}: score {fmt_milli(sec.get('score_milli'))}")
        L.append("")
    host = bundle.get("host")
    if host:
        hp = host.get("hardware_profile", {})
        L.append("## Host")
        L.append("")
        L.append(f"* {code(hp.get('id'))}: {esc(hp.get('cpu_model'))}, {hp.get('vcpus')} vCPU, {fmt_bytes(hp.get('ram_bytes'))}, GPU: {esc(hp.get('gpu') or 'none')}")
        if host.get("warnings"):
            L.append(f"* warnings: {', '.join(esc(w) for w in host['warnings'])}")
        L.append("")
    return "\n".join(L).rstrip() + "\n"
