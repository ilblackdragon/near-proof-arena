"""CLI: python -m arena_bench <command> (run from benchmarks/, or with PYTHONPATH=benchmarks).

  score        --input classes.json             (list of {class_id, weight_ppm, baseline_ns, median_ns})
  bootstrap    --input runs.json --seed N [--iterations B]
  outliers     --input runs.json --k K          (list of u64)
  drift        --pre a,b,c --post d,e,f [--threshold-ppm N] [--reference-ns N]
  schedule     --classes a,b,c --seed N --cold N --warmup N --measured N [--fresh N] [--calibration N]
  seed         --purpose P [parts...]
  report       --input bundle.json [--out report.md]
  host-profile --id ID [--governed] [--out file.json]
  gen-testvectors [--out path] [--check]   (score.json and cost.json next to it)
  cost-rescore --challenge chl.json --price-model pm.json --baseline-session S.json [--cost-baseline summary.json] VIEW:SESSION...  (offline, §14.8)
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict
from pathlib import Path

from . import hostprofile, report, testvectors
from .calibration import check_drift
from .outliers import flag_outliers
from .schedule import build_schedule
from .score import ScoreError, bootstrap_ci, class_inputs_from_json, class_runs_from_json, score
from .seeds import derive_seed

DEFAULT_VECTORS = Path(__file__).resolve().parent.parent / "testvectors" / "score.json"


def _load(path: str):
    return json.loads(Path(path).read_text() if path != "-" else sys.stdin.read())


def _ints(s: str) -> list[int]:
    return [int(x) for x in s.split(",") if x.strip()]


def _emit(obj, out: str | None = None) -> None:
    text = obj if isinstance(obj, str) else json.dumps(obj, indent=1, ensure_ascii=False) + "\n"
    if out:
        Path(out).write_text(text)
    else:
        sys.stdout.write(text)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="arena_bench")
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("score"); p.add_argument("--input", required=True)
    p = sub.add_parser("bootstrap"); p.add_argument("--input", required=True); p.add_argument("--seed", type=int, required=True); p.add_argument("--iterations", type=int, default=10_000)
    p = sub.add_parser("outliers"); p.add_argument("--input", required=True); p.add_argument("--k", type=int, required=True)
    p = sub.add_parser("drift"); p.add_argument("--pre", required=True); p.add_argument("--post", required=True)
    p.add_argument("--threshold-ppm", type=int, default=20_000); p.add_argument("--reference-ns", type=int); p.add_argument("--reference-threshold-ppm", type=int, default=50_000)
    p = sub.add_parser("schedule"); p.add_argument("--classes", required=True); p.add_argument("--seed", type=int, required=True)
    for f in ("cold", "warmup", "measured"):
        p.add_argument(f"--{f}", type=int, required=True)
    p.add_argument("--fresh", type=int, default=1); p.add_argument("--calibration", type=int, default=5)
    p = sub.add_parser("seed"); p.add_argument("--purpose", required=True); p.add_argument("parts", nargs="*")
    p = sub.add_parser("report"); p.add_argument("--input", required=True); p.add_argument("--out")
    p = sub.add_parser("host-profile"); p.add_argument("--id", required=True); p.add_argument("--governed", action="store_true"); p.add_argument("--note"); p.add_argument("--out")
    p = sub.add_parser("gen-testvectors"); p.add_argument("--out", default=str(DEFAULT_VECTORS)); p.add_argument("--check", action="store_true")
    p = sub.add_parser("cost-rescore"); p.add_argument("--challenge", required=True); p.add_argument("--price-model", required=True)
    p.add_argument("--baseline-session", required=True); p.add_argument("--out"); p.add_argument("subs", nargs="+", help="VIEW.json:SESSION.json")
    p.add_argument("--cost-baseline", help="run_baseline.py summary.json re-measuring the reference (verify/bytes; §14.4 control must pass)")
    p.add_argument("--allow-unconfirmed", action="store_true", help="re-score against a cost baseline whose verify control failed (labelled UNCONFIRMED)")
    a = ap.parse_args(argv)

    try:
        if a.cmd == "score":
            r = score(class_inputs_from_json(_load(a.input)))
            _emit({"score_milli": r.score_milli, "score_f64": repr(r.score_f64)})
        elif a.cmd == "bootstrap":
            _emit(asdict(bootstrap_ci(class_runs_from_json(_load(a.input)), a.seed, a.iterations)))
        elif a.cmd == "outliers":
            _emit(asdict(flag_outliers(_load(a.input), a.k)))
        elif a.cmd == "drift":
            v = check_drift(_ints(a.pre), _ints(a.post), a.threshold_ppm, a.reference_ns, a.reference_threshold_ppm)
            _emit(asdict(v))
            return 0 if v.ok else 3
        elif a.cmd == "schedule":
            s = build_schedule(a.classes.split(","), a.seed, a.cold, a.warmup, a.measured, a.fresh, a.calibration)
            _emit({"seed": str(a.seed), "runs": [e.to_json() for e in s]})
        elif a.cmd == "seed":
            _emit({"seed": derive_seed(a.purpose, *a.parts)})
        elif a.cmd == "report":
            _emit(report.render(_load(a.input)), a.out)
        elif a.cmd == "host-profile":
            _emit(hostprofile.collect(a.id, governed=a.governed, note=a.note), a.out)
        elif a.cmd == "cost-rescore":
            from . import rescore

            r = rescore.main(a.challenge, a.price_model, a.baseline_session, a.subs, a.out, a.cost_baseline, a.allow_unconfirmed)
            if not a.out:
                _emit(rescore.markdown(r))
        elif a.cmd == "gen-testvectors":
            outs = [(Path(a.out), testvectors.dumps(testvectors.generate())),
                    (Path(a.out).with_name("cost.json"), testvectors.dumps(testvectors.generate_cost()))]
            if a.check:
                stale = [str(p) for p, text in outs if not p.exists() or p.read_text() != text]
                if stale:
                    print(f"{', '.join(stale)} stale; regenerate with gen-testvectors", file=sys.stderr)
                    return 1
                print("test vectors up to date")
            else:
                for p, text in outs:
                    p.write_text(text)
    except ScoreError as e:
        _emit({"error": e.code, "detail": str(e)})
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
