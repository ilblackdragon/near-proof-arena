#!/usr/bin/env python3
"""End-to-end hostile-submission driver for NEAR Proof Arena.

Given a running server URL + tokens, submit every hostile package and assert the
server's final decision / gates / reason codes match each case's expect.json.
Also assert (a) no hostile submission ever becomes ADMITTED / accepted / ranked,
and (b) UI/log-injection payloads come back escaped/sanitized (no raw control
characters) from the API.

Depends only on the Python standard library (no `requests`): the arena host does
not vendor extra Python packages.

Modes
-----
  --dry-run            Package every case locally (build archives, validate
                       expect.json), NO server required. This is what runs at
                       development time and in `make e2e-hostile` when no server
                       URL is configured.
  --server URL         Full e2e against a live judge. Requires --token.

Env fallbacks: ARENA_SERVER, ARENA_TOKEN, ARENA_CHALLENGE.
"""
import argparse
import io
import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile
import time
import urllib.request
import urllib.error

HERE = os.path.dirname(os.path.abspath(__file__))
SUITE = os.path.normpath(os.path.join(HERE, "..", "hostile-submissions"))

# Raw control chars that must never appear in an API response body (ANSI ESC,
# BEL, backspace, etc.). Tab/newline/carriage-return are allowed.
CTRL = re.compile(rb"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f]")


# --------------------------------------------------------------------------- #
# case loading & packaging
# --------------------------------------------------------------------------- #

def load_cases():
    cases = []
    for name in sorted(os.listdir(SUITE)):
        d = os.path.join(SUITE, name)
        exp = os.path.join(d, "expect.json")
        if not os.path.isdir(d) or not os.path.exists(exp):
            continue
        with open(exp) as f:
            cases.append((name, d, json.load(f)))
    return cases


REPO = os.path.normpath(os.path.join(HERE, "..", ".."))
EXCLUDE_TOP = {"expect.json", "make-archive.sh", "make-archive.py", "archive-kind", "out", "BASE"}
EXCLUDE_ANY = {".git", "target", ".lake"}


def _walk(root_dir, exclude_top):
    """`arena pack` file set of a directory: {package-relative path: full path}."""
    out = {}
    for root, dirs, filenames in os.walk(root_dir):
        rel_root = os.path.relpath(root, root_dir)
        dirs[:] = [d for d in dirs
                   if d not in EXCLUDE_ANY and not (rel_root == "." and d in exclude_top)]
        for fn in filenames:
            full = os.path.join(root, fn)
            rel = os.path.relpath(full, root_dir)
            if rel_root == "." and fn in exclude_top:
                continue
            if os.path.islink(full) or not os.path.isfile(full):
                raise RuntimeError(f"{rel}: not a regular file (arena pack refuses it)")
            out[rel] = full
    return out


def _base_files(base_dir):
    """Tracked files of the base package (git ls-files, like milestone-d's
    stage_dir), falling back to a pruned walk outside a git checkout."""
    try:
        r = subprocess.run(["git", "ls-files", "-z", "--", "."], cwd=base_dir,
                           capture_output=True, check=True)
        rels = [x for x in r.stdout.decode().split("\0") if x]
        if rels:
            out = {}
            for rel in rels:
                full = os.path.join(base_dir, rel)
                if rel.split("/")[0] == "out" or any(p in EXCLUDE_ANY for p in rel.split("/")):
                    continue
                if os.path.isfile(full) and not os.path.islink(full):
                    out[rel] = full
            return out
    except (OSError, subprocess.CalledProcessError):
        pass
    return _walk(base_dir, {"out"})


def package_sources(case_dir):
    """{package path: source file} for a case. A DERIVED case (a `BASE` file
    naming a repo-relative package, e.g. examples/reexec-witness) is that
    package with the case directory's files laid over it."""
    base_file = os.path.join(case_dir, "BASE")
    src = {}
    if os.path.exists(base_file):
        base = open(base_file).read().strip()
        base_dir = os.path.normpath(os.path.join(REPO, base))
        if not base_dir.startswith(REPO + os.sep) or not os.path.isdir(base_dir):
            raise RuntimeError(f"BASE {base!r}: not a package directory in this repo")
        src.update(_base_files(base_dir))
    src.update(_walk(case_dir, EXCLUDE_TOP))
    return src


def materialize(case_dir, dest, challenge_id=None):
    """Write the package a case submits into `dest` (for local inspection/tests)."""
    for rel, full in package_sources(case_dir).items():
        p = os.path.join(dest, rel)
        os.makedirs(os.path.dirname(p), exist_ok=True)
        data = open(full, "rb").read()
        if rel == "candidate.toml" and challenge_id:
            data = re.sub(rb'challenge = "[^"]*"', f'challenge = "{challenge_id}"'.encode(), data)
        open(p, "wb").write(data)
        os.chmod(p, 0o755 if os.stat(full).st_mode & 0o111 else 0o644)


def build_package_bytes(case_dir, expect, challenge_id):
    """Return the raw archive bytes to upload for a case.

    Archive-attack cases run make-archive.sh (the hostile payload IS the archive
    encoding). All other cases are tarred from the directory, with the
    challenge id substituted into candidate.toml and the generator/helper files
    excluded.
    """
    mk_py = os.path.join(case_dir, "make-archive.py")
    mk_sh = os.path.join(case_dir, "make-archive.sh")
    if os.path.exists(mk_py) or os.path.exists(mk_sh):
        mk = [sys.executable, mk_py] if os.path.exists(mk_py) else ["sh", mk_sh]
        out = subprocess.run(mk, cwd=case_dir, capture_output=True)
        if out.returncode != 0:
            raise RuntimeError(f"make-archive failed: {out.stderr.decode(errors='replace')}")
        # The archive is rejected at extraction (PKG_WELLFORMED) before its
        # candidate.toml challenge is ever validated, so the placeholder is
        # left as-is (rewriting it would change the byte length and corrupt the
        # tar headers).
        return out.stdout

    # `arena pack` semantics (sdk/arena-cli/src/pack.rs): regular files only,
    # sorted by path bytes, mtime/uid/gid 0, mode 0755 iff any exec bit,
    # `.git/`, `target/`, `.lake/` pruned at any depth and the top-level
    # `out/` (build outputs are produced by the judge). The case README.md is
    # the package README (CONTRACTS §3); judge-only files are excluded.
    src = package_sources(case_dir)
    files = list(src)
    files.sort(key=lambda r: r.encode())
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w", format=tarfile.GNU_FORMAT) as tar:
        # CONTRACTS §3 layout: dependency-locks/ must exist even when empty.
        if not any(f.startswith("dependency-locks/") for f in files):
            ti = tarfile.TarInfo(name="dependency-locks")
            ti.type = tarfile.DIRTYPE
            ti.mode = 0o755
            ti.mtime = 0
            tar.addfile(ti)
        for rel in files:
            full = src[rel]
            data = open(full, "rb").read()
            if rel == "candidate.toml" and challenge_id:
                data = re.sub(rb'challenge = "[^"]*"',
                              f'challenge = "{challenge_id}"'.encode(), data)
            ti = tarfile.TarInfo(name=rel)
            ti.size = len(data)
            ti.mode = 0o755 if os.stat(full).st_mode & 0o111 else 0o644
            ti.mtime = 0
            ti.uid = ti.gid = 0
            ti.uname = ti.gname = ""
            tar.addfile(ti, io.BytesIO(data))
    return buf.getvalue()


# --------------------------------------------------------------------------- #
# dry run (no server)
# --------------------------------------------------------------------------- #

def dry_run(cases):
    print(f"# DRY RUN: packaging {len(cases)} hostile cases (no server)\n")
    fails = 0
    for name, d, expect in cases:
        try:
            pkg = build_package_bytes(d, expect, challenge_id=None)
            # expect.json invariants
            assert expect["expected_decision"] != "ADMITTED", "expects ADMITTED"
            assert "ADMITTED" in expect["must_never"], "must_never lacks ADMITTED"
            assert expect["why"].strip(), "empty rationale"
            if expect["expected_decision"] == "REJECTED":
                assert expect["expected_failing_gates"], "no failing gate"
                assert expect["expected_reason_codes"], "no reason code"
            print(f"ok   {name:30} pkg={len(pkg):>9}B gates={expect['expected_failing_gates']}")
        except Exception as e:  # noqa: BLE001
            print(f"FAIL {name:30} {e}")
            fails += 1
    print()
    if fails:
        print(f"DRY RUN FAILED: {fails} case(s)")
        return 1
    print(f"DRY RUN OK: {len(cases)} cases packaged and expect.json validated")
    return 0


# --------------------------------------------------------------------------- #
# live server
# --------------------------------------------------------------------------- #

class Client:
    def __init__(self, base, token):
        self.base = base.rstrip("/")
        self.token = token

    def _req(self, method, path, body=None, raw=False, ctype="application/json"):
        url = self.base + path
        data = body if raw else (json.dumps(body).encode() if body is not None else None)
        req = urllib.request.Request(url, data=data, method=method)
        req.add_header("Authorization", f"Bearer {self.token}")
        if data is not None:
            req.add_header("Content-Type", "application/octet-stream" if raw else ctype)
        with urllib.request.urlopen(req, timeout=60) as resp:
            return resp.status, resp.read()

    def upload(self, pkg_bytes):
        _, body = self._req("POST", "/v1/uploads", body=pkg_bytes, raw=True)
        return json.loads(body)

    def submit(self, challenge_id, upload_digest, idem, parent=None):
        payload = {"challenge_id": challenge_id, "upload_digest": upload_digest,
                   "idempotency_key": idem}
        if parent:
            payload["parent"] = parent
        _, body = self._req("POST", "/v1/submissions", body=payload)
        return json.loads(body), body

    def get_submission(self, sid):
        _, body = self._req("GET", f"/v1/submissions/{sid}")
        return json.loads(body), body

    def challenges(self):
        _, body = self._req("GET", "/v1/challenges")
        return json.loads(body)

    def leaderboard(self, challenge_id):
        try:
            _, body = self._req("GET", f"/v1/leaderboards/{challenge_id}")
            return json.loads(body), body
        except urllib.error.HTTPError:
            return None, b""


OBSERVED = {}

TERMINAL = {"ADMITTED", "REJECTED", "INCONCLUSIVE", "INFRA_ERROR", "CANCELLED"}


def poll_decision(client, sid, timeout_s):
    deadline = time.time() + timeout_s
    last = None
    while time.time() < deadline:
        view, raw = client.get_submission(sid)
        last = (view, raw)
        if view.get("decision") in TERMINAL:
            return view, raw
        time.sleep(2)
    return last if last else (None, b"")


def check_case(client, name, d, expect, challenge_id, timeout_s):
    """Return (ok: bool, messages: list[str])."""
    msgs = []
    pkg = build_package_bytes(d, expect, challenge_id)
    up = client.upload(pkg)
    idem = f"hostile-{name}-{int(time.time())}"
    view, _raw = client.submit(challenge_id, up["digest"], idem)
    sid = view["id"]
    view, raw = poll_decision(client, sid, timeout_s)
    if view is None:
        return False, [f"{name}: no response"]

    decision = view.get("decision")
    gates = {g["gate"]: g for g in view.get("gates", [])}
    OBSERVED[name] = {
        "submission": sid,
        "decision": decision,
        "accepted": view.get("accepted"),
        "failed_gates": sorted(g for g, v in gates.items() if v.get("status") == "FAIL"),
        "unknown_gates": sorted(g for g, v in gates.items() if v.get("status") == "UNKNOWN"),
        "reason_codes": sorted(set(view.get("reason_codes", [])) | {rc for v in gates.values() for rc in v.get("reason_codes", [])}),
        "expected_decision": expect["expected_decision"],
        "expected_failing_gates": expect["expected_failing_gates"],
        "expected_reason_codes": expect["expected_reason_codes"],
    }
    all_reasons = set(view.get("reason_codes", []))
    for g in view.get("gates", []):
        all_reasons.update(g.get("reason_codes", []))

    # --- hard invariant: never admitted / accepted / ranked ---
    if decision == "ADMITTED":
        return False, [f"{name}: ADMITTED a hostile submission!"]
    if view.get("accepted") is True:
        return False, [f"{name}: accepted=true on a hostile submission!"]
    if view.get("score_milli") is not None:
        msgs.append(f"{name}: WARNING score present on hostile submission")

    # --- expected decision ---
    if decision != expect["expected_decision"]:
        return False, [f"{name}: decision {decision} != expected {expect['expected_decision']}"]

    # --- at least one expected gate FAILed ---
    exp_gates = expect["expected_failing_gates"]
    if exp_gates:
        failed = [g for g in exp_gates if gates.get(g, {}).get("status") == "FAIL"]
        if not failed:
            present = {g: gates.get(g, {}).get("status") for g in exp_gates}
            return False, [f"{name}: none of expected gates FAILed: {present}"]

    # --- expected reason codes all present somewhere ---
    missing = [rc for rc in expect["expected_reason_codes"] if rc not in all_reasons]
    if missing:
        return False, [f"{name}: missing reason codes {missing}; saw {sorted(all_reasons)}"]

    # --- leaderboard must not RANK this submission (the server lists every
    # submission, unranked ones with rank null) ---
    lb, lb_raw = client.leaderboard(challenge_id)
    for e in (lb or []):
        if isinstance(e, dict) and e.get("submission_id") == sid and e.get("rank") is not None:
            return False, [f"{name}: hostile submission is RANKED on the leaderboard!"]

    # --- UI/log injection: response must be sanitized ---
    if expect["attack_family"] == "ui-log-injection":
        hits = CTRL.findall(raw)
        if hits:
            return False, [f"{name}: raw control chars in API response: {hits[:4]}"]
        # raw <script> in a rendered-string field is a red flag; JSON-escaped is ok
        if b"<script>" in raw:
            msgs.append(f"{name}: WARNING raw '<script>' in response "
                        "(acceptable for JSON clients, must be escaped by the UI)")

    msgs.append(f"{name}: OK decision={decision} gates_failed={exp_gates} "
                f"reasons={sorted(all_reasons & set(expect['expected_reason_codes']))}")
    return True, msgs


def applicable(expect, target):
    """Whether a case should be submitted for this run's target challenge kind."""
    if target not in expect.get("targets", ["demo"]):
        return False, f"target {target} not in {expect.get('targets', ['demo'])}"
    if not expect.get("runnable", True):
        return False, "runnable=false (documented; needs a reexec-witness NEAR backend)"
    return True, ""


def live_run(cases, server, token, challenge_id, timeout_s, target):
    client = Client(server, token)
    if not challenge_id:
        chs = client.challenges()
        if not chs:
            print("no challenges on server; set ARENA_CHALLENGE", file=sys.stderr)
            return 2
        challenge_id = chs[0]["id"] if isinstance(chs[0], dict) else chs[0]
    print(f"# LIVE e2e against {server}, challenge {challenge_id}, target={target}\n")

    fails = 0
    skipped = 0
    for name, d, expect in cases:
        ok_run, why = applicable(expect, target)
        if not ok_run:
            print(f"skip {name}: {why}")
            OBSERVED[name] = {"skipped": why}
            skipped += 1
            continue
        try:
            ok, msgs = check_case(client, name, d, expect, challenge_id, timeout_s)
        except Exception as e:  # noqa: BLE001
            ok, msgs = False, [f"{name}: driver error: {e}"]
        for m in msgs:
            print(("ok   " if ok else "FAIL ") + m)
        if not ok and name in OBSERVED:
            o = OBSERVED[name]
            print(f"     observed: decision={o['decision']} failed={o['failed_gates']} "
                  f"unknown={o['unknown_gates']} reasons={o['reason_codes']}")
        if name in OBSERVED:
            OBSERVED[name]["ok"] = ok
        if not ok:
            fails += 1
    print()
    ran = len(cases) - skipped
    if fails:
        print(f"E2E FAILED: {fails}/{ran} run hostile cases did not behave as expected "
              f"({skipped} skipped for target={target})")
        return 1
    print(f"E2E OK: all {ran} run hostile cases REJECTED with the expected gates/reasons; "
          f"none admitted or ranked; injection payloads sanitized ({skipped} skipped "
          f"for target={target})")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--server", default=os.environ.get("ARENA_SERVER"))
    ap.add_argument("--token", default=os.environ.get("ARENA_TOKEN"))
    ap.add_argument("--challenge", default=os.environ.get("ARENA_CHALLENGE"))
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--only", default="", help="comma-separated case names to run")
    ap.add_argument("--materialize", default="",
                    help="write each selected case's package to DIR/<case> and exit")
    ap.add_argument("--target", default=os.environ.get("ARENA_HOSTILE_TARGET", "demo"),
                    choices=["demo", "near-formal"],
                    help="challenge kind; cases whose targets exclude it are skipped")
    ap.add_argument("--report", default="", help="write per-case outcomes as JSON here")
    args = ap.parse_args()

    cases = load_cases()
    if args.only:
        want = set(args.only.split(","))
        cases = [c for c in cases if c[0] in want]
    if not cases:
        print(f"no cases found under {SUITE}", file=sys.stderr)
        return 2

    if args.materialize:
        for name, d, _expect in cases:
            dest = os.path.join(args.materialize, name)
            materialize(d, dest, args.challenge)
            print(f"materialized {name} -> {dest}")
        return 0

    if args.dry_run or not args.server:
        if not args.server and not args.dry_run:
            print("# no --server/ARENA_SERVER set; running --dry-run\n")
        return dry_run(cases)

    if not args.token:
        print("live run needs --token / ARENA_TOKEN", file=sys.stderr)
        return 2
    rc = live_run(cases, args.server, args.token, args.challenge, args.timeout, args.target)
    if args.report:
        with open(args.report, "w") as f:
            json.dump(OBSERVED, f, indent=1, sort_keys=True)
    return rc


if __name__ == "__main__":
    sys.exit(main())
