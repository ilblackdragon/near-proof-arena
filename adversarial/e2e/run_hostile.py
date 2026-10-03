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


def build_package_bytes(case_dir, expect, challenge_id):
    """Return the raw archive bytes to upload for a case.

    Archive-attack cases run make-archive.sh (the hostile payload IS the archive
    encoding). All other cases are tarred from the directory, with the
    challenge id substituted into candidate.toml and the generator/helper files
    excluded.
    """
    mk = os.path.join(case_dir, "make-archive.sh")
    if os.path.exists(mk):
        out = subprocess.run(["sh", mk], cwd=case_dir, capture_output=True)
        if out.returncode != 0:
            raise RuntimeError(f"make-archive.sh failed: {out.stderr.decode(errors='replace')}")
        return out.stdout

    buf = io.BytesIO()
    exclude = {"expect.json", "make-archive.sh", "archive-kind", "README.md"}
    with tarfile.open(fileobj=buf, mode="w") as tar:
        for root, _dirs, filenames in os.walk(case_dir):
            for fn in filenames:
                full = os.path.join(root, fn)
                rel = os.path.relpath(full, case_dir)
                top = rel.split(os.sep)[0]
                if top in exclude:
                    continue
                data = open(full, "rb").read()
                if rel == "candidate.toml" and challenge_id:
                    data = re.sub(rb'challenge = "[^"]*"',
                                  f'challenge = "{challenge_id}"'.encode(), data)
                ti = tarfile.TarInfo(name=rel)
                ti.size = len(data)
                ti.mode = 0o755 if rel.endswith(".sh") else 0o644
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

    # --- leaderboard must not list this submission ---
    lb, lb_raw = client.leaderboard(challenge_id)
    if lb_raw and sid.encode() in lb_raw:
        return False, [f"{name}: hostile submission appears on the leaderboard!"]

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


def live_run(cases, server, token, challenge_id, timeout_s):
    client = Client(server, token)
    if not challenge_id:
        chs = client.challenges()
        if not chs:
            print("no challenges on server; set ARENA_CHALLENGE", file=sys.stderr)
            return 2
        challenge_id = chs[0]["id"] if isinstance(chs[0], dict) else chs[0]
    print(f"# LIVE e2e against {server}, challenge {challenge_id}\n")

    fails = 0
    for name, d, expect in cases:
        try:
            ok, msgs = check_case(client, name, d, expect, challenge_id, timeout_s)
        except Exception as e:  # noqa: BLE001
            ok, msgs = False, [f"{name}: driver error: {e}"]
        for m in msgs:
            print(("ok   " if ok else "FAIL ") + m)
        if not ok:
            fails += 1
    print()
    if fails:
        print(f"E2E FAILED: {fails}/{len(cases)} hostile cases did not behave as expected")
        return 1
    print(f"E2E OK: all {len(cases)} hostile cases REJECTED with the expected gates/reasons; "
          "none admitted or ranked; injection payloads sanitized")
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--server", default=os.environ.get("ARENA_SERVER"))
    ap.add_argument("--token", default=os.environ.get("ARENA_TOKEN"))
    ap.add_argument("--challenge", default=os.environ.get("ARENA_CHALLENGE"))
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--timeout", type=int, default=600)
    args = ap.parse_args()

    cases = load_cases()
    if not cases:
        print(f"no cases found under {SUITE}", file=sys.stderr)
        return 2

    if args.dry_run or not args.server:
        if not args.server and not args.dry_run:
            print("# no --server/ARENA_SERVER set; running --dry-run\n")
        return dry_run(cases)

    if not args.token:
        print("live run needs --token / ARENA_TOKEN", file=sys.stderr)
        return 2
    return live_run(cases, args.server, args.token, args.challenge, args.timeout)


if __name__ == "__main__":
    sys.exit(main())
