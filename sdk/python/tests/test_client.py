import hashlib
import json
import subprocess
import sys
from pathlib import Path

import httpx
import pytest

from near_arena import (
    ArenaClient,
    AuthError,
    NotFoundError,
    RejectedError,
    UnavailableError,
    default_idempotency_key,
    package_digest,
    parse_lines,
)

CHL = "chl_0123456789abcdef0123456789abcdef"
HERE = Path(__file__).resolve().parent


def view(stage="RECEIVED", decision=None, **extra):
    v = {
        "id": "sub_1", "challenge_id": CHL, "agent": "a", "candidate_name": "toy",
        "backend_family": "toy", "parent": None, "tier": "formal",
        "package_digest": "sha256:" + "0" * 64, "stage": stage, "decision": decision,
        "accepted": None if decision is None else decision == "ADMITTED",
        "score_milli": None, "change_class": None, "gates": [], "reason_codes": [],
        "benchmark": None, "evidence_graph": None, "revoked": None,
        "created_at": "t", "updated_at": "t",
    }
    v.update(extra)
    return v


@pytest.fixture(autouse=True)
def no_config(monkeypatch, tmp_path):
    monkeypatch.setenv("ARENA_CONFIG", str(tmp_path / "none.toml"))
    monkeypatch.delenv("ARENA_URL", raising=False)
    monkeypatch.delenv("ARENA_TOKEN", raising=False)


def client(handler, token="tok"):
    return ArenaClient("http://arena.test", token, transport=httpx.MockTransport(handler))


def test_submit_archive_flow():
    seen = []
    data = b"tar-bytes"

    def h(req: httpx.Request):
        seen.append(req)
        assert req.headers["authorization"] == "Bearer tok"
        if req.url.path == "/v1/uploads":
            assert req.headers["content-type"] == "application/x-tar"
            return httpx.Response(200, json={"upload_id": "u1", "digest": package_digest(req.content)})
        if req.url.path == "/v1/submissions":
            return httpx.Response(201, json=view(extra_field=1))
        return httpx.Response(404)

    with client(h) as c:
        sub = c.submit_archive(CHL, data, parent="sub_0")
    assert sub["id"] == "sub_1" and sub["extra_field"] == 1  # verbatim
    body = json.loads(seen[1].content)
    assert body == {
        "challenge_id": CHL,
        "upload_digest": "sha256:" + hashlib.sha256(data).hexdigest(),
        "idempotency_key": default_idempotency_key(CHL, package_digest(data), "sub_0"),
        "parent": "sub_0",
    }


def test_idempotency_key_matches_cli_derivation():
    # Must stay identical to sdk/arena-cli/src/main.rs (submit).
    d = "sha256:" + "a" * 64
    expect = "arena-cli-" + hashlib.sha256(f"{CHL}\n{d}\n".encode()).hexdigest()[:32]
    assert default_idempotency_key(CHL, d, None) == expect


def test_upload_digest_mismatch():
    def h(req):
        return httpx.Response(200, json={"upload_id": "u1", "digest": "sha256:" + "f" * 64})

    with client(h) as c, pytest.raises(UnavailableError):
        c.upload(b"x")


@pytest.mark.parametrize(
    "status,exc", [(401, AuthError), (403, AuthError), (404, NotFoundError), (422, RejectedError), (409, RejectedError), (503, UnavailableError), (429, UnavailableError)]
)
def test_error_mapping(status, exc):
    with client(lambda req: httpx.Response(status, text="nope")) as c, pytest.raises(exc) as ei:
        c.submission("sub_1")
    assert ei.value.status == status


def test_transport_error():
    def h(req):
        raise httpx.ConnectError("refused", request=req)

    with client(h) as c, pytest.raises(UnavailableError):
        c.challenges()


def test_invalid_ids_rejected_locally():
    with client(lambda req: httpx.Response(500)) as c:
        with pytest.raises(ValueError):
            c.submission("../admin")
        with pytest.raises(ValueError):
            c.leaderboard("sub_1")


def test_lists_accept_bare_or_wrapped():
    entry = {"rank": 1, "submission_id": "sub_1"}

    def h(req):
        if req.url.path.startswith("/v1/leaderboards/"):
            return httpx.Response(200, json={"entries": [entry]})
        if req.url.path == "/v1/challenges":
            return httpx.Response(200, json=[{"id": CHL}])
        if req.url.path == "/v1/submissions":
            assert req.url.params["challenge_id"] == CHL
            return httpx.Response(200, json=[view()])
        return httpx.Response(404)

    with client(h, token=None) as c:
        assert c.leaderboard(CHL) == [entry]
        assert c.challenges() == [{"id": CHL}]
        assert c.submissions(challenge_id=CHL)[0]["id"] == "sub_1"


def test_sse_parser():
    lines = [": comment", "event: stage", "id: 7", "data: {\"a\":", "data: 1}", "", "data: x", "", ""]
    evs = list(parse_lines(lines))
    assert [e.event for e in evs] == ["stage", "message"]
    assert evs[0].json() == {"a": 1} and evs[0].id == "7" and evs[1].id == "7"


def test_events_stream():
    def h(req):
        assert req.headers["accept"] == "text/event-stream"
        assert req.headers["last-event-id"] == "3"
        return httpx.Response(200, headers={"content-type": "text/event-stream"}, content=b"event: stage\ndata: {}\nid: 4\n\n")

    with client(h) as c:
        evs = list(c.events("sub_1", last_event_id="3"))
    assert len(evs) == 1 and evs[0].event == "stage" and evs[0].id == "4"


def test_watch_until_decided():
    state = {"n": 0}

    def h(req):
        if req.url.path.endswith("/events"):
            return httpx.Response(200, content=b"data: a\n\ndata: b\n\n")
        state["n"] += 1
        if state["n"] == 1:
            return httpx.Response(200, json=view("VALIDATED"))
        if state["n"] == 2:
            return httpx.Response(200, json=view("BUILT"))
        return httpx.Response(200, json=view("DECIDED", "REJECTED", reason_codes=["CLAIM_MISMATCH"]))

    with client(h) as c:
        stages = [v["stage"] for v in c.watch("sub_1")]
    assert stages == ["VALIDATED", "BUILT", "DECIDED"]


def test_watch_falls_back_to_polling(monkeypatch):
    monkeypatch.setattr("time.sleep", lambda s: None)
    state = {"n": 0}

    def h(req):
        if req.url.path.endswith("/events"):
            return httpx.Response(404)
        state["n"] += 1
        return httpx.Response(200, json=view("DECIDED", "ADMITTED") if state["n"] > 4 else view("BUILT"))

    with client(h) as c:
        assert c.wait("sub_1")["decision"] == "ADMITTED"


def test_config_file(tmp_path, monkeypatch):
    cfg = tmp_path / "c.toml"
    cfg.write_text('url = "http://from-file:1/"\ntoken = "ft"\n')
    monkeypatch.setenv("ARENA_CONFIG", str(cfg))
    c = ArenaClient(transport=httpx.MockTransport(lambda r: httpx.Response(200, json=[])))
    assert c.base_url == "http://from-file:1" and c.token == "ft"
    monkeypatch.setenv("ARENA_TOKEN", "envtok")
    assert ArenaClient().token == "envtok"


def test_generated_types_up_to_date():
    r = subprocess.run([sys.executable, str(HERE.parent / "scripts" / "gen_types.py"), "--check"])
    assert r.returncode == 0, "near_arena/types.py is stale; run scripts/gen_types.py"


def test_types_cover_contract():
    from near_arena import types as t

    assert "SubmissionView" in t.__all__ and "LeaderboardEntry" in t.__all__
    assert set(t.SubmissionView.__annotations__) >= {"id", "stage", "decision", "accepted", "gates", "score_milli"}
    assert "HOSTILE_PROOF_ACCEPTED" in t.ReasonCode.__args__


def test_zstd_upload_content_type():
    data = b"\x28\xb5\x2f\xfd" + b"frame"

    def h(req):
        assert req.headers["content-type"] == "application/zstd"
        return httpx.Response(200, json={"upload_id": "u", "digest": package_digest(req.content)})

    with client(h) as c:
        assert c.upload(data)["digest"] == package_digest(data)
