"""Synchronous client for the NEAR Proof Arena API v1 (docs/CONTRACTS.md §10).

Responses are returned as the server's JSON objects (typed as the generated
TypedDicts in :mod:`near_arena.types`), never re-shaped.
"""
from __future__ import annotations

import hashlib
import re
import time
from typing import Any, Iterator, List, Optional, TypedDict, cast

import httpx

from . import config
from .errors import ArenaError, UnavailableError, for_status
from .sse import SseEvent, parse_lines
from .types import ChallengeDefinition, LeaderboardEntry, SubmissionView

_ID = re.compile(r"^[A-Za-z0-9_-]{1,128}$")

#: Terminal decisions. ``decision`` is ``None`` while a submission is pending.
DECISIONS = ("ADMITTED", "REJECTED", "INCONCLUSIVE", "INFRA_ERROR", "CANCELLED")


class UploadResult(TypedDict):
    upload_id: str
    digest: str


def _check_id(value: str, prefix: str) -> str:
    if not value.startswith(prefix) or not _ID.match(value):
        raise ValueError(f"invalid id {value!r} (expected {prefix}...)")
    return value


def package_digest(data: bytes) -> str:
    """``sha256:<hex>`` of the exact uploaded bytes (the ``upload_digest``)."""
    return "sha256:" + hashlib.sha256(data).hexdigest()


def default_idempotency_key(challenge_id: str, digest: str, parent: Optional[str]) -> str:
    """Same derivation as the CLI: identical retries never duplicate a submission."""
    h = f"{challenge_id}\n{digest}\n{parent or ''}".encode()
    return "arena-cli-" + hashlib.sha256(h).hexdigest()[:32]


def _list(v: Any, *keys: str) -> list:
    if isinstance(v, list):
        return v
    if isinstance(v, dict):
        for k in keys:
            if isinstance(v.get(k), list):
                return v[k]
    return []


class ArenaClient:
    """Blocking client. Use as a context manager or call :meth:`close`.

    ``base_url``/``token`` default to the CLI configuration
    (``ARENA_URL``, ``ARENA_TOKEN``, ``~/.config/arena/config.toml``).
    Pass ``transport`` (e.g. ``httpx.MockTransport``) for testing.
    """

    def __init__(
        self,
        base_url: Optional[str] = None,
        token: Optional[str] = None,
        *,
        timeout: float = 600.0,
        transport: Optional[httpx.BaseTransport] = None,
    ) -> None:
        cfg_url, cfg_token = config.load()
        self.base_url = (base_url or cfg_url).rstrip("/")
        self.token = token if token is not None else cfg_token
        headers = {"User-Agent": "near-arena-python/0.1.0"}
        if self.token:
            headers["Authorization"] = f"Bearer {self.token}"
        self._http = httpx.Client(
            base_url=self.base_url,
            headers=headers,
            timeout=httpx.Timeout(timeout, connect=15.0),
            transport=transport,
        )

    def __enter__(self) -> "ArenaClient":
        return self

    def __exit__(self, *exc: object) -> None:
        self.close()

    def close(self) -> None:
        self._http.close()

    # ------------------------------------------------------------ plumbing
    def _request(self, method: str, path: str, **kw: Any) -> httpx.Response:
        try:
            r = self._http.request(method, path, **kw)
        except httpx.TransportError as e:
            raise UnavailableError(f"cannot reach arena server: {e}") from e
        if r.status_code >= 400:
            raise for_status(r.status_code, r.text)
        return r

    def _json(self, method: str, path: str, **kw: Any) -> Any:
        r = self._request(method, path, **kw)
        try:
            return r.json()
        except ValueError as e:
            raise UnavailableError(f"server sent invalid JSON: {e}", r.status_code, r.text) from e

    # ---------------------------------------------------------- endpoints
    def challenges(self) -> List[Any]:
        """``GET /v1/challenges`` (list as returned by the server)."""
        return _list(self._json("GET", "/v1/challenges"), "challenges")

    def challenge(self, challenge_id: str) -> Any:
        """``GET /v1/challenges/{id}``; a ``ChallengeDefinition`` or ``{id, definition}``."""
        return self._json("GET", f"/v1/challenges/{_check_id(challenge_id, 'chl_')}")

    def challenge_definition(self, challenge_id: str) -> ChallengeDefinition:
        v = self.challenge(challenge_id)
        return cast(ChallengeDefinition, v.get("definition", v) if isinstance(v, dict) else v)

    def upload(self, data: bytes) -> UploadResult:
        """``POST /v1/uploads`` with the raw package archive (tar or tar.zst)."""
        res = self._json("POST", "/v1/uploads", content=data, headers={"Content-Type": "application/x-tar"})
        if res.get("digest") != package_digest(data):
            raise UnavailableError(f"server reported digest {res.get('digest')!r}, expected {package_digest(data)}")
        return cast(UploadResult, res)

    def create_submission(
        self,
        challenge_id: str,
        upload_digest: str,
        idempotency_key: str,
        parent: Optional[str] = None,
    ) -> SubmissionView:
        """``POST /v1/submissions``."""
        body: dict = {
            "challenge_id": _check_id(challenge_id, "chl_"),
            "upload_digest": upload_digest,
            "idempotency_key": idempotency_key,
        }
        if parent is not None:
            body["parent"] = _check_id(parent, "sub_")
        return cast(SubmissionView, self._json("POST", "/v1/submissions", json=body))

    def submit_archive(
        self,
        challenge_id: str,
        data: bytes,
        *,
        parent: Optional[str] = None,
        idempotency_key: Optional[str] = None,
    ) -> SubmissionView:
        """Upload ``data`` (e.g. from ``arena pack``) and create a submission."""
        up = self.upload(data)
        key = idempotency_key or default_idempotency_key(challenge_id, up["digest"], parent)
        return self.create_submission(challenge_id, up["digest"], key, parent)

    def submission(self, submission_id: str) -> SubmissionView:
        return cast(SubmissionView, self._json("GET", f"/v1/submissions/{_check_id(submission_id, 'sub_')}"))

    def submissions(self, challenge_id: Optional[str] = None, agent: Optional[str] = None) -> List[SubmissionView]:
        params = {k: v for k, v in (("challenge_id", challenge_id), ("agent", agent)) if v}
        return cast(List[SubmissionView], _list(self._json("GET", "/v1/submissions", params=params), "submissions"))

    def report(self, submission_id: str) -> Any:
        """Signed JSON report (``GET /v1/submissions/{id}/report``)."""
        return self._json("GET", f"/v1/submissions/{_check_id(submission_id, 'sub_')}/report")

    def cancel(self, submission_id: str) -> Any:
        return self._json("POST", f"/v1/submissions/{_check_id(submission_id, 'sub_')}/cancel", json={})

    def leaderboard(self, challenge_id: str) -> List[LeaderboardEntry]:
        v = self._json("GET", f"/v1/leaderboards/{_check_id(challenge_id, 'chl_')}")
        return cast(List[LeaderboardEntry], _list(v, "entries", "leaderboard"))

    # ---------------------------------------------------------------- SSE
    def events(self, submission_id: str, last_event_id: Optional[str] = None) -> Iterator[SseEvent]:
        """Iterate Server-Sent Events of a submission until the server closes the stream."""
        path = f"/v1/submissions/{_check_id(submission_id, 'sub_')}/events"
        headers = {"Accept": "text/event-stream"}
        if last_event_id:
            headers["Last-Event-ID"] = last_event_id
        try:
            with self._http.stream("GET", path, headers=headers, timeout=httpx.Timeout(None, connect=15.0)) as r:
                if r.status_code >= 400:
                    r.read()
                    raise for_status(r.status_code, r.text)
                yield from parse_lines(r.iter_lines())
        except httpx.TransportError as e:
            raise UnavailableError(f"event stream: {e}") from e

    def watch(
        self,
        submission_id: str,
        *,
        timeout: Optional[float] = None,
        poll_interval: float = 2.0,
    ) -> Iterator[SubmissionView]:
        """Yield the authoritative ``SubmissionView`` whenever it changes, ending
        with the decided view. Uses SSE as a change signal and falls back to
        polling if the stream is unavailable."""
        start = time.monotonic()
        last: Any = None
        last_id: Optional[str] = None
        sse_failures = 0

        def expired() -> bool:
            return timeout is not None and time.monotonic() - start > timeout

        while True:
            view = self.submission(submission_id)
            if view != last:
                last = view
                yield view
            if view.get("decision") is not None:
                return
            if expired():
                raise UnavailableError(f"timed out waiting for {submission_id}")
            if sse_failures < 3:
                try:
                    for ev in self.events(submission_id, last_id):
                        last_id = ev.id or last_id
                        view = self.submission(submission_id)
                        if view != last:
                            last = view
                            yield view
                        if view.get("decision") is not None:
                            return
                        if expired():
                            raise UnavailableError(f"timed out waiting for {submission_id}")
                except UnavailableError:
                    if expired():
                        raise
                    sse_failures += 1
                except ArenaError as e:
                    if e.exit_code == 4:
                        raise
                    sse_failures += 1
            time.sleep(poll_interval if sse_failures >= 3 else 0.3)

    def wait(self, submission_id: str, *, timeout: Optional[float] = None) -> SubmissionView:
        """Block until decided; return the final ``SubmissionView``."""
        view: Optional[SubmissionView] = None
        for view in self.watch(submission_id, timeout=timeout):
            pass
        assert view is not None
        return view
