"""Exception hierarchy. Mirrors the `arena` CLI exit codes (docs/AGENT_CONTRACT.md §9)."""
from __future__ import annotations


class ArenaError(Exception):
    """Base class. ``status`` is the HTTP status (``None`` for transport errors)."""

    exit_code = 1

    def __init__(self, message: str, status: int | None = None, body: str = "") -> None:
        super().__init__(message)
        self.status = status
        self.body = body


class AuthError(ArenaError):
    """Missing/invalid token (HTTP 401/403). CLI exit 4."""

    exit_code = 4


class UnavailableError(ArenaError):
    """Unreachable server, timeout, HTTP 5xx/429. Retry with the same idempotency key. CLI exit 5."""

    exit_code = 5


class RejectedError(ArenaError):
    """Server rejected the request (HTTP 400/409/413/422, other 4xx). CLI exit 6."""

    exit_code = 6


class NotFoundError(ArenaError):
    """HTTP 404. CLI exit 7."""

    exit_code = 7


def for_status(status: int, body: str) -> ArenaError:
    msg = f"HTTP {status}: {body[:2000]}"
    if status in (401, 403):
        return AuthError(msg, status, body)
    if status == 404:
        return NotFoundError(msg, status, body)
    if status == 429 or status >= 500:
        return UnavailableError(msg, status, body)
    return RejectedError(msg, status, body)
