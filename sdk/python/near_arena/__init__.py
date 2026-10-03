"""Python client for NEAR Proof Arena.

>>> from near_arena import ArenaClient
>>> with ArenaClient() as c:                       # ARENA_URL / ARENA_TOKEN
...     sub = c.submit_archive("chl_...", open("pkg.tar", "rb").read())
...     final = c.wait(sub["id"])
...     print(final["decision"], final["score_milli"])

Build packages with ``arena pack`` and validate them with
``arena check-local`` (LOCAL CHECK — NOT AN OFFICIAL VERDICT).
"""
from . import types
from .client import DECISIONS, ArenaClient, UploadResult, default_idempotency_key, package_digest
from .errors import ArenaError, AuthError, NotFoundError, RejectedError, UnavailableError
from .sse import SseEvent, parse_lines

__all__ = [
    "ArenaClient",
    "ArenaError",
    "AuthError",
    "DECISIONS",
    "NotFoundError",
    "RejectedError",
    "SseEvent",
    "UnavailableError",
    "UploadResult",
    "default_idempotency_key",
    "package_digest",
    "parse_lines",
    "types",
]
__version__ = "0.1.0"
