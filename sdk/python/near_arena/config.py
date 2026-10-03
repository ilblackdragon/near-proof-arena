"""Same configuration rules as the ``arena`` CLI.

``ARENA_URL`` (default ``http://127.0.0.1:8471``) and ``ARENA_TOKEN`` win over
``$ARENA_CONFIG`` or ``$XDG_CONFIG_HOME/arena/config.toml`` or
``~/.config/arena/config.toml`` (keys ``url`` and ``token``).
"""
from __future__ import annotations

import os
import tomllib
from pathlib import Path
from typing import Optional, Tuple

DEFAULT_URL = "http://127.0.0.1:8471"


def config_path() -> Optional[Path]:
    if os.environ.get("ARENA_CONFIG"):
        return Path(os.environ["ARENA_CONFIG"])
    if os.environ.get("XDG_CONFIG_HOME"):
        return Path(os.environ["XDG_CONFIG_HOME"]) / "arena" / "config.toml"
    home = os.environ.get("HOME")
    return Path(home) / ".config" / "arena" / "config.toml" if home else None


def load() -> Tuple[str, Optional[str]]:
    file: dict = {}
    p = config_path()
    if p is not None and p.exists():
        file = tomllib.loads(p.read_text())
    url = os.environ.get("ARENA_URL") or file.get("url") or DEFAULT_URL
    token = os.environ.get("ARENA_TOKEN") or file.get("token")
    return url.rstrip("/"), token
