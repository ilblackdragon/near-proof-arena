"""Minimal ``text/event-stream`` parser (WHATWG semantics, no ``retry``)."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Iterator, Optional


@dataclass(frozen=True)
class SseEvent:
    event: str
    data: str
    id: Optional[str] = None

    def json(self):
        import json

        return json.loads(self.data)


def parse_lines(lines: Iterable[str]) -> Iterator[SseEvent]:
    event = ""
    data: list[str] = []
    last_id: Optional[str] = None
    for raw in lines:
        line = raw[:-1] if raw.endswith("\r") else raw
        if line == "":
            if data or event:
                yield SseEvent(event or "message", "\n".join(data), last_id)
            event, data = "", []
            continue
        if line.startswith(":"):
            continue
        field, sep, value = line.partition(":")
        if sep and value.startswith(" "):
            value = value[1:]
        if field == "event":
            event = value
        elif field == "data":
            data.append(value)
        elif field == "id" and "\0" not in value:
            last_id = value
