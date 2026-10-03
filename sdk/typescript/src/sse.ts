/** One Server-Sent Event. */
export interface SseEvent {
  event: string;
  data: string;
  id?: string;
}

/** Incremental `text/event-stream` parser (WHATWG semantics, no `retry`). */
export class SseParser {
  #event = "";
  #data: string[] = [];
  #id: string | undefined;
  #buf = "";

  /** Feed a decoded text chunk; returns the events completed by it. */
  push(chunk: string): SseEvent[] {
    this.#buf += chunk;
    const out: SseEvent[] = [];
    let nl: number;
    while ((nl = this.#buf.search(/\r\n|\n|\r/)) >= 0) {
      const sepLen = this.#buf.startsWith("\r\n", nl) ? 2 : 1;
      // A lone trailing "\r" may be the first half of "\r\n": wait for more.
      if (sepLen === 1 && this.#buf[nl] === "\r" && nl === this.#buf.length - 1) break;
      const line = this.#buf.slice(0, nl);
      this.#buf = this.#buf.slice(nl + sepLen);
      const ev = this.line(line);
      if (ev) out.push(ev);
    }
    return out;
  }

  /** Process one line (without terminator). */
  line(line: string): SseEvent | undefined {
    if (line === "") {
      if (this.#data.length === 0 && this.#event === "") return undefined;
      const ev: SseEvent = { event: this.#event || "message", data: this.#data.join("\n") };
      if (this.#id !== undefined) ev.id = this.#id;
      this.#event = "";
      this.#data = [];
      return ev;
    }
    if (line.startsWith(":")) return undefined;
    const i = line.indexOf(":");
    const field = i < 0 ? line : line.slice(0, i);
    let value = i < 0 ? "" : line.slice(i + 1);
    if (value.startsWith(" ")) value = value.slice(1);
    if (field === "event") this.#event = value;
    else if (field === "data") this.#data.push(value);
    else if (field === "id" && !value.includes("\0")) this.#id = value;
    return undefined;
  }
}

/** Parse an SSE byte stream (e.g. `response.body` of `fetch`). */
export async function* parseSseStream(body: ReadableStream<Uint8Array>): AsyncGenerator<SseEvent> {
  const parser = new SseParser();
  const decoder = new TextDecoder();
  const reader = body.getReader();
  try {
    for (;;) {
      const { done, value } = await reader.read();
      if (done) break;
      yield* parser.push(decoder.decode(value, { stream: true }));
    }
    yield* parser.push(decoder.decode() + "\n\n");
  } finally {
    reader.releaseLock();
  }
}
