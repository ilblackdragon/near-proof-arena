"""Fail-closed line-oriented process execution for differential harnesses."""
import concurrent.futures
import subprocess


def run_lines(command, inputs, expected=None):
    process = subprocess.run(command, input="\n".join(inputs) + ("\n" if inputs else ""),
                             capture_output=True, text=True, check=True)
    lines = process.stdout.splitlines()
    want = len(inputs) if expected is None else expected
    if len(lines) != want:
        raise ValueError(f"{command[0]} returned {len(lines)} lines; expected {want}")
    return lines


def run_shards(command, inputs, shards, counts=None):
    """Preserve input order; `counts` specifies output lines per input (e.g. chunks)."""
    if shards < 1:
        raise ValueError("shards must be positive")
    counts = [1] * len(inputs) if counts is None else counts
    if len(counts) != len(inputs) or any(n < 0 for n in counts):
        raise ValueError("invalid per-input output counts")
    def one(k):
        lines = run_lines(command, inputs[k::shards], sum(counts[k::shards]))
        out, pos = [], 0
        for index in range(k, len(inputs), shards):
            out.append((index, lines[pos:pos + counts[index]]))
            pos += counts[index]
        return out
    result = [None] * len(inputs)
    with concurrent.futures.ThreadPoolExecutor(max_workers=shards) as pool:
        for batch in pool.map(one, range(min(shards, len(inputs)))):
            for index, lines in batch:
                result[index] = lines
    return [line for group in result for line in group]
