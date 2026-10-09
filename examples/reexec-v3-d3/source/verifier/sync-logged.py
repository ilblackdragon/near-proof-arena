#!/usr/bin/env python3
"""Vendor candidate logging modules with reviewable runtime/proof separation.

The transform replaces the namespace literally, extracts specified unchanged
source ranges into runtime modules, and rewires imports. Declaration bodies and
proofs are preserved. The manifest records upstream and output hashes, extraction
ranges, and all import edits. --check regenerates everything without writing.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def separate_runtime(original):
    files = dict(original)
    operations = []
    def extract(name, target, spans, imports, namespace=None, opened=None):
        source = original[name]
        chunks = []
        ranges = []
        for begin, until in spans:
            a = source.index(begin)
            b = source.index(until, a)
            chunk = source[a:b]
            chunks.append(chunk)
            ranges.append({"start_line": source[:a].count("\n") + 1,
                           "end_line": source[:b].count("\n"),
                           "sha256": hashlib.sha256(chunk.encode()).hexdigest()})
            if files[name].count(chunk) != 1:
                raise ValueError(f"ambiguous extraction in {name}")
            files[name] = files[name].replace(chunk, "")
        body = "\n".join(chunks)
        if namespace:
            body = f"namespace {namespace}\n\nopen {opened}\n\n" + body + f"\nend {namespace}\n"
        files[target] = "".join(f"import {x}\n" for x in imports) + "\n" + body
        files[name] = f"import ReexecV3D3.Logged.{target.removesuffix('.lean').replace('/', '.')}\n" + files[name]
        operations.append({"source": name, "target": target, "ranges": ranges,
                           "imports": imports, "namespace": namespace, "open": opened})
    for name, dep, trusted in [
        ("D2Actions", "D2Queues", "NearSpecV3.D2.Actions"),
        ("D2Receipts", "Runtime.D2Actions", "NearSpecV3.D2.Receipts"),
        ("D2Runtime", "Runtime.D2Receipts", "NearSpecV3.D2.RuntimeD2"),
        ("D2Check", "Runtime.D2Runtime", "NearSpecV3.ChunkValidationD2"),
    ]:
        extract(name + ".lean", "Runtime/" + name + ".lean",
                [("namespace NearSpecV3.D2\n", "namespace ReexecV3D3.Logged\n")],
                ["ReexecV3D3.Logged." + dep, trusted])
    ns = "ReexecV3D3.Logged.W"
    opened = "NearSpecV3.Wasm NearSpecV3.Wasm.TTN"
    extract("WasmStep.lean", "Runtime/WasmStep.lean",
            [("/-- The host functions", "theorem callFunc_of_callPre")],
            ["NearSpecV3.Wasm.Exec"], ns, opened)
    extract("WasmHR.lean", "Runtime/Dr.lean",
            [("/-- The erased store record.", "theorem E_real'")],
            ["ReexecV3D3.Logged.WasmHostL"], ns, opened)
    extract("WasmRun.lean", "Runtime/WasmRun.lean", [
        ("def callHostL", "section\nvariable"),
        ("/-- The machine loop up", "def mapRU"),
        ("def entrySt", "theorem E_entrySt"),
        ("def enterRunL", "def mapEntry"),
        ("def afterStartL", "section\nvariable"),
    ], ["ReexecV3D3.Logged.Runtime.Dr"], ns, opened)
    extract("D3LSpec.lean", "Runtime/D3Check.lean",
            [("namespace NearSpecV3.D3\n", "namespace ReexecV3D3.Logged\n")],
            ["ReexecV3D3.Logged.D3L"])
    extract("API.lean", "Runtime/API.lean", [
        ("/-- `checkD3` and its recorded-storage", "theorem checkD3Reads_eq"),
        ("def checkD2Reads", "theorem checkD2Reads_eq"),
    ], ["ReexecV3D3.Logged.Runtime.D3Check"],
        "ReexecV3D3.Logged", "NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.D3")
    edits = {
        "WasmHostL.lean": [("ReexecV3D3.Logged.WasmStep", "ReexecV3D3.Logged.Runtime.WasmStep")],
        "D3L.lean": [("ReexecV3D3.Logged.D2Check", "ReexecV3D3.Logged.Runtime.D2Check"),
                     ("ReexecV3D3.Logged.WasmRun", "ReexecV3D3.Logged.Runtime.WasmRun")],
    }
    for name, replacements in edits.items():
        for old, new in replacements:
            files[name] = files[name].replace("import " + old + "\n", "import " + new + "\n")
            operations.append({"source": name, "import_old": old, "import_new": new})
    for dep in ["D2Check", "WasmRun"]:
        files["D3LSpec.lean"] = f"import ReexecV3D3.Logged.{dep}\n" + files["D3LSpec.lean"]
        operations.append({"source": "D3LSpec.lean", "added_proof_import": dep})
    return files, operations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("commit")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    repo = Path(__file__).resolve().parents[4]
    package = Path(__file__).resolve().parents[2]
    def git(*command):
        return subprocess.check_output(["git", "-C", str(repo), *command])
    commit = git("rev-parse", "--verify", args.commit + "^{commit}").decode().strip()
    prefix = "spec/lean/v3/NearSpecV3/Logged/"
    paths = git("ls-tree", "-r", "--name-only", commit, prefix).decode().splitlines()
    if not paths or not all(path.startswith(prefix) and path.endswith(".lean") for path in paths):
        raise ValueError("missing or unexpected upstream logging modules")
    destination = package / "formal/ReexecV3D3/Logged"
    manifest_path = package / "dependency-locks/logged-candidate.json"
    manifest = {"upstream_commit": commit, "role": "candidate code; not judge-trusted",
                "transform": {"old": "NearSpecV3.Logged", "new": "ReexecV3D3.Logged"},
                "files": []}
    sha = lambda value: hashlib.sha256(value).hexdigest()
    originals = {path.removeprefix(prefix): git("show", f"{commit}:{path}") for path in paths}
    transformed, operations = separate_runtime({name: source.decode().replace(
        "NearSpecV3.Logged", "ReexecV3D3.Logged") for name, source in originals.items()})
    manifest["transform"]["runtime_separation"] = operations
    manifest["upstream_files"] = [{"path": prefix + name, "sha256": sha(source)}
                                  for name, source in sorted(originals.items())]
    for name, value in sorted(transformed.items()):
        target = destination / name
        data = value.encode()
        manifest["files"].append({"candidate_path": str(target.relative_to(package)),
                                  "candidate_sha256": sha(data)})
        if args.check:
            if target.read_bytes() != data:
                raise ValueError(f"modified candidate copy: {target}")
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
    expected = {item["candidate_path"] for item in manifest["files"]}
    actual = {str(path.relative_to(package)) for path in destination.rglob("*.lean")}
    if actual != expected:
        raise ValueError("unexpected candidate logging modules")
    encoded = json.dumps(manifest, indent=2) + "\n"
    if args.check:
        if manifest_path.read_text() != encoded:
            raise ValueError("provenance manifest mismatch")
    else:
        manifest_path.write_text(encoded)
    print(f"{'verified' if args.check else 'copied'} {len(transformed)} candidate modules from {len(paths)} upstream modules at {commit}")


if __name__ == "__main__":
    main()
