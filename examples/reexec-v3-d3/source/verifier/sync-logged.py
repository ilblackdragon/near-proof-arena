#!/usr/bin/env python3
"""Vendor proved logging modules as candidate code, with a namespace-only transform.

Usage: sync-logged.py COMMIT [--check]
This never changes the challenge's trusted set or its frozen vendor. Every byte
change is the literal replacement NearSpecV3.Logged -> ReexecV3D3.Logged (imports,
namespaces and qualified references). The manifest records both source and
transformed digests, plus the full upstream commit. --check is read-only.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


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
    for path in paths:
        source = git("show", f"{commit}:{path}")
        transformed = source.replace(b"NearSpecV3.Logged", b"ReexecV3D3.Logged")
        target = destination / path.removeprefix(prefix)
        manifest["files"].append({"upstream_path": path,
                                  "candidate_path": str(target.relative_to(package)),
                                  "upstream_sha256": sha(source), "candidate_sha256": sha(transformed)})
        if args.check:
            if target.read_bytes() != transformed:
                raise ValueError(f"modified candidate copy: {target}")
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(transformed)
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
    print(f"{'verified' if args.check else 'copied'} {len(paths)} candidate modules from {commit}")


if __name__ == "__main__":
    main()
