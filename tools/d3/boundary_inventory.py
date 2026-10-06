#!/usr/bin/env python3
"""Extract checkpoint-1 evidence from git objects, never from a dirty checkout.

This is research tooling, not the trusted specification or a conformance test.
Requires PyYAML (see requirements.txt). Unknown source syntax fails closed.
"""

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

import yaml

PIN = "44f7ae6cd7ef08bab604e20a473bf77e35d4c993"
PV = 86
CONFIG = "core/parameters/res/runtime_configs/"
VM = "runtime/near-vm-runner/src/"
SOURCES = [
    "Cargo.lock",
    "core/parameters/src/config_store.rs",
    "core/parameters/src/parameter_table.rs",
    "core/parameters/src/vm.rs",
    "core/primitives-core/src/version.rs",
    "core/primitives/src/receipt.rs",
    "core/primitives/src/action/mod.rs",
    VM + "features.rs", VM + "imports.rs", VM + "prepare.rs",
    VM + "prepare/prepare_v3.rs", VM + "prepare/instrument_v3.rs",
    VM + "wasmtime_runner/mod.rs", VM + "wasmtime_runner/logic.rs",
    VM + "wasmtime_runner/trap_classification.rs",
    VM + "logic/logic.rs", VM + "logic/gas_counter.rs", VM + "logic/errors.rs",
    "runtime/runtime/src/function_call.rs", "runtime/runtime/src/ext.rs",
    "runtime/runtime/src/lib.rs", "runtime/runtime/src/actions.rs",
    "runtime/runtime/src/receipt_manager.rs", "runtime/runtime/src/global_contracts.rs",
    "runtime/runtime/src/contract_code.rs",
]


class UniqueLoader(yaml.SafeLoader):
    pass


def unique_mapping(loader, node):
    result = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node)
        if key in result:
            raise ValueError(f"duplicate YAML key: {key}")
        result[key] = loader.construct_object(value_node)
    return result


UniqueLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, unique_mapping)


def yaml_map(source):
    value = yaml.load(source, Loader=UniqueLoader)
    if value is None:  # Some protocol revisions contain only comments.
        return {}
    if not isinstance(value, dict):
        raise ValueError("expected YAML mapping")
    return value


def extract_imports(source, params):
    body = source.split("\nimports! {\n", 1)[1].split("\n}", 1)[0]
    # Preserve newlines so each entry retains its source line.
    body = re.sub(r"//[^\n]*", "", body)
    entry = re.compile(
        r'\s*(?:#\[(?P<gate>\w+)\])?\s*'
        r'(?:#\[\["(?P<feature>\w+)"\]\])?\s*'
        r'(?:@in\s+(?P<module>\w+)\s*:)?\s*'
        r'(?:@as\s+(?P<alias>\w+)\s*:)?\s*'
        r'(?P<function>\w+)\s*<\[(?P<args>[^\]]*)\]\s*->\s*'
        r'\[(?P<returns>[^\]]*)\]\s*>,', re.MULTILINE,
    )
    result = []
    pos = 0
    while body[pos:].strip():
        match = entry.match(body, pos)
        if match is None:
            raise ValueError(f"unparsed import declaration: {body[pos:pos + 100]!r}")
        item = match.groupdict()
        gate, feature = item["gate"], item["feature"]
        if gate is not None and type(params.get(gate)) is not bool:
            raise ValueError(f"unresolved host gate: {gate}")
        if feature not in (None, "sandbox", "test_features"):
            raise ValueError(f"unreviewed build feature: {feature}")
        item["module"] = item["module"] or "env"
        item["name"] = item.pop("alias") or item["function"]
        item["args"] = " ".join(item["args"].split())
        item["returns"] = " ".join(item["returns"].split())
        item["enabled_in_production"] = feature is None and (gate is None or params[gate])
        item["source_line"] = source[:source.index("\nimports! {\n")].count("\n") + 3 + body[:match.start("function")].count("\n")
        result.append(item)
        pos = match.end()
    names = [(item["module"], item["name"]) for item in result]
    if not result or len(set(names)) != len(names):
        raise ValueError("missing or duplicate imports")
    return result


def inventory(nearcore):
    sources = {}

    def read(path):
        if path not in sources:
            sources[path] = subprocess.check_output(
                ["git", "-C", str(nearcore), "show", f"{PIN}:{path}"],
            )
        return sources[path].decode()

    for path in SOURCES:
        read(path)
    store = read("core/parameters/src/config_store.rs")
    diff_block = store.split("static CONFIG_DIFFS:", 1)[1].split("\n];", 1)[0]
    revisions = re.findall(r'\((\d+), include_config!\("(\d+\.yaml)"\)\)', diff_block)
    if len(revisions) != diff_block.count("include_config!"):
        raise ValueError("unparsed config revision")
    versions = [int(version) for version, _ in revisions]
    if versions != sorted(set(versions)):
        raise ValueError("config revisions not strictly increasing")
    params = yaml_map(read(CONFIG + "parameters.yaml"))
    applied = []
    for version, filename in revisions:
        if int(version) > PV:
            continue
        for key, diff in yaml_map(read(CONFIG + filename)).items():
            if not isinstance(diff, dict) or set(diff) - {"old", "new"}:
                raise ValueError(f"unknown diff syntax: {version}:{key}")
            if diff.get("old") != params.get(key):
                raise ValueError(f"old parameter differs: {version}:{key}")
            if "new" in diff:
                params[key] = diff["new"]
            else:
                params.pop(key)
        applied.append(int(version))
    imports = extract_imports(read(VM + "imports.rs"), params)
    constants = dict(re.findall(r"const (\w+): bool = (true|false);", read(VM + "features.rs")))
    if not constants:
        raise ValueError("missing WASM feature constants")
    return {
        "schema": "near-d3-boundary-inventory-v1",
        "nearcore_commit": PIN,
        "protocol_version": PV,
        "evidence": "source extraction only; no execution, differential testing, or Lean proof",
        "configuration": "mainnet base plus registered diffs <= 86; no genesis overrides; production features",
        "parameter_representation": "YAML values before nearcore typed conversion; monetary strings retained verbatim",
        "applied_config_versions": applied,
        "parameters": params,
        "feature_constants": {key: value == "true" for key, value in constants.items()},
        "imports": imports,
        "source_sha256": {path: hashlib.sha256(data).hexdigest() for path, data in sorted(sources.items())},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--nearcore", required=True, type=Path)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--output", type=Path)
    mode.add_argument("--check", type=Path)
    args = parser.parse_args()
    expected = json.dumps(inventory(args.nearcore), sort_keys=True, indent=2) + "\n"
    if args.check:
        if args.check.read_text() != expected:
            parser.exit(1, "D3 boundary inventory differs from pinned source; regenerate and review\n")
        print("D3 boundary inventory matches pinned source (research evidence only)")
    else:
        args.output.write_text(expected)
        print(f"Wrote {args.output}")


if __name__ == "__main__":
    main()
