#!/usr/bin/env bash
# Maintainer step (not run by the judge): regenerate the protobuf code shipped
# in source/patches/sp1-prover-types/generated/ with the upstream build script
# logic (tonic-build 0.12.3). Requires protoc 29.3 at $PROTOC.
set -euo pipefail
: "${PROTOC:?set PROTOC to protoc 29.3}"
P="$(cd "$(dirname "$0")/../source/patches/sp1-prover-types" && pwd)"
T="$(mktemp -d)"
mkdir -p "$T/src"
cat > "$T/Cargo.toml" <<TOML
[package]
name = "regen"
version = "0.0.0"
edition = "2021"
[build-dependencies]
tonic-build = "=0.12.3"
[workspace]
TOML
cat > "$T/build.rs" <<RS
fn main() {
    tonic_build::configure()
        .protoc_arg("--experimental_allow_proto3_optional")
        .type_attribute(".", "#[derive(serde::Serialize,serde::Deserialize)]")
        .out_dir("$P/generated")
        .compile_protos(&["$P/proto/worker.proto", "$P/proto/cluster.proto"], &["$P/proto/", "/usr/include"])
        .unwrap();
}
RS
echo 'fn main() {}' > "$T/src/main.rs"
( cd "$T" && cargo build -q )
sha256sum "$P"/generated/*.rs
