# upgrade-monitor

Semantic-impact report for moving a challenge from one nearcore ref to another.

```sh
cargo build -p upgrade-monitor
target/debug/upgrade-monitor \
  --repo /data/illia/nearproof-deps/nearcore-upgrade-monitor \  # any nearcore clone containing both refs
  --old 2.13.4 --new <newer-ref> \
  --impact-map spec/impact-map.toml \
  --json report.json --markdown report.md
```

Exit codes: **0** `NO_SEMANTIC_CHANGE_DETECTED`, **3** `REVALIDATION_REQUIRED`,
**2** error (must be treated as `REVALIDATION_REQUIRED`).

What it does (the repository is never modified; trees are extracted with
`git archive` into a scratch dir):

1. `cargo metadata --no-deps --offline` on both trees; closure of the root
   crates (default: `node-runtime, near-vm-runner, near-primitives,
   near-primitives-core, near-store, near-parameters, near-crypto`) over
   normal + build + *optional* path dependencies (dev-deps excluded). The
   closure is the union of the old and new closures.
2. Literal `include_str!`/`include_bytes!` targets outside a closure crate's
   directory are added to the closure.
3. `git diff --name-status -M` → each changed path (and rename source) is
   attributed to its owning crate by longest directory prefix. Workspace
   `Cargo.toml`, `Cargo.lock`, `rust-toolchain*`, `.cargo/**` count as build
   configuration changes.
4. External crates: `Cargo.lock` walked from the closure crates' non-dev
   external dependencies; any version difference is reported.
5. `core/parameters/res/runtime_configs/*` changes with a diff excerpt.
6. `core/primitives-core/src/version.rs`: stable/nightly/min-supported
   versions, `ProtocolFeature` variants and their versions (added, removed,
   re-versioned, renamed to `_Deprecated*`, newly enabled at stable);
   `DB_VERSION` constants. Unparseable ⇒ treated as changed.
7. `ProtocolFeature::*` references added/removed in changed closure sources.
8. Paths containing `migration`.
9. Mapping of every changed closure input to spec definitions, obligations
   and fixtures through the governed `spec/impact-map.toml`; inputs matching
   no rule get the maximal `[default]` target.

The verdict is `REVALIDATION_REQUIRED` whenever anything in 1–6 changed —
**even if the old Lean proofs still compile**. A change outside the closure
(e.g. chain/, network/, neard/) is reported but does not by itself trigger
revalidation.

Limitations (honest list):

* `build.rs` scripts reading arbitrary files, `include!` with non-literal
  paths (`concat!(env!("OUT_DIR"), …)`), and proc-macros reading files are
  not traced. Generated code is attributed only via its generating crate.
* Feature flags are over-approximated (all optional deps included); the
  closure is therefore larger than what a particular `neard` build uses.
* The version.rs parser is lexical; a refactor of that file produces parse
  issues, which fail closed but need a human to update the parser.
* The impact map is only as good as its rules; the initial version uses
  `concept:` placeholders until the spec lane names exact Lean declarations.
