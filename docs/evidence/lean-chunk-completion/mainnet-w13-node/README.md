# Mainnet capture-node launch evidence

Checkpoint: 2026-10-24 UTC. This records a real mainnet node launch, not completed
acquisition or a replay pass. `build.json` pins the binary, patch and launcher;
`setup.json` records live network/config provenance; `launch-status.json` is only
a snapshot. Runtime live status is
`/data/illia/nearproof-deps/mainnet-w13/home/capture-status.json`.

Service: `systemctl --user status nearproof-mainnet-w13.service`.
Stop: `systemctl --user stop nearproof-mainnet-w13.service`.
RPC: `http://127.0.0.1:3038/status`.
Exports: `/data/illia/nearproof-deps/mainnet-w13/exports/`.

Release build with pinned Rust 1.93.0 passed. Python syntax checks and a bounded
supervisor exercise (capture target, verdict counts, child shutdown) passed.
The node connected to 12 peers and completed epoch sync; headers/state sync still
precede execution and witness export. No node keys or database are committed.
