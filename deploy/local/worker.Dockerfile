# syntax=docker/dockerfile:1
# Dev image for arena-worker (firecracker backend). Build context: repo root.
# The firecracker binary and guest images come from deploy/images/ (runners-vm lane).
FROM rust:1.96.0-bookworm@sha256:5e2214abe154fe26e39f64488952e5c991eeed1d6d6da7cc8381ae83927f0cfc AS build
WORKDIR /src
COPY . .
RUN --mount=type=cache,target=/usr/local/cargo/registry \
    --mount=type=cache,target=/src/target \
    cargo build --release --locked --bin arena-worker \
 && install -D -m 0755 target/release/arena-worker /out/arena-worker

FROM debian:bookworm-slim@sha256:3783cc01769c7b2b1b83a5c5ad96c815348e28ed7da68e2e3687004faa906251
RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates \
 && rm -rf /var/lib/apt/lists/*
COPY --from=build /out/arena-worker /usr/local/bin/arena-worker
COPY deploy/scripts/arena-guard /usr/local/bin/arena-guard
USER 10002:10002
# Refuse unsafe configurations before the worker starts.
ENTRYPOINT ["/bin/sh", "-c", "/usr/local/bin/arena-guard worker && exec /usr/local/bin/arena-worker \"$@\"", "arena-worker"]
