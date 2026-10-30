# Corpus content gate on a provisioned runner (W01)

The `corpus-content-gates` job in `.github/workflows/ci.yml` re-walks the six pinned regression
corpora (d1run, d2corpus.v2, d3c7–d3c10: 235,716 cases, 8.5 GiB in ~707k files) and fails if any
family's case count, byte total or digest differs from the committed manifest
`docs/evidence/lean-chunk-L7/corpus-manifest.json`. GitHub-hosted runners do not have the corpora,
so the job runs only when the repository variable `NEAR_CORPORA_AVAILABLE` is `true`, on a
self-hosted runner labelled `near-corpora`. Without that variable GitHub reports the job as
**skipped**, never as passed.

The job is ready; it has not been run, because enabling it needs the owner actions below.

## Owner actions (not done by the lane)

1. **Register a self-hosted runner** (Settings → Actions → Runners → New self-hosted runner) on a
   Linux x86_64 host with ≥ 20 GB free disk, `python3` ≥ 3.11, and `rsync` (source mode) or `curl`
   + `zstd` (URL mode). Give it the extra label `near-corpora`. The host that holds the corpora
   today is the lane machine (`/data/illia/nearproof-deps/corpora`).
2. **Set repository variables** (Settings → Secrets and variables → Actions → Variables):

   | variable | value |
   |---|---|
   | `NEAR_CORPORA_AVAILABLE` | `true` |
   | `NEAR_CORPORA_DIR` | the runner-local corpora root, e.g. `/data/illia/nearproof-deps/corpora` |
   | `NEAR_CORPORA_SOURCE` | optional: an rsync source (path or `host:path`) holding the six families |
   | `NEAR_CORPORA_URL` | optional: base URL serving `<family>.tar.zst` and `SHA256SUMS` |

   With neither source set, the corpora must already be under `NEAR_CORPORA_DIR`.
3. **Re-record the manifest when a corpus is deliberately changed.** The 2026-10-27 cold re-judging
   of the 224 `d2corpus.v2/ood` cases (branch `worktree-agent-a103b9b4017fa3668`, commit
   `c8b2aeccd`) replaced those cases in place on the lane host. Until that commit and its updated
   manifest reach `main`, the gate on this host fails for `d2corpus.v2/ood` (that is the gate
   working, not a bug). Re-record with
   `python3 tools/d3/corpus_manifest.py --corpora "$NEAR_CORPORA_DIR" --out docs/evidence/lean-chunk-L7/corpus-manifest.json`
   only in the commit that changes the corpus.

## What the job does

1. `tools/d3/fetch_corpora.sh`: if all six families are under `NEAR_CORPORA_DIR`, verify in place;
   else rsync them from `NEAR_CORPORA_SOURCE`, or download `<family>.tar.zst` from
   `NEAR_CORPORA_URL`, check `SHA256SUMS` (transport only) and extract. In every mode the corpora
   are accepted only if `corpus_manifest.py --verify` reproduces the committed manifest (the trust
   anchor). Exit 2 = not configured, 1 = drift or fetch failure.
2. The W01 comparator self-tests (`tools/mainnet-replay/test_full_observables.py`,
   `test_failure_kinds.py`).

## Publishing tarballs (URL mode)

On the host that holds verified corpora:

```
cd "$NEAR_CORPORA_DIR"
for f in d1run d2corpus.v2 d3c7 d3c8 d3c9 d3c10; do tar -c "$f" | zstd -T8 -19 > "/srv/corpora/$f.tar.zst"; done
(cd /srv/corpora && sha256sum *.tar.zst > SHA256SUMS)
```

## Local dry run

```
NEAR_CORPORA_DIR=/data/illia/nearproof-deps/corpora bash tools/d3/fetch_corpora.sh   # verify in place
env -u NEAR_CORPORA_DIR bash tools/d3/fetch_corpora.sh; echo $?                      # 2: not configured
```
