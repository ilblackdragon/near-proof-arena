#!/usr/bin/env python3
"""Materialize the permanent hostile-submission suite.

Each case is a COMPLETE candidate package (candidate.toml, source/, formal/,
build-recipe/build.sh, README.md, dependency-locks/) plus expect.json. Most
cases are the DEMO toy-arithmetic reference candidate, honest in every respect
EXCEPT the one attacked behaviour, so the attacked gate is the FIRST gate to
fail (not PROVER_RELIABILITY because the prover was broken for an unrelated
reason). This is what the live e2e requires: `tests/e2e/run.sh --hostile`
against the demo challenge `chl_54c6…`.

`expect.json` carries `targets` and `runnable`:

* `targets` ⊆ {"demo","near-formal"}: which challenge a case is meaningful on.
  Formal / artifact-binding / crypto obligations only exist on the NEAR formal
  challenge, so those cases are `["near-formal"]` and are SKIPPED by the demo
  run (and vice-versa).
* `runnable`: false for the generic Lean-certificate stubs. They DOCUMENT an
  attack but cannot execute on the NEAR challenge without a real
  reexec-witness backend to build; the executable NEAR kills are the
  reexec-witness-derived cases `near-reexec-*` (verified in Milestone D). The
  driver skips `runnable: false` cases with that note rather than faking a run.

Build-image assumptions (documented once): the build sandbox has NO network, a
C compiler (`cc`) and `/bin/sh`, a read-only bundle, a writable scratch dir, a
fresh `$HOME` and `SOURCE_DATE_EPOCH=0`. Recipes vendor nothing and fetch
nothing.

The hand-written `near-reexec-*` cases are NOT produced by this generator (they
are full reexec-witness copies) and are left untouched.

Run:  python3 generate.py            # writes/overwrites the generated case dirs
      python3 generate.py --check    # fail if the tree is stale vs the generator
"""
import json
import os
import shutil
import stat
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))

# Placeholder challenge; the e2e driver rewrites it to the live challenge id.
CHALLENGE = "chl_0000000000000000000000000000000"

# Cases this generator owns. Anything else under hostile-submissions/ (e.g. the
# hand-written near-reexec-* packages) is left alone.
OWNED = set()

# --------------------------------------------------------------------------- #
# shared toy-arithmetic sources (the demo reference candidate, verbatim), with
# per-case overrides. The demo challenge's claim encoding is demo-toy-arith-v1:
#   request  = 16 bytes = two u64 LE (a, b)
#   claim    = 24 bytes = request ++ le64(a*b)
#   proof    = 40 bytes = "TOYPRF01" ++ claim(24) ++ le64(fnv1a(fnv1a(INIT,key),proof[0..32]))
# --------------------------------------------------------------------------- #

COMMON_H = '''#include <stddef.h>
#include <stdint.h>
const char *arg(int argc, char **argv, const char *key);
long read_file(const char *path, unsigned char *buf, size_t max);
int write_file(const char *path, const unsigned char *buf, size_t n);
uint64_t le64(const unsigned char *p);
void put_le64(unsigned char *p, uint64_t v);
uint64_t fnv1a(uint64_t h, const unsigned char *p, size_t n);
#define FNV_INIT 0xcbf29ce484222325ULL
#define KEY_MAX 256
#define PROOF_MAGIC "TOYPRF01"
#define PROOF_LEN (8 + 24 + 8)
'''

COMMON_C = '''#include "common.h"
#include <stdio.h>
#include <string.h>
const char *arg(int argc, char **argv, const char *key) {
  for (int i = 1; i + 1 < argc; i++) if (!strcmp(argv[i], key)) return argv[i + 1];
  return NULL;
}
long read_file(const char *path, unsigned char *buf, size_t max) {
  FILE *f = path ? fopen(path, "rb") : NULL;
  if (!f) return -1;
  size_t n = fread(buf, 1, max, f);
  int extra = fgetc(f);
  fclose(f);
  return extra == EOF ? (long)n : -1;
}
int write_file(const char *path, const unsigned char *buf, size_t n) {
  FILE *f = path ? fopen(path, "wb") : NULL;
  if (!f) return -1;
  int ok = fwrite(buf, 1, n, f) == n;
  return (fclose(f) == 0 && ok) ? 0 : -1;
}
uint64_t le64(const unsigned char *p) {
  uint64_t v = 0;
  for (int i = 7; i >= 0; i--) v = (v << 8) | p[i];
  return v;
}
void put_le64(unsigned char *p, uint64_t v) {
  for (int i = 0; i < 8; i++) { p[i] = (unsigned char)v; v >>= 8; }
}
uint64_t fnv1a(uint64_t h, const unsigned char *p, size_t n) {
  for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 0x100000001b3ULL; }
  return h;
}
'''

PREPARE_C = '''/* prepare --params <f> --out <dir>: writes the public key file. */
#include "common.h"
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
int main(int argc, char **argv) {
  const char *out = arg(argc, argv, "--out");
  if (!out || !arg(argc, argv, "--params")) return 2;
  mkdir(out, 0755);
  char path[4096];
  snprintf(path, sizeof path, "%s/key", out);
  const char *key = "toy-arith-checksum-key-v1";
  return write_file(path, (const unsigned char *)key, strlen(key)) ? 2 : 0;
}
'''

PROVE_C = '''/* prove --public D --request R --witness W --claim-out C --proof-out P */
#include "common.h"
#include <stdio.h>
#include <string.h>
int main(int argc, char **argv) {
  const char *pub = arg(argc, argv, "--public"), *req = arg(argc, argv, "--request");
  const char *wit = arg(argc, argv, "--witness"), *co = arg(argc, argv, "--claim-out");
  const char *po = arg(argc, argv, "--proof-out");
  if (!pub || !req || !wit || !co || !po) return 2;
  unsigned char r[16], w[1], key[KEY_MAX], claim[24], proof[PROOF_LEN];
  if (read_file(req, r, sizeof r) != 16) return 2;
  if (read_file(wit, w, 0) < 0) return 2;
  char kp[4096];
  snprintf(kp, sizeof kp, "%s/key", pub);
  long kn = read_file(kp, key, sizeof key);
  if (kn < 0) return 2;
  memcpy(claim, r, 16);
  put_le64(claim + 16, le64(r) * le64(r + 8));
  memcpy(proof, PROOF_MAGIC, 8);
  memcpy(proof + 8, claim, 24);
  uint64_t h = fnv1a(fnv1a(FNV_INIT, key, (size_t)kn), proof, 32);
  put_le64(proof + 32, h);
  return (write_file(co, claim, 24) || write_file(po, proof, PROOF_LEN)) ? 2 : 0;
}
'''

VERIFY_C = '''/* verify --public D --claim C --proof P: 0 accept, 1 reject, 2 error. */
#include "common.h"
#include <stdio.h>
#include <string.h>
int main(int argc, char **argv) {
  const char *pub = arg(argc, argv, "--public"), *cp = arg(argc, argv, "--claim");
  const char *pp = arg(argc, argv, "--proof");
  if (!pub || !cp || !pp) return 2;
  unsigned char claim[24], proof[PROOF_LEN], key[KEY_MAX];
  char kp[4096];
  snprintf(kp, sizeof kp, "%s/key", pub);
  long kn = read_file(kp, key, sizeof key);
  if (kn < 0) return 2;
  if (read_file(cp, claim, sizeof claim) != 24) return 1;
  if (read_file(pp, proof, sizeof proof) != PROOF_LEN) return 1;
  if (le64(claim + 16) != le64(claim) * le64(claim + 8)) return 1;
  if (memcmp(proof, PROOF_MAGIC, 8) || memcmp(proof + 8, claim, 24)) return 1;
  if (le64(proof + 32) != fnv1a(fnv1a(FNV_INIT, key, (size_t)kn), proof, 32)) return 1;
  return 0;
}
'''

BASE_BUILD = '''#!/bin/sh
# Offline, reproducible: plain cc, no timestamps or randomness embedded.
set -eu
mkdir -p out
for t in prepare prove verify; do
  cc -O2 -std=c99 -Wall -o "out/$t" source/common.c "source/$t.c"
done
'''

# A tiny Lean project for the generic (non-executable) formal stubs.
STUB_TOOLCHAIN = "leanprover/lean4:v4.34.1\n"
STUB_LAKEFILE = '''import Lake
open Lake DSL
package candidate
require ArenaCore from git "" @ "frozen"
require NearSpec from git "" @ "frozen"
@[default_target] lean_lib Candidate
'''
STUB_LEAN = '''import ArenaCore
import NearSpec.TransferV1
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := by
  exact ArenaCore.admits_of_sound NearSpec.TransferV1.sound
'''

BASE_CANDIDATE = '''schema = "arena-candidate-v1"
name = "{name}"
agent = "adversarial-suite"
challenge = "{challenge}"
backend_family = "{backend_family}"
security_profile_request = "validity-classical-128"
hardware = {{ gpu = false, min_ram_gb = 1 }}

[build]
recipe = "build-recipe/build.sh"
outputs = ["out/prepare", "out/prove", "out/verify"]

[entry]
prepare = "out/prepare"
prove = "out/prove"
verify = "out/verify"
'''

FORMAL_CANDIDATE = BASE_CANDIDATE + '''
[formal]
lean_project = "formal"
certificate = "Candidate.certificate"
'''

STAGE = {
    "PKG_WELLFORMED": "VALIDATED",
    "BUILD_REPRODUCIBLE": "BUILT",
    "ARTIFACT_BINDING": "BUILT",
    "FORMAL_SEMANTIC_SOUNDNESS": "FORMAL_CHECKED",
    "FORMAL_SEMANTIC_COMPLETENESS": "FORMAL_CHECKED",
    "FORMAL_CRYPTO_SOUNDNESS": "FORMAL_CHECKED",
    "FORMAL_IMPL_CONNECTION": "FORMAL_CHECKED",
    "AXIOM_AUDIT": "FORMAL_CHECKED",
    "CONFORMANCE_DIFFERENTIAL": "CONFORMANCE_CHECKED",
    "ADVERSARIAL_PROOFS": "CONFORMANCE_CHECKED",
    "PROVER_RELIABILITY": "CONFORMANCE_CHECKED",
    "RESOURCE_LIMITS": "BENCHMARKED",
    "BENCHMARK": "BENCHMARKED",
}

CASES = []


def case(name, family, why, gates, reasons, *, targets=("demo",), runnable=True,
         candidate=None, build=None, source=None, formal=None, archive=None,
         readme_extra="", extra=None, notes=None, decision="REJECTED",
         must_never=None):
    OWNED.add(name)
    CASES.append(dict(
        name=name, family=family, why=why, gates=gates, reasons=reasons,
        targets=list(targets), runnable=runnable,
        candidate=candidate, build=build, source=source or {}, formal=formal or {},
        archive=archive, readme_extra=readme_extra, extra=extra or {}, notes=notes,
        decision=decision, must_never=must_never,
    ))


# ===========================================================================
# DEMO cases: honest toy-arith candidate, one attacked behaviour. Run live on
# the demo challenge; the attacked gate is the first to fail.
# ===========================================================================

case("always-accept-verifier", "verifier-soundness",
     "The prover is the honest toy-arith reference, so BUILD / CONFORMANCE / "
     "PROVER_RELIABILITY pass. The verifier, however, ignores its input and "
     "exits 0 for every proof. ADVERSARIAL_PROOFS feeds hostile proof bytes and "
     "must fail: a verifier that accepts everything proves nothing.",
     ["ADVERSARIAL_PROOFS"], ["HOSTILE_PROOF_ACCEPTED"],
     source={"verify.c": '#include "common.h"\nint main(int c,char**v){(void)c;(void)v;return 0;}\n'})

case("always-reject-verifier", "prover-reliability",
     "The verifier exits 1 for every proof, including the candidate's own honest "
     "proof. PROVER_RELIABILITY must fail: the honest prover's output does not "
     "verify, so the backend cannot discharge the required workloads.",
     ["PROVER_RELIABILITY"], ["PROVER_FAILED"],
     source={"verify.c": '#include "common.h"\nint main(int c,char**v){(void)c;(void)v;return 1;}\n'})

case("weak-public-input-binding", "public-input-binding",
     "The prover is honest, so the honest-proof checks pass. The verifier only "
     "checks the proof's magic tag -- it does NOT recompute the checksum or bind "
     "the proof to the claim's public inputs. ADVERSARIAL_PROOFS feeds mutated "
     "proofs that keep the magic; any acceptance is HOSTILE_PROOF_ACCEPTED: a "
     "verifier that does not actually check the argument (or its binding to the "
     "claim) is unsound.",
     ["ADVERSARIAL_PROOFS"], ["HOSTILE_PROOF_ACCEPTED"],
     source={"verify.c": '''/* verify: checks ONLY the magic tag -- no checksum, no claim binding. */
#include "common.h"
#include <string.h>
int main(int argc, char **argv) {
  const char *pp = arg(argc, argv, "--proof");
  if (!pp) return 2;
  unsigned char proof[PROOF_LEN];
  if (read_file(pp, proof, sizeof proof) != PROOF_LEN) return 1;
  if (memcmp(proof, PROOF_MAGIC, 8)) return 1;   /* magic only */
  return 0;
}
'''})

case("forged-pass-output", "forged-output",
     "The build script prints PASS and writes fake gate-result JSON files into "
     "out/; the verifier prints a PASS banner. The judge computes gates itself "
     "from measured outcomes and ignores candidate stdout and candidate-written "
     "files, so the verifier is still exercised and -- being always-accept -- "
     "fails ADVERSARIAL_PROOFS. Forged output changes nothing.",
     ["ADVERSARIAL_PROOFS"], ["HOSTILE_PROOF_ACCEPTED"],
     build='''#!/bin/sh
set -eu
mkdir -p out gate-results
echo "ALL GATES PASS"
# Forge gate results OUTSIDE out/ (the judge compares only declared build
# outputs and ignores these entirely).
for g in PKG_WELLFORMED CONFORMANCE_DIFFERENTIAL ADVERSARIAL_PROOFS BENCHMARK; do
  printf '{"gate":"%s","status":"PASS"}\\n' "$g" > "gate-results/$g.json"
done
for t in prepare prove verify; do
  cc -O2 -std=c99 -o "out/$t" source/common.c "source/$t.c"
done
''',
     source={"verify.c": '#include "common.h"\n#include <stdio.h>\nint main(int c,char**v){(void)c;(void)v;printf("GATE ADVERSARIAL_PROOFS PASS\\n");return 0;}\n'},
     notes="Demonstrates judge-computed gates override forged candidate output.")

case("ui-injection-logs", "ui-log-injection",
     "The prover is honest but the verifier writes HTML/JS, ANSI escapes and an "
     "RTL override to stderr and accepts every proof. The submission is REJECTED "
     "at ADVERSARIAL_PROOFS, and the API must additionally return every captured "
     "string sanitized -- no raw control characters.",
     ["ADVERSARIAL_PROOFS"], ["HOSTILE_PROOF_ACCEPTED"],
     source={"verify.c": r'''#include "common.h"
#include <stdio.h>
int main(int c, char **v) {
  (void)c; (void)v;
  fprintf(stderr, "\x1b[31m<script>alert('xss')</script>\xe2\x80\xaegnp.\x07\n");
  return 0;  /* accept everything; also an unsound verifier */
}
''',},
     readme_extra="\n<script>alert('readme-xss')</script>\n",
     notes="attack_family 'ui-log-injection' tells the driver to assert the API "
           "response has no raw control chars.")

case("benchmark-shortcut", "benchmark-cheat",
     "The prover returns the correct product ONLY for a hard-coded 'benchmark' "
     "request and an off-by-one wrong product for everything else. Conformance "
     "samples fresh judge inputs (sampled after freeze), so CONFORMANCE_"
     "DIFFERENTIAL against the oracle fails with CLAIM_MISMATCH. A prover that "
     "only works on known inputs cannot pass differential testing.",
     ["CONFORMANCE_DIFFERENTIAL"], ["CLAIM_MISMATCH"],
     source={"prove.c": '''/* prove: correct product only for one hard-coded request; else wrong. */
#include "common.h"
#include <stdio.h>
#include <string.h>
int main(int argc, char **argv) {
  const char *pub = arg(argc, argv, "--public"), *req = arg(argc, argv, "--request");
  const char *wit = arg(argc, argv, "--witness"), *co = arg(argc, argv, "--claim-out");
  const char *po = arg(argc, argv, "--proof-out");
  if (!pub || !req || !wit || !co || !po) return 2;
  unsigned char r[16], w[1], key[KEY_MAX], claim[24], proof[PROOF_LEN];
  if (read_file(req, r, sizeof r) != 16) return 2;
  if (read_file(wit, w, 0) < 0) return 2;
  char kp[4096]; snprintf(kp, sizeof kp, "%s/key", pub);
  long kn = read_file(kp, key, sizeof key); if (kn < 0) return 2;
  uint64_t a = le64(r), b = le64(r + 8), prod = a * b;
  static const unsigned char BENCH[16] = {7,7,7,7,7,7,7,7,3,3,3,3,3,3,3,3};
  if (memcmp(r, BENCH, 16)) prod += 1;             /* wrong unless the bench input */
  memcpy(claim, r, 16); put_le64(claim + 16, prod);
  memcpy(proof, PROOF_MAGIC, 8); memcpy(proof + 8, claim, 24);
  put_le64(proof + 32, fnv1a(fnv1a(FNV_INIT, key, (size_t)kn), proof, 32));
  return (write_file(co, claim, 24) || write_file(po, proof, PROOF_LEN)) ? 2 : 0;
}
'''})

case("precomputed-fixture-table", "benchmark-cheat",
     "`prepare` writes a tiny table of answers for public fixtures into the "
     "public dir; `prove` just looks the request up and returns a wrong product "
     "on a miss. `prepare` never sees the challenge inputs (they are sampled "
     "after freeze), so held-out inputs miss the table and CONFORMANCE_"
     "DIFFERENTIAL fails. Setup that depends on challenge inputs is impossible.",
     ["CONFORMANCE_DIFFERENTIAL"], ["CLAIM_MISMATCH"],
     source={
         "prepare.c": '''/* prepare: writes the key AND a 'table' marker for public fixtures. */
#include "common.h"
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
int main(int argc, char **argv) {
  const char *out = arg(argc, argv, "--out");
  if (!out || !arg(argc, argv, "--params")) return 2;
  mkdir(out, 0755);
  char p[4096]; snprintf(p, sizeof p, "%s/key", out);
  if (write_file(p, (const unsigned char *)"toy-arith-checksum-key-v1", 25)) return 2;
  snprintf(p, sizeof p, "%s/table", out);
  return write_file(p, (const unsigned char *)"public-fixtures-only", 20) ? 2 : 0;
}
''',
         "prove.c": '''/* prove: 'instant' lookup; correct only for the one tabled input. */
#include "common.h"
#include <stdio.h>
#include <string.h>
int main(int argc, char **argv) {
  const char *pub = arg(argc, argv, "--public"), *req = arg(argc, argv, "--request");
  const char *wit = arg(argc, argv, "--witness"), *co = arg(argc, argv, "--claim-out");
  const char *po = arg(argc, argv, "--proof-out");
  if (!pub || !req || !wit || !co || !po) return 2;
  unsigned char r[16], w[1], key[KEY_MAX], claim[24], proof[PROOF_LEN];
  if (read_file(req, r, sizeof r) != 16) return 2;
  if (read_file(wit, w, 0) < 0) return 2;
  char kp[4096]; snprintf(kp, sizeof kp, "%s/key", pub);
  long kn = read_file(kp, key, sizeof key); if (kn < 0) return 2;
  uint64_t prod = le64(r) * le64(r + 8);
  static const unsigned char TAB[16] = {2,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0};
  if (memcmp(r, TAB, 16)) prod ^= 0xdead;          /* table miss -> wrong */
  memcpy(claim, r, 16); put_le64(claim + 16, prod);
  memcpy(proof, PROOF_MAGIC, 8); memcpy(proof + 8, claim, 24);
  put_le64(proof + 32, fnv1a(fnv1a(FNV_INIT, key, (size_t)kn), proof, 32));
  return (write_file(co, claim, 24) || write_file(po, proof, PROOF_LEN)) ? 2 : 0;
}
'''})

case("background-daemon", "async-cheat",
     "`prove` forks a background daemon and exits immediately without writing the "
     "proof; the daemon would 'finish later'. The sandbox tears down the whole "
     "process group at exit and collects outputs only then, so the proof is "
     "absent: PROVER_RELIABILITY fails.",
     ["PROVER_RELIABILITY"], ["PROVER_FAILED"],
     source={"prove.c": '''#include "common.h"
#include <stdio.h>
#include <unistd.h>
int main(int argc, char **argv) {
  const char *po = arg(argc, argv, "--proof-out"); if (!po) return 2;
  if (fork() == 0) { sleep(30);
    FILE *f = fopen(po, "wb"); if (f) { fputs("TOYPRF01", f); fclose(f); } _exit(0); }
  return 0;  /* parent exits before the proof exists */
}
'''})

for esc_name, esc_why, esc_body in [
    ("sandbox-escape-filesystem",
     "`prove` tries to read /etc/passwd and ~/.ssh and to write outside the "
     "scratch dir, then exits without producing a proof. The bundle is read-only, "
     "home is absent and writes outside scratch are denied, so the attempt is "
     "contained and has no effect; the observable kill is PROVER_RELIABILITY "
     "(no proof).",
     '''#include "common.h"
#include <stdio.h>
int main(int argc, char **argv) {
  (void)argc; (void)argv;
  FILE *a = fopen("/etc/passwd", "rb"); if (a) fclose(a);
  FILE *b = fopen("/root/.ssh/id_rsa", "rb"); if (b) fclose(b);
  FILE *c = fopen("/escape-write", "wb"); if (c) { fputs("x", c); fclose(c); }
  FILE *d = fopen("../../escape", "wb"); if (d) { fputs("x", d); fclose(d); }
  return 0;  /* no proof written */
}
'''),
    ("sandbox-escape-network",
     "`prove` tries to open an outbound TCP connection, then exits without a "
     "proof. The sandbox has no network (`network: None`), so connect fails; the "
     "observable kill is PROVER_RELIABILITY.",
     '''#include "common.h"
#include <string.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
int main(int argc, char **argv) {
  (void)argc; (void)argv;
  int s = socket(AF_INET, SOCK_STREAM, 0);
  struct sockaddr_in a; memset(&a, 0, sizeof a);
  a.sin_family = AF_INET; a.sin_port = htons(53); a.sin_addr.s_addr = inet_addr("8.8.8.8");
  connect(s, (struct sockaddr *)&a, sizeof a);
  return 0;  /* no proof written */
}
'''),
    ("sandbox-ptrace-proc",
     "`prove` attempts ptrace and pokes at /proc/self/mem and the docker socket, "
     "then exits without a proof. All are denied/absent; the observable kill is "
     "PROVER_RELIABILITY.",
     '''#include "common.h"
#include <stdio.h>
#include <sys/ptrace.h>
int main(int argc, char **argv) {
  (void)argc; (void)argv;
  ptrace(PTRACE_TRACEME, 0, 0, 0);
  FILE *m = fopen("/proc/self/mem", "rb"); if (m) fclose(m);
  FILE *d = fopen("/var/run/docker.sock", "rb"); if (d) fclose(d);
  return 0;  /* no proof written */
}
'''),
]:
    case(esc_name, "sandbox-escape", esc_why,
         ["PROVER_RELIABILITY"], ["PROVER_FAILED"],
         source={"prove.c": esc_body},
         notes="HONEST OBSERVABLE on bwrap-dev (no seccomp): the escape attempt "
               "is contained and has no effect, so the kill is 'no proof "
               "produced' (PROVER_FAILED), not a dedicated SANDBOX_VIOLATION. "
               "Firecracker's forged-guest-report path maps to SANDBOX_VIOLATION; "
               "sound syscall-level attempt detection in the sandbox is a "
               "runners-core follow-up (see adversarial/README.md).")

case("sandbox-fork-bomb", "sandbox-escape",
     "`prove` forks without bound. The sandbox pid cap / memory limit contains it "
     "and the worker reports RESOURCE_LIMITS / RESOURCE_LIMIT rather than hanging "
     "the host.",
     ["RESOURCE_LIMITS"], ["RESOURCE_LIMIT"],
     source={"prove.c": '#include <unistd.h>\nint main(void){for(;;){if(fork()<0)break;}return 0;}\n'})

case("forged-timing", "benchmark-cheat",
     "`prove` prints a fabricated fast timing to stdout and tries to tamper with "
     "the clock (clock_settime), then exits without a valid proof. The supervisor "
     "measures wall time itself and ignores stdout; clock_settime is denied. "
     "Because forging gains nothing, the only way this changes the outcome is by "
     "breaking the prover -- observable as PROVER_RELIABILITY.",
     ["PROVER_RELIABILITY"], ["PROVER_FAILED"],
     source={"prove.c": '''#define _POSIX_C_SOURCE 200112L
#include "common.h"
#include <stdio.h>
#include <time.h>
int main(int argc, char **argv) {
  (void)argc; (void)argv;
  printf("prove_time_ns=1\\n");                 /* ignored: supervisor measures */
  struct timespec t = {0, 0}; clock_settime(CLOCK_REALTIME, &t);  /* denied */
  return 0;  /* no proof written */
}
'''},
     notes="Supervisor-measured timing is authoritative, so the fake print is "
           "futile; clock tamper is contained. The runnable kill on the demo "
           "worker is the absent proof.")

case("build-network-fetch", "build-integrity",
     "The build recipe tries to fetch a dependency over the network (curl, then "
     "git). The build sandbox has no network, so the fetch fails and "
     "BUILD_REPRODUCIBLE fails with BUILD_FAILED. Honest packages vendor "
     "everything.",
     ["BUILD_REPRODUCIBLE"], ["BUILD_FAILED"],
     build='''#!/bin/sh
set -eu
mkdir -p out
curl -fsSL https://example.com/prover.tar.gz -o prover.tar.gz || \\
  git clone https://example.com/prover.git vendor
for t in prepare prove verify; do cc -O2 -std=c99 -o "out/$t" source/common.c "source/$t.c"; done
''')

case("build-nonreproducible", "build-integrity",
     "The build mixes bytes from /dev/urandom into the compiled verifier, so two "
     "independent judge builds are not bit-identical. BUILD_REPRODUCIBLE must "
     "fail with BUILD_NOT_REPRODUCIBLE; a non-deterministic build cannot be bound "
     "to a certified artifact.",
     ["BUILD_REPRODUCIBLE"], ["BUILD_NOT_REPRODUCIBLE"],
     build='''#!/bin/sh
set -eu
mkdir -p out
# Non-deterministic: bake random bytes into the verifier.
R="$(head -c 8 /dev/urandom | od -An -tx1 | tr -d ' \\n')"
printf 'const char *build_nonce = "%s";\\n' "$R" > source/_nonce.c
cc -O2 -std=c99 -o out/prepare source/common.c source/prepare.c
cc -O2 -std=c99 -o out/prove   source/common.c source/prove.c
cc -O2 -std=c99 -o out/verify  source/common.c source/verify.c source/_nonce.c
''')

case("build-dependency-substitution", "build-integrity",
     "The recipe ignores the vendored verifier source and compiles an alternate, "
     "backdoored `verify_alt.c` (always-accept) as out/verify. The build is "
     "deterministic, so it reproduces; the backdoored verifier is then caught by "
     "ADVERSARIAL_PROOFS. (On the NEAR challenge the same swap is caught earlier "
     "by ARTIFACT_BINDING against the certified verifier digest.)",
     ["ADVERSARIAL_PROOFS"], ["HOSTILE_PROOF_ACCEPTED"],
     build='''#!/bin/sh
set -eu
mkdir -p out
cc -O2 -std=c99 -o out/prepare source/common.c source/prepare.c
cc -O2 -std=c99 -o out/prove   source/common.c source/prove.c
cc -O2 -std=c99 -o out/verify  source/common.c source/verify_alt.c   # substituted
''',
     source={"verify_alt.c": '#include "common.h"\nint main(int c,char**v){(void)c;(void)v;return 0;}\n'})

case("ui-injection-manifest", "ui-log-injection",
     "Injection payload in the manifest `name` field, which is constrained to "
     "[a-z0-9-]. PKG_WELLFORMED must reject it with MANIFEST_INVALID before any "
     "code runs; the free-form backend_family payload must be stored and rendered "
     "escaped.",
     ["PKG_WELLFORMED"], ["MANIFEST_INVALID"],
     candidate=BASE_CANDIDATE.replace('name = "{name}"', 'name = "<script>alert(1)</script>"')
                             .replace('backend_family = "{backend_family}"',
                                      'backend_family = "fam<script>alert(2)</script>"'))

# ---- archive attacks (malicious tar built by make-archive.py) --------------

for an, awhy, kind in [
    ("archive-zip-slip",
     "An entry whose path escapes the extraction root via `../` (zip-slip). "
     "Extraction must refuse path traversal before writing any file.", "zipslip"),
    ("archive-symlink-escape",
     "A symlink pointing outside the root. Symlinks are rejected outright by the "
     "archive policy.", "symlink"),
    ("archive-hardlink",
     "A hardlink to a file outside the package. Hardlinks are rejected.", "hardlink"),
    ("archive-device-file",
     "A character-device node. Device entries are rejected.", "device"),
    ("archive-bomb",
     "A decompression bomb that expands far beyond the expansion / ratio limits. "
     "Extraction must stop at the cap, not exhaust disk.", "bomb"),
]:
    case(an, "archive-attack",
         awhy + " The payload is the archive ENCODING, so the directory package "
         "here is a well-formed placeholder and make-archive.py emits the "
         "malicious tar; the driver uploads that.",
         ["PKG_WELLFORMED"], ["ARCHIVE_UNSAFE"],
         archive=kind,
         notes="make-archive.py writes raw tar headers with Python's tarfile so "
               "device/hardlink/symlink entries do not need privilege and the "
               "package is not nested under a subdir.")

# ===========================================================================
# NEAR-formal cases: the attacked obligations (FORMAL_*, AXIOM_AUDIT,
# ARTIFACT_BINDING, FORMAL_CRYPTO_SOUNDNESS) exist only on the formal challenge.
# These generic stubs DOCUMENT the attack; they are not executable without a
# real reexec-witness backend, so runnable=false and the driver skips them with
# that note. Executable NEAR kills: near-reexec-malicious-executable
# (ARTIFACT_BINDING) and near-reexec-skip-refund (FORMAL_*), verified in
# Milestone D.
# ===========================================================================

def formal_stub(name, family, why, gates, reasons, lean, notes=None):
    case(name, family, why, gates, reasons, targets=("near-formal",), runnable=False,
         candidate=FORMAL_CANDIDATE, formal={"Candidate.lean": lean}, notes=notes)

formal_stub("malicious-executable", "artifact-binding",
    "Correct certificate about a faithful model, but the built verifier binary "
    "differs from the certified verifier artifact. ARTIFACT_BINDING ties the "
    "running binary's digest to the formally connected artifact; a mismatch must "
    "fail. Executable analogue: near-reexec-malicious-executable.",
    ["ARTIFACT_BINDING"], ["ARTIFACT_BINDING_FAILED"], STUB_LEAN)

formal_stub("wrong-verification-key", "artifact-binding",
    "Params / verification key for a different protocol version or program than "
    "the challenge pins. ARTIFACT_BINDING compares the built params digest "
    "against the certified one; a wrong key must fail.",
    ["ARTIFACT_BINDING"], ["ARTIFACT_BINDING_FAILED"], STUB_LEAN)

formal_stub("stale-certificate", "artifact-binding",
    "The certificate certifies a PREVIOUS verifier (embedded formal digests point "
    "at an older artifact). PACKAGING kill, not semantic: the proof may be sound "
    "for the old verifier but is not bound to the artifact built now, so "
    "ARTIFACT_BINDING fails.",
    ["ARTIFACT_BINDING"], ["ARTIFACT_BINDING_FAILED"], STUB_LEAN,
    notes="Classified PACKAGING: a stale-digest failure must NOT be reported as "
          "a semantic-soundness failure.")

formal_stub("restricted-domain", "theorem-type-mismatch",
    "The certificate proves soundness only on a RESTRICTED domain (extra "
    "hypothesis). Its type is not the challenge's required relation type, so "
    "FORMAL_SEMANTIC_SOUNDNESS must fail on a type mismatch.",
    ["FORMAL_SEMANTIC_SOUNDNESS"], ["THEOREM_TYPE_MISMATCH"],
    '''import ArenaCore
import NearSpec.TransferV1
theorem Candidate.certificate (h : NearSpec.TransferV1.SingleReceipt) :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := by
  exact ArenaCore.admits_of_sound (NearSpec.TransferV1.sound_restricted h)
''')

formal_stub("false-premise", "theorem-type-mismatch",
    "The certificate is `False -> Goal`, trivially provable and vacuous. Its type "
    "carries an extra unsatisfiable premise, so it is not the required relation "
    "type: FORMAL_SEMANTIC_SOUNDNESS must fail on the type mismatch.",
    ["FORMAL_SEMANTIC_SOUNDNESS"], ["THEOREM_TYPE_MISMATCH"],
    '''import ArenaCore
import NearSpec.TransferV1
theorem Candidate.certificate (h : False) :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation :=
  absurd h (by intro x; exact x.elim)
''')

formal_stub("missing-certificate", "formal-missing",
    "The manifest names `Candidate.certificate` but the Lean project defines no "
    "such constant. FORMAL_SEMANTIC_SOUNDNESS must fail with CERTIFICATE_MISSING "
    "rather than defaulting to pass.",
    ["FORMAL_SEMANTIC_SOUNDNESS"], ["CERTIFICATE_MISSING"],
    '''import ArenaCore
import NearSpec.TransferV1
theorem Candidate.something_else : True := trivial
''')

formal_stub("additional-axiom", "axiom-audit",
    "An extra `axiom` not on the allowlist is used to close the proof. "
    "AXIOM_AUDIT walks the transitive axioms and must fail with FORBIDDEN_AXIOM.",
    ["AXIOM_AUDIT"], ["FORBIDDEN_AXIOM"],
    '''import ArenaCore
import NearSpec.TransferV1
axiom Candidate.cheat : ArenaCore.Admits NearSpec.TransferV1.NearRelation
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := Candidate.cheat
''')

formal_stub("shadowed-definition", "axiom-audit",
    "The package ships its own altered copy of a trusted definition (a weakened "
    "`ArenaCore.Admits`) so the certificate type-checks against the wrong meaning. "
    "The checker pins trusted sources by tree digest and must detect the shadow.",
    ["AXIOM_AUDIT"], ["SHADOWED_DEFINITION"],
    '''import ArenaCore            -- resolves to the shipped, weakened copy
import NearSpec.TransferV1
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := trivial
''',
    notes="Also ships formal/ArenaCore.lean redefining Admits := True.")

formal_stub("sorry-certificate", "axiom-audit",
    "The certificate is closed with `sorry` (emits `sorryAx`, an unsound axiom). "
    "AXIOM_AUDIT must fail with SORRY_FOUND.",
    ["AXIOM_AUDIT"], ["SORRY_FOUND"],
    '''import ArenaCore
import NearSpec.TransferV1
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := by
  sorry
''')

formal_stub("native-decide-certificate", "axiom-audit",
    "The proof uses `native_decide`, trusting compiled code and `ofReduceBool` "
    "instead of the kernel. The policy forbids native evaluation; AXIOM_AUDIT "
    "must fail with NATIVE_EVAL_FOUND.",
    ["AXIOM_AUDIT"], ["NATIVE_EVAL_FOUND"],
    '''import ArenaCore
import NearSpec.TransferV1
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := by
  native_decide
''')

formal_stub("changed-security-parameters", "crypto-soundness",
    "The manifest requests 128-bit security but the concrete parameters yield ~40 "
    "bits. The judge evaluates the CERTIFIED bound formula at the ACTUAL "
    "parameters (kernel-evaluated) and ignores the manifest claim; "
    "FORMAL_CRYPTO_SOUNDNESS must fail with SECURITY_BOUND_INSUFFICIENT.",
    ["FORMAL_CRYPTO_SOUNDNESS"], ["SECURITY_BOUND_INSUFFICIENT"],
    '''import ArenaCore
import NearSpec.TransferV1
def Candidate.params : ArenaCore.CryptoParams :=
  { queryReps := 1, fieldBits := 64, soundnessErrorLog2 := 40 }
theorem Candidate.certificate :
    ArenaCore.AdmitsWith Candidate.params NearSpec.TransferV1.NearRelation := by
  exact ArenaCore.admits_of_sound NearSpec.TransferV1.sound
''')


# ===========================================================================
# make-archive.py (one script, selects the kind from its sibling archive-kind)
# ===========================================================================

MAKE_ARCHIVE_PY = r'''#!/usr/bin/env python3
"""Emit a MALICIOUS tar to stdout for this archive-attack case. The e2e driver
uploads these bytes directly (not a tar of the directory). Uses Python tarfile
to write raw headers, so device/hardlink/symlink entries need no privilege and
the package is NOT nested under a subdirectory. No network.
"""
import io, os, sys, tarfile

HERE = os.path.dirname(os.path.abspath(__file__))
KIND = (sys.argv[1] if len(sys.argv) > 1
        else open(os.path.join(HERE, "archive-kind")).read().strip())

CANDIDATE = b"""schema = "arena-candidate-v1"
name = "archive-attack"
agent = "adversarial-suite"
challenge = "CHALLENGE_PLACEHOLDER"
backend_family = "archive"
security_profile_request = "validity-classical-128"
hardware = { gpu = false, min_ram_gb = 1 }
[build]
recipe = "build-recipe/build.sh"
outputs = ["out/verify"]
[entry]
prepare = "out/prepare"
prove = "out/prove"
verify = "out/verify"
"""

def add_file(tar, name, data, mode=0o644):
    ti = tarfile.TarInfo(name)
    ti.size = len(data); ti.mode = mode; ti.mtime = 0
    tar.addfile(ti, io.BytesIO(data))

buf = io.BytesIO()
tar = tarfile.open(fileobj=buf, mode="w", format=tarfile.GNU_FORMAT)
# a well-formed package at the archive ROOT (not nested)
add_file(tar, "candidate.toml", CANDIDATE)
add_file(tar, "README.md", b"archive attack placeholder\n")
add_file(tar, "build-recipe/build.sh", b"#!/bin/sh\nmkdir -p out; : > out/verify\n", 0o755)
add_file(tar, "source/verify.c", b"int main(void){return 0;}\n")
add_file(tar, "dependency-locks/NONE", b"none\n")

if KIND == "zipslip":
    add_file(tar, "../../../../tmp/zipslip-escape", b"escaped\n")
elif KIND == "symlink":
    ti = tarfile.TarInfo("source/leak"); ti.type = tarfile.SYMTYPE
    ti.linkname = "/etc/passwd"; ti.mtime = 0; tar.addfile(ti)
elif KIND == "hardlink":
    ti = tarfile.TarInfo("source/hard"); ti.type = tarfile.LNKTYPE
    ti.linkname = "/etc/passwd"; ti.mtime = 0; tar.addfile(ti)
elif KIND == "device":
    ti = tarfile.TarInfo("source/dev0"); ti.type = tarfile.CHRTYPE
    ti.devmajor = 1; ti.devminor = 3; ti.mode = 0o666; ti.mtime = 0; tar.addfile(ti)
elif KIND == "bomb":
    # one large all-zeros entry: compresses to almost nothing, so the
    # decompressed/compressed ratio blows past the archive guard (>200 after
    # 16 MiB). 128 MiB is plenty and cheap to build in RAM.
    big = 128 * 1024 * 1024
    ti = tarfile.TarInfo("source/zeros"); ti.size = big; ti.mode = 0o644; ti.mtime = 0
    tar.addfile(ti, io.BytesIO(bytes(big)))
else:
    sys.stderr.write("unknown kind %s\n" % KIND); sys.exit(2)

tar.close()
data = buf.getvalue()
if KIND == "bomb":
    import subprocess
    p = subprocess.run(["zstd", "-19", "-c"], input=data, stdout=subprocess.PIPE)
    data = p.stdout
sys.stdout.buffer.write(data)
'''


# ===========================================================================
# emit
# ===========================================================================

def chmod_x(path):
    st = os.stat(path)
    os.chmod(path, st.st_mode | stat.S_IEXEC | stat.S_IXGRP | stat.S_IXOTH)


def write(path, content, executable=False):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    mode = "w" if isinstance(content, str) else "wb"
    with open(path, mode) as f:
        f.write(content)
    if executable:
        chmod_x(path)


def build_files(c):
    files = {}
    is_formal = c["formal"] and "Candidate.lean" in c["formal"]
    base_cand = c["candidate"] or (FORMAL_CANDIDATE if is_formal else BASE_CANDIDATE)
    files["candidate.toml"] = base_cand.format(
        name=c["name"], challenge=CHALLENGE, backend_family=c["family"])

    files["build-recipe/build.sh"] = c["build"] or BASE_BUILD

    # source (toy base + overrides)
    src = {"common.h": COMMON_H, "common.c": COMMON_C,
           "prepare.c": PREPARE_C, "prove.c": PROVE_C, "verify.c": VERIFY_C}
    src.update(c["source"])
    for rel, content in src.items():
        files["source/" + rel] = content

    files["dependency-locks/NONE"] = "no external dependencies\n"

    # formal
    if is_formal or c["formal"]:
        fm = {"lean-toolchain": STUB_TOOLCHAIN, "lakefile.lean": STUB_LAKEFILE,
              "Candidate.lean": STUB_LEAN}
        fm.update(c["formal"])
        if c["name"] == "shadowed-definition":
            fm["ArenaCore.lean"] = ("/-- Shadowed, weakened trusted definition. -/\n"
                                    "namespace ArenaCore\n"
                                    "def Admits (_r : Prop) : Prop := True\n"
                                    "theorem admits_of_sound {r : Prop} (_ : r) : Admits r := trivial\n"
                                    "end ArenaCore\n")
        for rel, content in fm.items():
            files["formal/" + rel] = content
    else:
        # a formal/ dir must exist for the package layout; ship a trivial stub
        files["formal/Candidate.lean"] = "theorem Candidate.placeholder : True := trivial\n"

    for rel, content in c["extra"].items():
        files[rel] = content

    if c["archive"] is not None:
        files["make-archive.py"] = MAKE_ARCHIVE_PY
        files["archive-kind"] = c["archive"] + "\n"

    gates = ", ".join(c["gates"]); reasons = ", ".join(c["reasons"])
    readme = (f"# Hostile case: {c['name']}\n\n"
              f"**Attack family:** {c['family']}\n\n"
              f"**Targets:** {', '.join(c['targets'])}  (runnable: {str(c['runnable']).lower()})\n\n"
              f"**Expected decision:** {c['decision']}\n"
              f"**Expected failing gate(s):** {gates}\n"
              f"**Expected reason code(s):** {reasons}\n\n"
              f"## What this proves about the judge\n\n{c['why']}\n")
    if c["notes"]:
        readme += f"\n## Notes\n\n{c['notes']}\n"
    readme += c["readme_extra"]
    files["README.md"] = readme

    expect = {
        "case": c["name"],
        "attack_family": c["family"],
        "targets": c["targets"],
        "runnable": c["runnable"],
        "expected_decision": c["decision"],
        "expected_failing_gates": c["gates"],
        "expected_reason_codes": c["reasons"],
        "fail_by_stage": STAGE.get(c["gates"][0]) if c["gates"] else None,
        "must_never": c["must_never"] or ["ADMITTED", "accepted", "ranked"],
        "why": c["why"],
    }
    if c["notes"]:
        expect["notes"] = c["notes"]
    files["expect.json"] = json.dumps(expect, indent=2) + "\n"
    return files


def emit(c, check_only):
    d = os.path.join(ROOT, c["name"])
    files = build_files(c)
    if check_only:
        for rel, content in files.items():
            p = os.path.join(d, rel)
            mode = "r" if isinstance(content, str) else "rb"
            if not os.path.exists(p):
                return False, rel
            with open(p, mode) as f:
                if f.read() != content:
                    return False, rel
        # also fail if stale extra files linger
        return True, None
    if os.path.isdir(d):
        shutil.rmtree(d)
    for rel, content in files.items():
        ex = rel.endswith(".sh") or rel.endswith(".py")
        write(os.path.join(d, rel), content, executable=ex)
    return True, None


def main():
    check = "--check" in sys.argv
    names = [c["name"] for c in CASES]
    assert len(names) == len(set(names)), "duplicate case names"
    stale = []
    for c in CASES:
        ok, which = emit(c, check)
        if check and not ok:
            stale.append(f"{c['name']}:{which}")
    if check:
        if stale:
            print("STALE (regenerate with python3 generate.py):")
            for s in stale:
                print("  " + s)
            sys.exit(1)
        print(f"OK: {len(CASES)} generated cases match the generator")
    else:
        print(f"wrote {len(CASES)} hostile cases to {ROOT}")
        demo = sum(1 for c in CASES if "demo" in c["targets"])
        near = sum(1 for c in CASES if "near-formal" in c["targets"])
        runnable = sum(1 for c in CASES if c["runnable"])
        print(f"  demo-targeted: {demo}  near-formal-targeted: {near}  runnable: {runnable}")


if __name__ == "__main__":
    main()
