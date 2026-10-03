/-!
# Obligation status table (data; mirrors `EVIDENCE.md`)

`checked` = kernel-checked here; `trusted` = assumed, named TCB;
`tested` = differential / adversarial testing only; `missing` = no evidence.
-/

namespace Candidate.Status

inductive St where
  | checked | trusted | tested | missing
  deriving Repr, DecidableEq

structure Row where
  obligation : String
  status : St
  note : String
  deriving Repr

def table : List Row :=
  [ ⟨"FORMAL_SEMANTIC_SOUNDNESS (B-level)", .checked,
      "Candidate.backend_semSound; vacuous for B := Rel, STARK content moved to Pipeline hypotheses"⟩,
    ⟨"FORMAL_SEMANTIC_COMPLETENESS (B-level)", .checked, "Candidate.backend_semComplete; same caveat"⟩,
    ⟨"composition of open obligations", .checked,
      "Candidate.Pipeline.sound_or_forged (abstract parameters only)"⟩,
    ⟨"AIR => NearRelation (semantic soundness of the AIR)", .tested,
      "byte-identical claims on all public fixtures; native self-check; single-cell witness-mutation probe; no proof"⟩,
    ⟨"NearRelation => AIR satisfiable (completeness)", .tested,
      "honest prover succeeds on every in-domain fixture; no proof"⟩,
    ⟨"STARK/FRI/LogUp/FS soundness bound", .missing,
      "no Lean proof (ArkLib FRI soundness unproven); Plonky3 calculator (unverified): proven-UDR ~103, conjectured 128 (CR cap)"⟩,
    ⟨"AIR identity binding (public.bin)", .tested, "fingerprint digest recomputed by verify"⟩,
    ⟨"FORMAL_IMPL_CONNECTION (Rust verifier <-> model)", .missing, "native Rust verifier, no extraction"⟩,
    ⟨"FORMAL_CRYPTO_SOUNDNESS", .missing, "see STARK row"⟩,
    ⟨"AXIOM_AUDIT", .checked,
      "kernel axioms of every theorem here are within propext, Classical.choice, Quot.sound; no holes"⟩ ]

end Candidate.Status
