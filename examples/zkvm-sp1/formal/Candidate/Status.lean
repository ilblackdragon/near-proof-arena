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
      "Candidate.backend_semSound; vacuous for B := Rel, zkVM content moved to crypto/impl"⟩,
    ⟨"FORMAL_SEMANTIC_COMPLETENESS (B-level)", .checked,
      "Candidate.backend_semComplete; same caveat"⟩,
    ⟨"composition of open obligations", .checked,
      "Candidate.Pipeline.sound_or_forged (abstract parameters only)"⟩,
    ⟨"GUEST: transfer-core refines NearRelation", .tested,
      "1520 in-domain byte-identical claims vs oracle; 224 out-of-domain refused; no proof"⟩,
    ⟨"COMPILER: ELF implements transfer-core", .tested,
      "guest claims equal native claims on every proved/executed case; no verified compiler"⟩,
    ⟨"CONSTRAINTS: SP1 AIR soundness", .missing,
      "sp1-lean: 25 RV64IM chips only, machine theorem rests on an unproved hole; precompiles/syscalls/memory out of scope"⟩,
    ⟨"STARK/FS/RECURSION soundness bound", .missing,
      "no Lean proof anywhere; Poseidon2 FS not an approved assumption; SP1 targets 100 bits < 128"⟩,
    ⟨"VKEY binding", .tested,
      "judge-run prepare derives vkey from embedded ELF; verify pins ELF digest"⟩,
    ⟨"FORMAL_IMPL_CONNECTION", .missing,
      "native Rust verifier; at best .nativeTrusted (trusted edge) once a Lean model exists"⟩,
    ⟨"FORMAL_CRYPTO_SOUNDNESS", .missing, "see STARK/FS row"⟩,
    ⟨"AXIOM_AUDIT", .checked, "kernel axioms of every theorem here ⊆ {propext, Classical.choice, Quot.sound}; no holes"⟩ ]

end Candidate.Status
