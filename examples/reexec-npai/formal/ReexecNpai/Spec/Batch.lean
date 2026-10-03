import ReexecNpai.Spec.State

/-!
# Phase spec: applying the receipts
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

section
variable {pub cb pb : Bytes}

theorem batch_wp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat}
    (h : TrieSt cb pb rs R A K (vals0 pb A) m) :
    wp P (Inp pub cb pb) pBatch m (fun m' => ∃ acc vals,
      runBatch (claimOf cb).ctx (rootT A K (vals0 pb A)) rs = some acc ∧
      TrieSt cb pb rs R A K vals m' ∧ rootT A K vals = acc.trie ∧ BatchMem acc m') := by
  sorry

theorem batch_twp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat}
    (h : TrieSt cb pb rs R A K (vals0 pb A) m) {acc : Acc}
    (hr : runBatch (claimOf cb).ctx (rootT A K (vals0 pb A)) rs = some acc) :
    twp P (Inp pub cb pb) pBatch m (fun m' c => ∃ vals, TrieSt cb pb rs R A K vals m' ∧
      rootT A K vals = acc.trie ∧ BatchMem acc m' ∧ c ≤ 20000000) := by
  sorry

end

end ReexecNpai
