import ReexecNpai.Spec.State

/-!
# Phase spec: outputs
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

section
variable {pub cb pb : Bytes}

theorem final_wp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes}
    {acc : Acc} (h : TrieSt cb pb rs R A K vals m) (hb : BatchMem acc m) (ht : rootT A K vals = acc.trie)
    (hlen : acc.outcomes.length = rs.length) (hgas : acc.gasBurnt = rs.length * Params.G)
    (htok : acc.tokensBurnt < Params.two128) :
    wp P (Inp pub cb pb) pFinal m (fun m' => Outputs.ofAcc acc = Outputs.ofClaim (claimOf cb) ∧
      m'.regs 15 = 1) := by
  sorry

theorem final_twp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes}
    {acc : Acc} (h : TrieSt cb pb rs R A K vals m) (hb : BatchMem acc m) (ht : rootT A K vals = acc.trie)
    (hlen : acc.outcomes.length = rs.length) (hgas : acc.gasBurnt = rs.length * Params.G)
    (htok : acc.tokensBurnt < Params.two128) (he : Outputs.ofAcc acc = Outputs.ofClaim (claimOf cb)) :
    twp P (Inp pub cb pb) pFinal m (fun m' c => m'.regs 15 = 1 ∧ c ≤ 20 * pb.length + 1000000) := by
  sorry

end

end ReexecNpai
