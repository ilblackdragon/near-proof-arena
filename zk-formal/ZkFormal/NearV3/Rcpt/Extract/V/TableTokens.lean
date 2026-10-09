import ZkFormal.NearV3.Rcpt.Extract.V.TokenList

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Flattened semantic receipts preserve the actual physical layout order. -/
theorem flat_views (tr : Trace Fp) (tt : Nat) (bs : List ListBlock) :
    flatR (bs.map (ListBlock.view tr tt))=(bs.flatMap ListBlock.receipts).map (rcptOf tr tt) := by
  simp [flatR,ListBlock.view,ListBlock.viewReceipts,List.map_flatMap,List.flatMap_map,Function.comp_def]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Complete table token/Wf field: one sequence, zero initialization, every globally
indexed receipt well formed, and the exact final public burnt balance. -/
theorem ListChain.view_tokens {e : Nat} {bs : List ListBlock} (hc : ListChain tr tt 0 bs e) :
    let ls := bs.map (ListBlock.view tr tt)
    ∃ toks : List Nat,toks.length=(flatR ls).length+1 ∧ toks.head?=some 0 ∧
      (∀ r,(hr:r<(flatR ls).length) →
        (flatR ls)[r].Wf r (pubBytes pub PH_GP 16) (toks.getD r 0) (toks.getD (r+1) 0)) ∧
      ((∀ i,i<16 → pubNat pub (PH_BURNT+i)<256) →
        toks.getD (flatR ls).length 0=leN' (pubBytes pub PH_BURNT 16)) := by
  intro ls
  let xs := bs.flatMap ListBlock.receipts
  have hf : flatR ls=xs.map (rcptOf tr tt) := flat_views tr tt bs
  have hl : (flatR ls).length=xs.length := by rw [hf,List.length_map]
  have hr := hc.zero_token_run hL
  refine ⟨tokenList tr tt xs 0,?_,rfl,?_,?_⟩
  · rw [tokenList_length,hl]
  · intro r hr'
    have hx : r<xs.length := by omega
    obtain ⟨j,hj,k,hk,hindex,hvalue⟩ := receipt_flat_index bs r hx
    have hw := hc.indexed_wf hL j hj k hk
    have hv : (flatR ls)[r]=rcptOf tr tt xs[r] := by simp only [hf,List.getElem_map]
    rw [hr.input r hx,tokenList_output r hx,hv]
    rw [hvalue,hindex]
    exact hw
  · intro hb
    rw [hl,hr.last]
    exact hc.final_token_value hL hb

end ZkFormal.NearV3.RcptV3Proof
