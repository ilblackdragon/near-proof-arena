import ZkFormal.NearV3.Assembly.RcptCandidateRowT
import ZkFormal.NearV3.Rcpt.Extract.V.Of
-- Original Of.lean SHA256: 87e3df712b2fb99595dfe4e25fd09af7c8df65f1415ec691070d2cd473325aa8. Reuses exact original receipt view definitions.
namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open RcptV3Proof RcptSkeleton
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- **An always-on emission slot over a field is an `emitAt` chunk.** -/
theorem fld_chunk {s r0 L X : Nat} {ems : List Em} {e : Nat} {id p v g : Expr}
    (hH : r0 + L ≤ tr.height tt) (F : RFld tr tt s r0 L X) (hX : (X, ems) ∈ emits) (he : e < 3)
    (hs : ems[e]? = some (id, p, v, g)) (idN off : Nat) (bytes : List Nat) (hlen : bytes.length = L)
    (hg : ∀ k, k < L → g.eval tr tt (r0 + k) pub = 1)
    (hid : ∀ k, k < L → id.eval tr tt (r0 + k) pub = ((idN : Nat) : Fp))
    (hp : ∀ k, k < L → p.eval tr tt (r0 + k) pub = ((off + k : Nat) : Fp))
    (hv : ∀ k, k < L → v.eval tr tt (r0 + k) pub = ((bytes.getD k 0 : Nat) : Fp)) :
    (List.range' r0 L).flatMap (fun q => slotT tr tt q e) = (emitAt idN off bytes).map Msg.toFp := by
  rw [List.range'_eq_map_range, List.flatMap_map, emitAt, hlen, List.map_map]
  rw [flatMap_congr' (G := fun k => [[((idN : Nat) : Fp), ((off + k : Nat) : Fp), ((bytes.getD k 0 : Nat) : Fp)]])
    (fun k hk => by
      rw [List.mem_range] at hk
      rw [emit_some hL (by omega) hX (F.fld.st k hk) he hs, if_pos (hg k hk), hid k hk, hp k hk, hv k hk])]
  rw [← map_eq_flatMap]
  apply List.map_congr_left; intro k _
  simp [Msg.toFp, natCast_eq]

/-- A slot that is off over a field. -/
theorem fld_chunk_off {s r0 L X : Nat} {ems : List Em} {e : Nat} {id p v g : Expr}
    (hH : r0 + L ≤ tr.height tt) (F : RFld tr tt s r0 L X) (hX : (X, ems) ∈ emits) (he : e < 3)
    (hs : ems[e]? = some (id, p, v, g)) (hg : ∀ k, k < L → g.eval tr tt (r0 + k) pub = 0) :
    (List.range' r0 L).flatMap (fun q => slotT tr tt q e) = [] := by
  rw [List.range'_eq_map_range, List.flatMap_map]
  rw [flatMap_congr' (G := fun _ => []) (fun k hk => by
      rw [List.mem_range] at hk
      rw [emit_some hL (by omega) hX (F.fld.st k hk) he hs, if_neg (by rw [hg k hk]; exact fp_zero_ne_one)]),
    flatMap_nil_fun]

/-- A missing slot. -/
theorem fld_chunk_none {s r0 L X : Nat} {ems : List Em} {e : Nat}
    (hH : r0 + L ≤ tr.height tt) (F : RFld tr tt s r0 L X) (hX : (X, ems) ∈ emits) (he : e < 3)
    (hs : ems[e]? = none) : (List.range' r0 L).flatMap (fun q => slotT tr tt q e) = [] := by
  rw [List.range'_eq_map_range, List.flatMap_map]
  rw [flatMap_congr' (G := fun _ => []) (fun k hk => by
      rw [List.mem_range] at hk
      exact emit_none hL (by omega) hX (F.fld.st k hk) he hs), flatMap_nil_fun]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3

/-- The three slots of a field's rows, up to permutation. -/
theorem slots_perm (tr : Trace Fp) (tt r0 L : Nat) :
    ((List.range' r0 L).flatMap fun q => (List.range 3).flatMap (slotT tr tt q)).Perm
      ((List.range' r0 L).flatMap (fun q => slotT tr tt q 0) ++ (List.range' r0 L).flatMap (fun q => slotT tr tt q 1) ++
        (List.range' r0 L).flatMap (fun q => slotT tr tt q 2)) := by
  have h3 : ∀ q, (List.range 3).flatMap (slotT tr tt q) = slotT tr tt q 0 ++ (slotT tr tt q 1 ++ slotT tr tt q 2) := by
    intro q; simp [List.range_succ]
  simp only [h3]
  refine (flatMap_append_perm _ _ _).trans ?_
  rw [List.append_assoc]
  exact List.Perm.append_left _ (flatMap_append_perm _ _ _)

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
