import ZkFormal.NearV3.Assembly.RcptSystemComplete
import ZkFormal.NearV3.Rcpt.Extract.V.SignerTrafficRows

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Both directions use the actual receiver byte at the selected position;
systemAux.sx supplies this byte to signer rows. -/
def systemMessages (r : Receipt) (receiptIndex n : Nat) : List Msg :=
  ((List.range n).filter (systemLookup r)).map
    (fun i=>[receiptIndex,i,(r.receiverId.getD i 0).toNat])

theorem systemMessages_none (r : Receipt) (receiptIndex n : Nat)
    (he : systemEqual r=false) (hm : systemMismatch r=false) :
    systemMessages r receiptIndex n=[] := by
  simp [systemMessages,systemLookup,he,hm]

theorem systemMessages_balance (r : Receipt) (receiptIndex : Nat) :
    systemMessages r receiptIndex r.receiverId.length=
      systemMessages r receiptIndex r.signerId.length := by
  by_cases he : systemEqual r=true
  · rw [systemEqual_length r he]
  · by_cases hm : systemMismatch r=true
    · rw [(systemMismatch_witness r hm).2.1]
    · have he' : systemEqual r=false := Bool.eq_false_iff.mpr he
      have hm' : systemMismatch r=false := Bool.eq_false_iff.mpr hm
      rw [systemMessages_none r receiptIndex _ he' hm',systemMessages_none r receiptIndex _ he' hm']

theorem systemMessages_bound (r : Receipt) (receiptIndex n : Nat) :
    (systemMessages r receiptIndex n).length≤n := by
  simp only [systemMessages,List.length_map]
  simpa only [List.length_range] using List.length_filter_le (systemLookup r) (List.range n)

theorem systemMessages_positions (r : Receipt) (receiptIndex n : Nat) {m : Msg}
    (h : m∈systemMessages r receiptIndex n) :
    ∃i,i<n ∧ systemLookup r i=true ∧ m=[receiptIndex,i,(r.receiverId.getD i 0).toNat] := by
  obtain ⟨i,hi,he⟩ := List.mem_map.mp h
  obtain ⟨hr,hlook⟩ := List.mem_filter.mp hi
  exact ⟨i,List.mem_range.mp hr,hlook,he.symm⟩

theorem system_gt_bit (b : Bool) (m : List Fp) :
    RcptV3Proof.gt (bitCell b) m=if b then [m] else [] := by
  cases b <;> simp [RcptV3Proof.gt,bitCell]

/-- Generic physical padding transport used by the concrete bus proof. -/
theorem range_get_flatMap {α β : Type} (n : Nat) (xs : List α) (f : α→List β)
    (h : xs.length≤n) :
    (List.range n).flatMap (fun i=>match xs[i]? with | some x=>f x | none=>[])=xs.flatMap f := by
  induction n generalizing xs with
  | zero =>
    have hx : xs=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    rfl
  | succ n ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      rw [List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
      simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,Function.comp_def]
      rw [ih xs (by simpa only [List.length_cons,Nat.succ_le_succ_iff] using h)]
      rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
