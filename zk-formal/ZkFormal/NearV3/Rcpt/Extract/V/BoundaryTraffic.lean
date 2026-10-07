import ZkFormal.NearV3.Rcpt.Extract.V.BoundaryTrafficIndex

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def boundaryMsgs (sd : Bool) (_r : Nat) (x : RcptE) : List Msg :=
  x.rlk.map fun (p,l,h,hn,u) => [BND_STRIDE*x.q+p,l,h,hn,u+(if sd then 1 else 0)]

/-- Selected records map to exactly the enabled singleton message sequence. -/
theorem filterMap_messages {α β γ : Type} (xs : List α) (p : α→Bool) (f : α→β) (g : β→γ) :
    (xs.filterMap (fun x => if p x then some (f x) else none)).map g=
      xs.flatMap (fun x => if p x then [g (f x)] else []) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [hp,ih]

theorem boundaryMsgs_view (tr : Trace Fp) (tt : Nat) (pub : List Fp) (bs : List ListBlock) (sd : Bool) :
    indexedReceiptMsgs tr tt bs (boundaryMsgs sd)=
      (if sd then rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_BND
        else rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_BND) := by
  rw [indexedReceiptMsgs_view]
  cases sd <;>
    simp only [Bool.false_eq_true,ite_false,ite_true,rcptSends3,rcptRecvs3,
      show B_BND≠B_BYTES by decide,show B_BND≠B_RCL by decide,List.nil_append]
  all_goals
    apply flatMap_congr'
    intro j _
    apply flatMap_congr'
    intro x _
    simp [rSends,rRecvs,boundaryMsgs,B_MEM,B_BYTES,B_KEYNIB,B_RIDS,B_MPOS,B_SREC,B_AKC,B_FINAL,B_DIGEST,B_BND]

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Boundary records and counter successors match every actual selected lookup. -/
theorem Layout.boundary_traffic {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt) (sd : Bool) :
    (List.range' y.s y.tot).flatMap (fun q => rowTraffic RcptV3.interactions tr tt q pub B_BND sd)=
      (boundaryMsgs sd 0 (rcptOf tr tt y)).map Msg.toFp := by
  rw [h.bnd_window hL,List.range'_eq_map_range,List.flatMap_map]
  simp only [boundaryMsgs,rcptOf,List.map_map]
  have hfilter := filterMap_messages (List.range (y.Lv+1))
    (fun k => decide (tr.cell tt (lkRow y k) gBd=1))
    (fun k => (k,cv tr tt (lkRow y k) loB,cv tr tt (lkRow y k) hiB,
      cv tr tt (lkRow y k) hnB,cv tr tt (lkRow y k) uB))
    (fun (p,l,hi,hn,u) => Msg.toFp [BND_STRIDE*cv tr tt y.s RcptV3.q+p,l,hi,hn,u+(if sd then 1 else 0)])
  simp only [decide_eq_true_eq] at hfilter
  simp only [Function.comp_def]
  rw [hfilter]
  apply flatMap_congr'
  intro k hk
  have hk := List.mem_range.mp hk
  change rowTraffic RcptV3.interactions tr tt (lkRow y k) pub B_BND sd=_
  rw [rowT_bnd]
  have hi := h.boundary_index hL k (by omega)
  simp only [gt,hi.1,hi.2]
  by_cases hg : tr.cell tt (lkRow y k) gBd=1
  · simp only [hg,ite_true,Msg.toFp,List.map_cons,List.map_nil,←natCast_eq,natCast_add,natCast_mul]
    simp only [cv,natCast_eq,Fp.ofNat_toNat]
    cases sd <;> simp only [ite_true,Bool.false_eq_true,ite_false] <;> congr 6 <;> grind
  · simp only [hg,ite_false]

/-- Both whole-table boundary lookup/counter directions equal the unchanged view. -/
theorem ListChain.boundary_traffic {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) (sd : Bool) :
    (List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_BND sd)=
      ((if sd then rcptSends3 pub (bs.map (ListBlock.view tr tt)) B_BND
        else rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_BND).map Msg.toFp) := by
  rw [←boundaryMsgs_view]
  apply h.indexed_traffic hL
  · intro B hB
    exact (h.blocks B hB).header_bnd hL sd
  · intro q hq ha
    apply bnd_silent hL hq _ sd
    have hn := noState hL hq ha
    simp only [rwE,eval_add,eval_mul,eval_c,hn sV (by simp [states]),hn sRID (by simp [states])]
    grind
  · intro j hj k hk
    have hw := (h.blocks bs[j] (List.getElem_mem hj)).layouts bs[j].receipts[k] (List.getElem_mem hk)
    exact hw.boundary_traffic hL sd

end ZkFormal.NearV3.RcptV3Proof
