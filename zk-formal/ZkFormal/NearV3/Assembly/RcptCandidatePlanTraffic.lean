import ZkFormal.NearV3.Assembly.RcptCandidateIndexedTrafficPerm
-- Source PlanTraffic.lean SHA256: fe211947eaa4da102d597592c8dae5bd0f0a43011d27d6ee799d3725576c1c5e.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.IndexedTrafficPerm

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Actual receipt fields partition its physical interval in serialization order. -/
theorem plan_consecutive (y : RS) :
    Consec y.s ((plan y.h y.Lp y.Lv y.Ls y.kt).map fun f => (y.s+f.2.1,f.2.2)) := by
  cases he : y.h <;> simp [plan,Consec,hN,Vt,Nat.add_assoc] <;> omega

theorem plan_end (y : RS) :
    segEnd y.s ((plan y.h y.Lp y.Lv y.Ls y.kt).map fun f => (y.s+f.2.1,f.2.2))=y.s+y.tot := by
  cases he : y.h <;> simp [plan,segEnd,hN,RS.tot,total,he,Nat.add_assoc] <;> omega

/-- Generic traffic decomposition into actual receipt fields; field-local proofs
can subsequently reorder only messages, never omit or duplicate physical rows. -/
theorem plan_traffic {α : Type} (y : RS) (f : Nat→List α) :
    (List.range' y.s y.tot).flatMap f=
      (plan y.h y.Lp y.Lv y.Ls y.kt).flatMap
        (fun fld => (List.range' (y.s+fld.2.1) fld.2.2).flatMap f) := by
  have hh := range'_segs ((plan y.h y.Lp y.Lv y.Ls y.kt).map fun f => (y.s+f.2.1,f.2.2)) y.s (plan_consecutive y)
  rw [plan_end,Nat.add_sub_cancel_left] at hh
  rw [hh]
  simp only [List.flatMap_map,List.flatMap_assoc]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
