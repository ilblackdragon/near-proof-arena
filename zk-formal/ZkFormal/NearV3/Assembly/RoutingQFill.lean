import ZkFormal.NearV3.Assembly.RoutingQNormalize

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Executable bit filling, with the original q and receiver-start selectors.
Only the seven scratch entries need to be copied into an existing honest row. -/
def filledCell (Q col : Nat) : Fp :=
  if col=q then Fp.ofNat Q else
  if col=sV ∨ col=fs then 1 else
  if xb 12≤col ∧ col≤xb 18 then Fp.ofNat ((Q/2^(col-xb 12))%2) else 0

def filledTrace (Q : Nat) : Trace Fp := ⟨fun _=>1,fun _ _ c=>filledCell Q c⟩

def fillingPasses (Q : Nat) : Bool :=
  decide (qBound.eval (filledTrace Q) 0 0 []=0) &&
    (List.range 7).all fun i=>decide (filledCell Q (xb (12+i))=0 ∨ filledCell Q (xb (12+i))=1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem all_honest_fillings : (List.range 128).all fillingPasses=true := by decide

/-- Exhaustive finite proof of the exact honest bit assignment for every legal q;
no inverse or unconstrained field value is used to satisfy the new polynomial. -/
theorem honest_filling (Q : Nat) (hQ : Q<128) :
    qBound.eval (filledTrace Q) 0 0 []=0 ∧
      ∀i,i<7 → filledCell Q (xb (12+i))=0 ∨ filledCell Q (xb (12+i))=1 := by
  have h := (List.all_eq_true.mp all_honest_fillings) Q (List.mem_range.mpr hQ)
  simp only [fillingPasses,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range] at h
  exact h

end ZkFormal.NearV3.Assembly.RoutingQCandidate
