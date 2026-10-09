import ZkFormal.NearV3.Candidates.ProcActualMemoryChainSegments
import ZkFormal.NearV3.Candidates.ProcActualMemoryComparisonInventory
namespace ZkFormal.NearV3.Candidates.ProcActualMemoryChainBounds
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete

def finalW (w : Nat) : List Gen.MOp→Nat
  | []=>w
  | o::os=>finalW o.w os

theorem final_eq (w : Nat) (os : List Gen.MOp) :
    finalW w os=(match os.getLast? with |some o=>o.w |none=>w) := by
  induction os generalizing w with
  | nil=>rfl
  | cons o os ih=>
    cases os with
    | nil=>rfl
    | cons p ps=>
      rw [finalW,ih,List.getLast?_cons_cons]
      cases he:(p::ps).getLast? with
      | none=>simp_all
      | some z=>rfl

theorem step (g : Gen.Seg) (v w : Nat) (o : Gen.MOp) (h:OpOk g v w o) :
    o.v≤v ∧ w≤o.w := by
  rcases h.kind with hr|hg
  · have hh:=h.rd hr;rw [hh.1,hh.2.1,h.vin,h.wp];exact ⟨Nat.le_refl _,Nat.le_refl _⟩
  · have hh:=h.gr hg
    rw [hh.2.2.2.1,hh.2.2.2.2,h.vin,h.wp]
    constructor
    · split <;> (try split) <;> omega
    · omega

theorem bounds (g : Gen.Seg) (v w : Nat) (os : List Gen.MOp) (h:OpsOk g v w os) :
    w≤finalW w os ∧ ∀o∈os,o.vin≤v ∧ o.v≤v ∧ o.wp≤finalW w os ∧ o.w≤finalW w os := by
  induction os generalizing v w with
  | nil=>exact ⟨Nat.le_refl _,by simp⟩
  | cons o os ih=>
    have hh:=step g v w o h.1
    have ht:=ih o.v o.w h.2
    refine ⟨Nat.le_trans hh.2 ht.1,?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl|hq
    · exact ⟨by rw [h.1.vin];exact Nat.le_refl _,hh.1,by rw [h.1.wp];exact Nat.le_trans hh.2 ht.1,ht.1⟩
    · have hq':=ht.2 q hq
      exact ⟨Nat.le_trans hq'.1 hh.1,Nat.le_trans hq'.2.1 hh.1,hq'.2.2⟩

theorem segment_bounds (g : Gen.Seg) (h:ProcActualMemoryChainSegments.SegChain g) :
    g.w0≤g.wfin ∧ ∀o∈g.ops,o.vin≤g.v0 ∧ o.v≤g.v0 ∧ o.wp≤g.wfin ∧ o.w≤g.wfin := by
  have he:finalW g.w0 g.ops=g.wfin:=final_eq _ _
  rw [←he]
  exact bounds g g.v0 g.w0 g.ops h
end ZkFormal.NearV3.Candidates.ProcActualMemoryChainBounds
