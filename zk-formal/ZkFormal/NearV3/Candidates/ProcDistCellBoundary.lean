import ZkFormal.NearV3.Candidates.ProcDistCellEndFlag
namespace ZkFormal.NearV3.Candidates.ProcDistCellBoundary
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistCellRow
attribute [local irreducible] ProcDistCellRow.row
set_option maxRecDepth 32768

def Next (tv n i j:Nat)(tr:Trace Fp)(t r:Nat) : Prop :=
  (j+1=n→i+1≠n→
    tr.cell t ((r+1)%tr.height t) Dist.kGH=1 ∧
    tr.cell t ((r+1)%tr.height t) Dist.a=Fp.ofNat (i+1) ∧
    tr.cell t ((r+1)%tr.height t) Dist.tau=Fp.ofNat tv ∧
    tr.cell t ((r+1)%tr.height t) Dist.nn=Fp.ofNat n) ∧
  (j+1=n→i+1=n→
    tr.cell t ((r+1)%tr.height t) Dist.kp=0 ∧
    (tr.cell t ((r+1)%tr.height t) Dist.act=0 ∨
      tr.cell t ((r+1)%tr.height t) Dist.kSh=1 ∧
      tr.cell t ((r+1)%tr.height t) Dist.side=0 ∧
      tr.cell t ((r+1)%tr.height t) Dist.a=0))

theorem physical (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]!)
    (hnext:Next tv n i j tr t r) :
    ∀e∈Dist.cGrid.drop 34,e.eval tr t r pub=0 := by
  let rn:=(r+1)%tr.height t
  have ho:=ProcDistCellOutputCells.fields ids tv n i j sv rr n1 l1 n2 l2 allowed
  have hp:=ProcDistCellPosition.fields ids tv n i j sv rr n1 l1 n2 l2 allowed
  have hk:tr.cell t r Dist.kC=1:=by rw [hrow,ho.2.2.1];rfl
  have ha:tr.cell t r Dist.a=Fp.ofNat i:=by rw [hrow,ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have ht:tr.cell t r Dist.tau=Fp.ofNat tv:=by rw [hrow,hp.1]
  have hn:tr.cell t r Dist.nn=Fp.ofNat n:=by rw [hrow,ho.2.2.2.2.1]
  have he1:tr.cell t r Dist.e1=(if j+1=n then 1 else 0):=by rw [hrow,hp.2];split <;> rfl
  have he2:tr.cell t r Dist.e2=(if i+1=n then 1 else 0):=by
    rw [hrow,ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1];split <;> rfl
  have heI:tr.cell t r Dist.eI=(if j+1=n then 1 else 0)*(if i+1=n then 1 else 0):=by
    rw [hrow,ProcDistCellEndFlag.cell,←ofNat_mul']
    by_cases hj:j+1=n <;> by_cases hi:i+1=n <;> simp only [hj,hi,ite_true,ite_false] <;> rfl
  clear ho hp hrow
  have headerGate (v:Fp)(hv:j+1=n→i+1≠n→v=0) :
      tr.cell t r Dist.kC*tr.cell t r Dist.e1*((1 + -tr.cell t r Dist.e2)*v)=0 := by
    rw [hk,he1,he2]
    by_cases hj:j+1=n
    · rw [if_pos hj]
      by_cases hi:i+1=n
      · rw [if_pos hi];grind only
      · rw [if_neg hi,hv hj hi];grind only
    · rw [if_neg hj];grind only
  have finalGate (v:Fp)(hv:j+1=n→i+1=n→v=0) :tr.cell t r Dist.eI*v=0 := by
    rw [heI]
    by_cases hj:j+1=n
    · rw [if_pos hj]
      by_cases hi:i+1=n
      · rw [if_pos hi,hv hj hi];grind only
      · rw [if_neg hi];grind only
    · rw [if_neg hj];grind only
  simp only [Dist.cGrid,Dist.instCols,List.cons_append,List.nil_append,List.map_cons,List.map_nil,
    List.drop_succ_cons,List.drop_zero,List.forall_mem_cons]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,by simp⟩
  · change tr.cell t r Dist.kC*tr.cell t r Dist.e1*((1 + -tr.cell t r Dist.e2)*(1 + -tr.cell t rn Dist.kGH))=0
    apply headerGate
    intro hj hi;rw [(hnext.1 hj hi).1];grind only
  · change tr.cell t r Dist.kC*tr.cell t r Dist.e1*((1 + -tr.cell t r Dist.e2)*(tr.cell t rn Dist.a + -(tr.cell t r Dist.a+1)))=0
    apply headerGate
    intro hj hi;rw [(hnext.1 hj hi).2.1,ha,←ofNat_add']
    change (Fp.ofNat i+1)+-(Fp.ofNat i+1)=0;grind only
  · change tr.cell t r Dist.kC*tr.cell t r Dist.e1*((1 + -tr.cell t r Dist.e2)*(tr.cell t rn Dist.tau + -tr.cell t r Dist.tau))=0
    apply headerGate
    intro hj hi;rw [(hnext.1 hj hi).2.2.1,ht];grind only
  · change tr.cell t r Dist.kC*tr.cell t r Dist.e1*((1 + -tr.cell t r Dist.e2)*(tr.cell t rn Dist.nn + -tr.cell t r Dist.nn))=0
    apply headerGate
    intro hj hi;rw [(hnext.1 hj hi).2.2.2,hn];grind only
  · change tr.cell t r Dist.eI + -(tr.cell t r Dist.kC*tr.cell t r Dist.e1*tr.cell t r Dist.e2)=0
    rw [heI,hk,he1,he2];grind only
  · change tr.cell t r Dist.eI*tr.cell t rn Dist.act*(1 + -tr.cell t rn Dist.kSh)=0
    have h:=finalGate (tr.cell t rn Dist.act*(1 + -tr.cell t rn Dist.kSh)) (by
      intro hj hi
      rcases (hnext.2 hj hi).2 with hz|⟨hz,_,_⟩ <;> rw [hz] <;> grind only)
    grind only
  · change tr.cell t r Dist.eI*tr.cell t rn Dist.act*tr.cell t rn Dist.side=0
    have h:=finalGate (tr.cell t rn Dist.act*tr.cell t rn Dist.side) (by
      intro hj hi
      rcases (hnext.2 hj hi).2 with hz|⟨_,hz,_⟩ <;> rw [hz] <;> grind only)
    grind only
  · change tr.cell t r Dist.eI*tr.cell t rn Dist.act*tr.cell t rn Dist.a=0
    have h:=finalGate (tr.cell t rn Dist.act*tr.cell t rn Dist.a) (by
      intro hj hi
      rcases (hnext.2 hj hi).2 with hz|⟨_,_,hz⟩ <;> rw [hz] <;> grind only)
    grind only
  · change tr.cell t r Dist.eI*tr.cell t rn Dist.kp=0
    exact finalGate _ (fun hj hi=>(hnext.2 hj hi).1)
end ZkFormal.NearV3.Candidates.ProcDistCellBoundary
