import ZkFormal.NearV3.Candidates.ProcConcatRows
import ZkFormal.NearV3.Candidates.ProcBoundaryLocal
namespace ZkFormal.NearV3.Candidates.ProcConcatPadding
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Sched.Complete
open ProcConcatGeometry
open ZkFormal.Chacha.Table.E

theorem inactive (rs : List Run) (r : Nat) (hr : (rows rs).length≤r) :
    atRow rs r=padPV ∨ ∃R,atRow rs r=tailV R := by
  rw [atRow,dif_neg (by omega)]
  split
  · unfold tail
    split
    · exact Or.inl rfl
    · rename_i R _
      exact Or.inr ⟨R,rfl⟩
  · exact Or.inl rfl

theorem inactive_flags (rs : List Run) (r : Nat) (hr : (rows rs).length≤r) :
    ProcOtherRows.NonKey (atRow rs r) ∧ (atRow rs r).le=0 ∧
      (atRow rs r).kH=0 ∧ (atRow rs r).kE=0 := by
  rcases inactive rs r hr with hv | ⟨R,hv⟩ <;>
    simp [hv,ProcOtherRows.NonKey,padPV,tailV,zeroV]

theorem next_flags (rs : List Run) (r t : Nat) (hrow : (rows rs).length≤r) (hr : r<2^22) :
    (trace rs).cell t ((r+1)%(trace rs).height t) Proc.kH=0 ∧
    (trace rs).cell t ((r+1)%(trace rs).height t) Proc.kE=0 := by
  change Fp.ofNat ((atRow rs ((r+1)%(2^22))).cell Proc.kH)=0 ∧
    Fp.ofNat ((atRow rs ((r+1)%(2^22))).cell Proc.kE)=0
  by_cases hl : r+1<2^22
  · rw [Nat.mod_eq_of_lt hl]
    have hs := inactive_flags rs (r+1) (by omega)
    simp [PV.cell,Proc.kH,Proc.kE,hs.2.2.1,hs.2.2.2]
    rfl
  · have he : r+1=2^22 := by omega
    rw [he,Nat.mod_self,ProcConcatRows.first]
    cases rs <;> exact ⟨rfl,rfl⟩

theorem pad_entry (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀c,tr.cell t r c=Fp.ofNat (padPV.cell c)) :
    ∀e∈Proc.cEnt,e.eval tr t r pub=0 := by
  simp only [Proc.cEnt,List.forall_mem_cons,List.forall_mem_nil]
  simp [Proc.mul3,Proc.notE,sub,c,n,k,Expr.eval,Expr.evalWith,rowEnv,hc,PV.cell,
    Proc.kE,Proc.le,Proc.x,Proc.Lr,Proc.lastf,Proc.rem,Proc.irem,Proc.ok,Proc.cS,Proc.cR,Proc.cL,
    Proc.za,Proc.alOut,Proc.ia,Proc.zn,Proc.z,Proc.pm,Proc.cg,Proc.kH,Proc.zk,
    Proc.cx,Proc.Kq,Proc.cy,Proc.K,Proc.ts,padPV,zeroV]
  have cast_eq (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  simp only [cast_eq]
  repeat apply And.intro <;> grind

theorem padding_groups (rs : List Run) (r t : Nat) (pub : List Fp)
    (hrow : (rows rs).length≤r) (hr : r<2^22) :
    ∀e∈ProcBoundaryRepair.cKey++Proc.cHdr++Proc.cEnt,e.eval (trace rs) t r pub=0 := by
  have hs := inactive_flags rs r hrow
  have hn := next_flags rs r t hrow hr
  have hc (c : Nat) : (trace rs).cell t r c=Fp.ofNat ((atRow rs r).cell c) := rfl
  simp only [List.forall_mem_append]
  refine ⟨⟨?_,?_⟩,?_⟩
  · exact ProcBoundaryLocal.old_key _ _ _ _ (ProcNonKey.key_eval _ hs.1 _ _ _ _ hc
      (Or.inr hs.2.1) (Or.inl hs.2.2))
  · exact ProcHeaderPadding.quiet _ ⟨hs.2.2.1,hs.2.2.2,hs.1.1,hs.1.2.2.1,hs.2.1⟩
      _ _ _ _ hc hn.1 hn.2
  · rcases inactive rs r hrow with hv | ⟨R,hv⟩
    · exact pad_entry _ _ _ _ (by simpa only [hv] using hc)
    · exact ProcNonEntry.constraints R _ (Or.inr (Or.inr (Or.inl hv))) _ _ _ _ hc
end ZkFormal.NearV3.Candidates.ProcConcatPadding
