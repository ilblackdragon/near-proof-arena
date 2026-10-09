import ZkFormal.NearV3.Candidates.ProcPriorOverlayPadding
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayWindowLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ProcPriorCells ProcPriorVertical4Linear

/-- Reuse physical log22 legality strictly before a shorter window's final
padding row; no arbitrary extension/truncation of valid traces is used. -/
theorem interior_env (tr : Trace Fp) (tt r : Nat) (hlog:tr.log tt=22)
    (hr:r+1<2^22) :
    rowEnv tr tt r []=env (tr.cell tt r) (tr.cell tt (r+1)) (if r=0 then 1 else 0) 0 1 := by
  simp only [rowEnv,Trace.height,hlog,Nat.mod_eq_of_lt hr,env,List.getD_nil]
  have hlast:¬r+1=2^22:=by omega
  simp only [hlast,ite_false]
  congr 1
  funext c nx
  cases nx <;> rfl

def localEnv (data : Nat→Nat→Fp) (size r : Nat) : Env Fp :=
  env (data r) (data (r+1)) (if r=0 then 1 else 0)
    (if r+1=size then 1 else 0) (if r+1=size then 0 else 1)

/-- Actual component Local plus a proved zero suffix establishes its honest
short window. Only final padding sees changed next-stage cells. -/
theorem constraints (T : Air.Table) (hT:T∈components) (tr : Trace Fp) (tt : Nat)
    (hlog:tr.log tt=22) (hlocal:TableLocal T tr tt [])
    (used size : Nat) (hused:used<size) (hsize:size≤2^22)
    (hz:∀r,used≤r→tr.cell tt r=fun _=>0)
    (r : Nat) (hr:r<size) (e : Expr) (he:e∈T.constraints) :
    e.evalWith (localEnv (tr.cell tt) size r)=0 := by
  by_cases hlast:r+1=size
  · have hp:used≤r:=by omega
    unfold localEnv
    rw [hz r hp]
    apply ProcPriorOverlayPadding.constraints T hT
    · exact Or.inl (by simp only [hlast,ite_true])
    · exact he
  · have hnext:r+1<2^22:=by omega
    have h:=hlocal.constr r (by change r<2^(tr.log tt);rw [hlog];omega) e he
    change e.evalWith (rowEnv tr tt r [])=0 at h
    rw [interior_env tr tt r hlog hnext] at h
    simpa only [localEnv,hlast,ite_false] using h

theorem bits (T : Air.Table) (hT:T∈components) (tr : Trace Fp) (tt : Nat)
    (hlog:tr.log tt=22) (hlocal:TableLocal T tr tt [])
    (used size : Nat) (hused:used<size) (hsize:size≤2^22)
    (hz:∀r,used≤r→tr.cell tt r=fun _=>0)
    (r : Nat) (hr:r<size) (i : Interaction) (hi:i∈T.interactions) (e : Expr) (he:e∈i.mult) :
    e.evalWith (localEnv (tr.cell tt) size r)=0 ∨ e.evalWith (localEnv (tr.cell tt) size r)=1 := by
  by_cases hlast:r+1=size
  · have hp:used≤r:=by omega
    unfold localEnv
    rw [hz r hp]
    exact Or.inl (ProcPriorOverlayPadding.multiplicity T hT _ _ _ _ i hi e he)
  · have hnext:r+1<2^22:=by omega
    have h:=hlocal.bits r (by change r<2^(tr.log tt);rw [hlog];omega) i hi e he
    change e.evalWith (rowEnv tr tt r [])=0 ∨ e.evalWith (rowEnv tr tt r [])=1 at h
    rw [interior_env tr tt r hlog hnext] at h
    simpa only [localEnv,hlast,ite_false] using h
end ZkFormal.NearV3.Candidates.ProcPriorOverlayWindowLocal
