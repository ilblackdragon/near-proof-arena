import ZkFormal.NearV3.Candidates.UniqueSourcePartitionTransfer
namespace ZkFormal.NearV3.Candidates.UniqueSourceSoundShadow
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Rcpt.Candidates

def increment (tr : Trace Fp) (tt r : Nat) : Fp :=
  tr.cell tt r SrcpV3.rt*tr.cell tt r SrcpV3.L+
    33*(tr.cell tt r SrcpV3.sf*tr.cell tt r SrcpV3.sg*(1-tr.cell tt r SrcpV3.lf))

def counter (tr : Trace Fp) (tt : Nat) : Nat→Fp
  | 0 => tr.cell tt 0 SrcpV3.L
  | r+1 => counter tr tt r+increment tr tt (r+1)

/-- An extraction-only trace restores the old accumulator. No byte bound is
claimed for this column; corrected SIZE soundness must use the original trace. -/
def shadow (tr : Trace Fp) : Trace Fp :=
  ⟨tr.log,fun tt r x=>if x=SrcpV3.sz then counter tr tt r else tr.cell tt r x⟩

def initial : Expr := .mul .isFirst (Dsl.sub (Dsl.c SrcpV3.sz) (Dsl.c SrcpV3.L))
def step : Expr := .mul .isTransition (Dsl.sub (Dsl.n SrcpV3.sz)
  (Dsl.sum [Dsl.c SrcpV3.sz,.mul (Dsl.n SrcpV3.rt) (Dsl.n SrcpV3.L),
    Dsl.smul 33 (Dsl.mul3 (Dsl.n SrcpV3.sf) (Dsl.n SrcpV3.sg) (Dsl.not (Dsl.n SrcpV3.lf)))]))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem coverage : DedupTable.constraints.all
    (UniqueSourcePartitionTransfer.covered UniqueSourceCharge.constraints [initial,step])=true := by
  decide +kernel

theorem agrees (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (e : Expr)
    (he : UniqueSourceRender.sizeFree e=true) :
    e.eval (shadow tr) tt r pub=e.eval tr tt r pub := by
  apply UniqueSourceRender.eval_agrees (rowEnv (shadow tr) tt r pub)
    (rowEnv tr tt r pub).col _ e he
  intro x nx hx
  cases nx <;> simp [rowEnv,shadow,Trace.height,hx]

theorem initial_zero (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    initial.eval (shadow tr) tt r pub=0 := by
  by_cases h : r=0
  · subst r
    simp [initial,Dsl.sub,Dsl.c,Expr.eval,Expr.evalWith,rowEnv,shadow,counter,SrcpV3.sz,SrcpV3.L]
    grind
  · simp [initial,Dsl.sub,Dsl.c,Expr.eval,Expr.evalWith,rowEnv,h]
    grind

theorem step_zero (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (hr : r<tr.height tt) :
    step.eval (shadow tr) tt r pub=0 := by
  by_cases hl : r+1=tr.height tt
  · simp [step,Expr.eval,Expr.evalWith,rowEnv,shadow,Trace.height,hl]
    grind
  · have hm : (r+1)%tr.height tt=r+1 := Nat.mod_eq_of_lt (by omega)
    change (r+1)% (2^tr.log tt)=r+1 at hm
    change r+1≠2^tr.log tt at hl
    simp [step,Dsl.sub,Dsl.sum,Dsl.c,Dsl.n,Dsl.k,Dsl.smul,Dsl.mul3,Dsl.not,
      Expr.eval,Expr.evalWith,rowEnv,shadow,Trace.height,hl,hm,counter,increment,
      SrcpV3.sz,SrcpV3.rt,SrcpV3.L,SrcpV3.sf,SrcpV3.sg,SrcpV3.lf]
    grind

/-- Recover established semantic extraction from any accepting corrected logical
trace, without asserting the old accumulator is paid by the native witness. -/
theorem old_local {tr : Trace Fp} {tt cap : Nat} {pub : List Fp}
    (h : TableLocal (UniqueSourceCharge.table cap) tr tt pub) :
    TableLocal (DedupTable.table cap) (shadow tr) tt pub := by
  refine ⟨h.log_ge,h.log_le,?_,?_⟩
  · intro r hr e he
    have hh:=List.all_eq_true.mp coverage e he
    simp only [UniqueSourcePartitionTransfer.covered,Bool.or_eq_true,Bool.and_eq_true] at hh
    rcases hh with ⟨hf,hm⟩|hm
    · obtain ⟨x,hx,hxe⟩:=List.any_eq_true.mp hm
      have hxe : e=x := of_decide_eq_true hxe
      rw [agrees tr tt r pub e hf]
      exact h.constr r hr e (hxe.symm ▸ hx)
    · obtain ⟨x,hx,hxe⟩:=List.any_eq_true.mp hm
      have hxe : e=x := of_decide_eq_true hxe
      subst e
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl
      · exact initial_zero tr tt r pub
      · exact step_zero tr tt r pub hr
  · intro r hr i hi b hb
    have hf:=List.all_eq_true.mp UniqueSourceLocal.gates_free b (List.mem_flatMap.mpr ⟨i,hi,hb⟩)
    rw [agrees tr tt r pub b hf]
    exact h.bits r hr i hi b hb
end ZkFormal.NearV3.Candidates.UniqueSourceSoundShadow
