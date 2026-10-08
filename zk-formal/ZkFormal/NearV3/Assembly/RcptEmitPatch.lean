import ZkFormal.NearV3.Assembly.RcptPhysicalRegs

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

set_option maxRecDepth 4096 in
theorem constraint_group_counts :
    [cStates.length,cEmit.length,cRegs.length,cChars.length,cKey.length,cSys.length,
      cRoute.length,cGas.length,cDep.length,cEnd.length,constraints.length]=
    [248,189,200,61,49,14,18,40,39,23,881] := by decide

def emissionColumn (c : Nat) : Bool := decide (31≤c ∧ c≤42)
def noEmissionExpr : Expr→Bool
  | .col c _=> !emissionColumn c
  | .add a b | .mul a b=>noEmissionExpr a && noEmissionExpr b
  | .neg a=>noEmissionExpr a
  | _=>true

structure EmissionValues where
  id : Fp
  pos : Fp
  value : Fp
  gate : Fp

def emissionValues (tr : Trace Fp) (pub : List Fp) (t pos state slot : Nat) : EmissionValues :=
  match emits.find? (fun p=>p.1==state) with
  | none=>⟨0,0,0,0⟩
  | some (_,ems)=>match ems[slot]? with
    | none=>⟨0,0,0,0⟩
    | some (id,p,v,g)=>⟨id.eval tr t pos pub,p.eval tr t pos pub,v.eval tr t pos pub,g.eval tr t pos pub⟩

/-- Overwrite exactly the twelve emission columns; all other native receipt
cells and the table height are preserved. -/
def emissionPatch (base : Trace Fp) (pub : List Fp) (stateAt : Nat→Nat→Nat) : Trace Fp :=
  ⟨base.log,fun t pos c=>if emissionColumn c then
    let v := emissionValues base pub t pos (stateAt t pos) ((c-31)/4)
    [v.id,v.pos,v.value,v.gate].getD ((c-31)%4) 0
    else base.cell t pos c⟩

theorem emissionPatch_other (base : Trace Fp) (pub : List Fp) (stateAt : Nat→Nat→Nat)
    (t pos c : Nat) (hc : emissionColumn c=false) :
    (emissionPatch base pub stateAt).cell t pos c=base.cell t pos c := by simp [emissionPatch,hc]

theorem emissionPatch_eval (base : Trace Fp) (pub : List Fp) (stateAt : Nat→Nat→Nat)
    (t pos : Nat) (e : Expr) (he : noEmissionExpr e=true) :
    e.eval (emissionPatch base pub stateAt) t pos pub=e.eval base t pos pub := by
  induction e with
  | const | pub | isFirst | isLast | isTransition => rfl
  | col c nx =>
    have hc : emissionColumn c=false := by simpa [noEmissionExpr] using he
    cases nx <;> exact emissionPatch_other base pub stateAt _ _ c hc
  | add a b ia ib =>
    have hh : noEmissionExpr a=true ∧ noEmissionExpr b=true := by simpa only [noEmissionExpr,Bool.and_eq_true] using he
    simp only [eval_add,ia hh.1,ib hh.2]
  | mul a b ia ib =>
    have hh : noEmissionExpr a=true ∧ noEmissionExpr b=true := by simpa only [noEmissionExpr,Bool.and_eq_true] using he
    simp only [eval_mul,ia hh.1,ib hh.2]
  | neg a ia => simp only [eval_neg,ia he]

set_option maxRecDepth 4096 in
theorem cRegs_noEmission : cRegs.all noEmissionExpr=true := by decide

/-- The emission extension preserves the already proved physical register group. -/
theorem emissionPatch_cRegs (base : Trace Fp) (pub : List Fp) (stateAt : Nat→Nat→Nat)
    (t pos : Nat) (h : ∀e∈cRegs,e.eval base t pos pub=0) :
    ∀e∈cRegs,e.eval (emissionPatch base pub stateAt) t pos pub=0 := by
  intro e he
  rw [emissionPatch_eval base pub stateAt t pos e (List.all_eq_true.mp cRegs_noEmission e he)]
  exact h e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
