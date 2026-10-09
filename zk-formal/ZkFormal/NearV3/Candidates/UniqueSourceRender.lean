import ZkFormal.NearV3.Candidates.UniqueSourceCharge
namespace ZkFormal.NearV3.Candidates.UniqueSourceRender
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Rcpt.Candidates Render.SrcpGen

/-- Corrected accumulator on the unchanged logical source row inventory. -/
def counter (bs : List SrcpB) (pos : Nat) : Nat :=
  if pos<DedupRender.R bs then
    let r:=(DedupRender.recs bs).getD pos default
    let B:=bs.getD r.1 default
    let before:=UniqueSourceCharge.size (bs.take r.1)
    match r.2 with
    | .root => before+if B.dup then 0 else B.L+44
    | .leaf _ => before+B.L+44
    | .path i _ => before+B.L+44+33*(i+1)
  else UniqueSourceCharge.size bs

def cell (bs : List SrcpB) (rep : Nat→Bool) (pos x : Nat) : Nat :=
  if x=SrcpV3.sz then counter bs pos else DedupRender.cell bs rep pos x

theorem non_size (bs : List SrcpB) (rep : Nat→Bool) (pos x : Nat) (hx : x≠SrcpV3.sz) :
    cell bs rep pos x=DedupRender.cell bs rep pos x := by simp [cell,hx]

theorem padding (bs : List SrcpB) (rep : Nat→Bool) (pos : Nat) (hp : DedupRender.R bs≤pos) :
    cell bs rep pos SrcpV3.sz=UniqueSourceCharge.size bs := by simp [cell,counter,show ¬pos<DedupRender.R bs by omega]

/-- An expression is independent of the changed size accumulator, on both rows. -/
def sizeFree : Expr→Bool
  | .col i _ => i != SrcpV3.sz
  | .add a b | .mul a b => sizeFree a && sizeFree b
  | .neg a => sizeFree a
  | _ => true

theorem eval_agrees (a : Env Fp) (cols : Nat→Bool→Fp)
    (hc : ∀i nx,i≠SrcpV3.sz→a.col i nx=cols i nx)
    (e : Expr) (he : sizeFree e=true) : e.evalWith a=e.evalWith {a with col:=cols} := by
  induction e with
  | col i nx => exact hc i nx (by simpa [sizeFree] using he)
  | add x y ix iy | mul x y ix iy =>
    have hh : sizeFree x=true ∧ sizeFree y=true := by simpa [sizeFree] using he
    simp only [Expr.evalWith,ix hh.1,iy hh.2]
  | neg x ih => simp only [Expr.evalWith,ih he]
  | isFirst | isLast | isTransition | pub | const => rfl

set_option maxRecDepth 32768 in
/-- Only the two replaced accumulator constraints inspect the SIZE column. -/
theorem unaffected_constraints :
    (DedupTable.constraints.take 51++DedupTable.constraints.drop 53).all sizeFree=true := by decide +kernel

set_option maxRecDepth 32768 in
theorem unaffected_interactions :
    ((DedupTable.interactions.filter fun i=>i.bus != B_SIZE).flatMap fun i=>i.mult++i.msg).all sizeFree=true := by decide +kernel
def trace (bs : List SrcpB) (rep : Nat→Bool) (log : Nat) : Trace Fp :=
  ⟨fun _=>log,fun _ r x=>Fp.ofNat (cell bs rep r x)⟩
def oldTrace (bs : List SrcpB) (rep : Nat→Bool) (log : Nat) : Trace Fp :=
  ⟨fun _=>log,fun _ r x=>Fp.ofNat (DedupRender.cell bs rep r x)⟩

/-- All unchanged constraints evaluate identically on the concrete new trace. -/
theorem trace_agrees (bs : List SrcpB) (rep : Nat→Bool) (log t r : Nat)
    (pub : List Fp) (e : Expr) (he : sizeFree e=true) :
    e.eval (trace bs rep log) t r pub=e.eval (oldTrace bs rep log) t r pub := by
  have hh:=eval_agrees (rowEnv (trace bs rep log) t r pub)
    (rowEnv (oldTrace bs rep log) t r pub).col
    (by intro i nx hi;cases nx <;> simp [rowEnv,trace,oldTrace,Trace.height,non_size bs rep _ i hi]) e he
  exact hh

end ZkFormal.NearV3.Candidates.UniqueSourceRender
