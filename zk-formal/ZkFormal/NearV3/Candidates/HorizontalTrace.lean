import ZkFormal.NearV3.Candidates.HorizontalTables
import ZkFormal.Near.Extract.Common

namespace ZkFormal.NearV3.Candidates.HorizontalTrace
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near HorizontalTables
set_option maxRecDepth 32768

def project (off : Nat) (tr : Trace Fp) : Trace Fp :=
  {log:=tr.log,cell:=fun t r i => tr.cell t r (off+i)}

theorem expression_eval (tr : Trace Fp) (t r off : Nat) (pub : List Fp) (e : Expr) :
    (expression off e).eval tr t r pub=e.eval (project off tr) t r pub := by
  unfold Expr.eval
  rw [HorizontalTables.expression_eval]
  rfl

/-- Every located component retains its original local legality at the same height. -/
theorem project_local {ts : List Air.Table} {T : Air.Table} {off t : Nat}
    {tr : Trace Fp} {pub : List Fp}
    (hloc : shifted off T∈layout 0 ts) (hcap : T.maxLog=22)
    (h : TableLocal (fuse ts) tr t pub) : TableLocal T (project off tr) t pub := by
  refine ⟨h.log_ge,?_,?_,?_⟩
  · change tr.log t≤T.maxLog
    rw [hcap]
    exact h.log_le
  · intro r hr e he
    rw [← expression_eval]
    apply h.constr r hr
    exact List.mem_flatMap.mpr ⟨shifted off T,hloc,List.mem_map.mpr ⟨e,he,rfl⟩⟩
  · intro r hr i hi b hb
    have hi' : interaction off i∈(fuse ts).interactions :=
      List.mem_flatMap.mpr ⟨shifted off T,hloc,List.mem_map.mpr ⟨i,hi,rfl⟩⟩
    have hb' : expression off b∈(interaction off i).mult := List.mem_map.mpr ⟨b,hb,rfl⟩
    simpa only [expression_eval] using h.bits r hr _ hi' _ hb'

/-- An executable two-block assembly; later blocks begin after the left width. -/
def join (width : Nat) (a b : Trace Fp) : Trace Fp :=
  {log:=a.log,cell:=fun t r i => if i<width then a.cell t r i else b.cell t r (i-width)}

theorem join_left_eval (a b : Trace Fp) (t r width : Nat) (pub : List Fp)
    (e : Expr) (he : e.colBound≤width) :
    e.eval (join width a b) t r pub=e.eval a t r pub := by
  induction e with
  | col i nx =>
    have hi : i<width := by change i+1≤width at he; omega
    simp only [Expr.eval,Expr.evalWith,rowEnv,join,if_pos hi]
    rfl
  | add a0 b0 ia ib =>
    change a0.eval _ _ _ _ + b0.eval _ _ _ _ = _
    rw [ia (by change max a0.colBound b0.colBound≤width at he; omega),
      ib (by change max a0.colBound b0.colBound≤width at he; omega)]
    rfl
  | mul a0 b0 ia ib =>
    change a0.eval _ _ _ _ * b0.eval _ _ _ _ = _
    rw [ia (by change max a0.colBound b0.colBound≤width at he; omega),
      ib (by change max a0.colBound b0.colBound≤width at he; omega)]
    rfl
  | neg a0 ia => exact congrArg Neg.neg (ia he)
  | _ => rfl

theorem join_right_eval (a b : Trace Fp) (t r width : Nat) (pub : List Fp)
    (hl : a.log t=b.log t) (e : Expr) :
    (expression width e).eval (join width a b) t r pub=e.eval b t r pub := by
  unfold Expr.eval
  rw [HorizontalTables.expression_eval]
  congr 1
  unfold rowEnv join Trace.height
  simp only [hl]
  congr 1
  funext i nx
  simp [show ¬width+i<width by omega]
end ZkFormal.NearV3.Candidates.HorizontalTrace
