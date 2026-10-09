import ZkFormal.NearV3.Render.Ups.CompactTableCandidate
import ZkFormal.NearV3.Extract.Ups.LayoutRows
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows

/-- Local candidate equations, read from arbitrary canonical rows. -/
def RowOk (C D : URow) : Prop := ∀e∈compactConstraints,e.pure=true → uev C D e=0

theorem rowOk {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hL : TableLocal compactTable tr t pub) (hr : r<tr.height t) :
    RowOk (rowC tr t r) (rowC tr t ((r+1)%tr.height t)) := by
  intro e he hp
  rw [←eval_pure tr t r pub e hp]
  exact hL.constr r hr e he

theorem fact {C D : URow} (ok : RowOk C D) {e : Expr}
    (he : e∈compactConstraints) (hp : e.pure=true := by rfl) : uev C D e=0 := ok e he hp

theorem noValue {C D : URow} (ok : RowOk C D) (hC : ∀x,C x<P) : C vb=0 := by
  have h:=fact ok (e:=c vb) (by simp [compactConstraints,compactRows])
  exact natv (hC _) (by have := P_gt; omega) h

private def removedRows := (UpsV3.cRows.drop 10).take 13
set_option maxHeartbeats 2000000 in
private theorem old_covered : UpsV3.constraints ⊆ compactConstraints++removedRows := by
  have hc : UpsV3.cRows ⊆ compactRows++removedRows := by decide +kernel
  intro e he
  have hc' : e∈UpsV3.cRows → e∈compactRows ∨ e∈removedRows := fun h=>List.mem_append.mp (hc h)
  simp only [UpsV3.constraints,List.mem_append] at he
  simp only [compactConstraints,List.mem_append]
  grind only

/-- All old local extraction theorems are reusable away from W3. Deleted value
constraints vanish because the candidate forces vb=0; only W3 changes successor. -/
theorem oldRowOk {C D : URow} (ok : RowOk C D) (hC : ∀x,C x<P)
    (hw : C wt3=0) : URowOk C D := by
  have hv:=noValue ok hC
  intro e he hp
  rcases List.mem_append.mp (old_covered he) with he|he
  · exact ok e he hp
  · simp only [removedRows,UpsV3.cRows,List.drop_succ_cons,List.drop_zero,
      List.take_succ_cons,List.take_zero,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [uev,Expr.evalWith,uEnv,Dsl.c,Dsl.mul3,hw,hv,cast_ofNat,cast0] <;> grind

theorem rowBool {C D : URow} (ok : RowOk C D) (hC : ∀x,C x<P)
    {x : Nat} (hx : x∈rowBools) : C x=0 ∨ C x=1 := by
  have h:=fact ok (e:=Dsl.bool (c x)) (by simp only [compactConstraints,cBool,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false,or_assoc]; exact Or.inl ⟨x,hx,rfl⟩)
  exact nat01 (hC x) h

/-- W3 starts node part one directly, without any fresh-value row. -/
theorem w3_next {C D : URow} (ok : RowOk C D) (hD : ∀x,D x<P) (hw : C wt3=1) :
    D qb=1 ∧ D pf=1 ∧ D j=1 := by
  have hq:=fact ok (e:=.mul (c wt3) (Dsl.not (n qb))) (by simp [compactConstraints,compactRows])
  have hp:=fact ok (e:=.mul (c wt3) (Dsl.not (n pf))) (by simp [compactConstraints,compactRows])
  have hj:=fact ok (e:=.mul (c wt3) (sub (n j) (k 1))) (by simp [compactConstraints,compactRows])
  uev_simp
  simp only [hw,cast_ofNat,cast1] at hq hp hj
  have one : (1:Nat)<P := by have := P_gt; omega
  exact ⟨natv (hD _) one (by grind),natv (hD _) one (by grind),natv (hD _) one (by grind)⟩
end ZkFormal.NearV3.Render.UpsRelay.Extract
