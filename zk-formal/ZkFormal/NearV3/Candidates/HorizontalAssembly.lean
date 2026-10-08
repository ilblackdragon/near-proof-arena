import ZkFormal.NearV3.Candidates.HorizontalJoin
namespace ZkFormal.NearV3.Candidates.HorizontalAssembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near HorizontalTables HorizontalTrace HorizontalJoin

@[simp] theorem expression_zero (e : Expr) : expression 0 e=e := by
  induction e <;> simp_all [expression]

@[simp] theorem expression_add (a b : Nat) (e : Expr) :
    expression a (expression b e)=expression (a+b) e := by
  induction e <;> simp_all [expression,Nat.add_assoc]

theorem expression_zero_fun : expression 0=id := funext expression_zero

@[simp] theorem interaction_zero (i : Interaction) : interaction 0 i=i := by
  cases i
  simp [interaction,expression_zero_fun]

@[simp] theorem shifted_zero (T : Air.Table) : shifted 0 T=T := by
  cases T
  simp [shifted,expression_zero_fun,show interaction 0=id from funext interaction_zero]

@[simp] theorem shifted_add (a b : Nat) (T : Air.Table) :
    shifted a (shifted b T)=shifted (a+b) T := by
  cases T
  simp [shifted,interaction,List.map_map,Function.comp_def]

@[simp] theorem layout_shift (ts : List Air.Table) (a b : Nat) :
    (layout b ts).map (shifted a)=layout (a+b) ts := by
  induction ts generalizing b with
  | nil => rfl
  | cons T ts ih => simp [layout,ih,Nat.add_assoc]

theorem shifted_fuse_constraints (ts : List Air.Table) (a : Nat) :
    (shifted a (fuse ts)).constraints=(layout a ts).flatMap (·.constraints) := by
  have hl := congrArg (fun xs : List Air.Table=>xs.flatMap (·.constraints)) (layout_shift ts a 0)
  simpa only [shifted,fuse,List.flatMap_map,List.map_flatMap,Function.comp_def,Nat.add_zero] using hl

theorem shifted_fuse_interactions (ts : List Air.Table) (a : Nat) :
    (shifted a (fuse ts)).interactions=(layout a ts).flatMap (·.interactions) := by
  have hl := congrArg (fun xs : List Air.Table=>xs.flatMap (·.interactions)) (layout_shift ts a 0)
  simpa only [shifted,fuse,List.flatMap_map,List.map_flatMap,Function.comp_def,Nat.add_zero] using hl

theorem fuse_cons (T : Air.Table) (ts : List Air.Table) (h : T.maxLog≤22) :
    fuse (T::ts)=pair T (fuse ts) := by
  cases T with
  | mk width constraints interactions maxLog =>
    have hc := shifted_fuse_constraints ts width
    have hi := shifted_fuse_interactions ts width
    unfold pair
    rw [hc,hi]
    simp [fuse,layout,show max maxLog 22=22 from Nat.max_eq_right h]

/-- Column concatenation with one explicit clock. Honest components must already
have this physical height; this construction does not extend shorter traces. -/
def trace (clock : Nat→Nat) : List (Air.Table × Trace Fp) → Trace Fp
  | [] => {log:=clock,cell:=fun _ _ _=>0}
  | (T,tr)::xs => join T.width tr (trace clock xs)

theorem trace_log (clock : Nat→Nat) (xs : List (Air.Table × Trace Fp)) (t : Nat)
    (h : ∀ x∈xs,x.2.log t=clock t) : (trace clock xs).log t=clock t := by
  cases xs with
  | nil => rfl
  | cons x xs => exact h x (by simp)

theorem trace_local (clock : Nat→Nat) (xs : List (Air.Table × Trace Fp))
    (t : Nat) (pub : List Fp) (hc : 1≤clock t ∧ clock t≤22)
    (hclock : ∀ x∈xs,x.2.log t=clock t)
    (hcap : ∀ x∈xs,x.1.maxLog≤22)
    (hlocal : ∀ x∈xs,TableLocal x.1 x.2 t pub)
    (hcols : ∀ x∈xs,∀e∈x.1.exprs,e.colBound≤x.1.width) :
    TableLocal (fuse (xs.map Prod.fst)) (trace clock xs) t pub := by
  induction xs with
  | nil =>
    refine ⟨hc.1,hc.2,?_,?_⟩
    · simp [fuse,layout]
    · simp [fuse,layout]
  | cons x xs ih =>
    rw [List.map_cons,fuse_cons _ _ (hcap x (by simp))]
    apply join_local (hlocal x (by simp))
      (ih (by intro y hy; exact hclock y (by simp [hy]))
        (by intro y hy; exact hcap y (by simp [hy]))
        (by intro y hy; exact hlocal y (by simp [hy]))
        (by intro y hy; exact hcols y (by simp [hy])))
    · rw [hclock x (by simp),trace_log clock xs t (by intro y hy; exact hclock y (by simp [hy]))]
    · exact hcols x (by simp)
end ZkFormal.NearV3.Candidates.HorizontalAssembly
