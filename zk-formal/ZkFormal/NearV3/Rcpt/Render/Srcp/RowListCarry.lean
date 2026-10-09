import ZkFormal.NearV3.Rcpt.Render.Srcp.ListCarry

namespace ZkFormal.NearV3.Render.SrcpGen
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air ZkFormal.Algebra

def listCarryPolys : List Expr :=
  SrcpV3.listConst.map (fun x => .mul (Dsl.c SrcpV3.rt) (Dsl.sub (Dsl.n x) (Dsl.c x))) ++
  SrcpV3.listConst.map (fun x => Dsl.mul3 (Dsl.c SrcpV3.sg) (Dsl.not (Dsl.c SrcpV3.sl))
    (Dsl.sub (Dsl.n x) (Dsl.c x))) ++
  SrcpV3.listConst.map (fun x => Dsl.mul3 (Dsl.c SrcpV3.sl) (Dsl.n SrcpV3.sg)
    (Dsl.sub (Dsl.n x) (Dsl.c x)))

theorem listCarryPolys_eq : (SrcpV3.constraints.drop 65).take 12 = listCarryPolys := rfl

private theorem carry_eval (C D P : Nat → Int) (fst lst trn : Int)
    (hc : (∀ x ∈ SrcpV3.listConst, D x = C x) ∨
      (C SrcpV3.rt = 0 ∧ C SrcpV3.sl = 1 ∧ D SrcpV3.sg = 0) ∨
      (C SrcpV3.rt = 0 ∧ C SrcpV3.sg = 0 ∧ C SrcpV3.sl = 0)) :
    ∀ ex ∈ listCarryPolys, ev C D fst lst trn P ex = 0 := by
  intro ex hex
  rcases hc with hc | ⟨hRt, hSl, hSg⟩ | ⟨hRt, hSg, hSl⟩
  all_goals simp only [listCarryPolys, List.mem_append, List.mem_map] at hex
  all_goals rcases hex with (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩
  all_goals simp_all [ev, Dsl.mul3, Dsl.c, Dsl.n, Dsl.not, Dsl.sub, Dsl.k,
    Int.add_right_neg]

theorem row_list_carry {bs : List SrcpB} (h : SrcpWf bs) (H r : Nat)
    (hH : R bs ≤ H) (P : Nat → Int) (fst lst trn : Int) :
    ∀ ex ∈ listCarryPolys,
      ev (fun x => (cell bs r x : Int)) (fun x => (cell bs ((r + 1) % H) x : Int))
        fst lst trn P ex = 0 := by
  apply carry_eval
  by_cases hr : r < R bs
  · rcases list_carry_cases h H r hH hr with hc | ⟨hRt, hSl, hSg⟩
    · exact Or.inl (fun x hx => congrArg (fun n : Nat => (n : Int)) (hc x hx))
    · exact Or.inr (Or.inl ⟨by simp [hRt], by simp [hSl], by simp [hSg]⟩)
  · right; right
    have hp : R bs ≤ r := by omega
    simp [padding_cell hp, SrcpV3.rt, SrcpV3.sg, SrcpV3.sl, SrcpV3.sz]

theorem list_carry_constraints {bs : List SrcpB} (h : SrcpWf bs) {tr : Trace Fp}
    {tt r : Nat} {pub : List Fp} (hH : R bs ≤ tr.height tt)
    (hc : ∀ x, tr.cell tt r x = Fp.ofNat (cell bs r x))
    (hd : ∀ x, tr.cell tt ((r + 1) % tr.height tt) x =
      Fp.ofNat (cell bs ((r + 1) % tr.height tt) x)) :
    ∀ ex ∈ (SrcpV3.constraints.drop 65).take 12, ex.eval tr tt r pub = 0 := by
  rw [listCarryPolys_eq]
  intro ex hex
  apply eval_zero_of_ev (C := fun x => (cell bs r x : Int))
    (D := fun x => (cell bs ((r + 1) % tr.height tt) x : Int))
  · intro x
    rw [hc x, ofNat_int]
  · intro x
    rw [hd x, ofNat_int]
  · exact row_list_carry h _ r hH _ _ _ _ ex hex

end ZkFormal.NearV3.Render.SrcpGen
