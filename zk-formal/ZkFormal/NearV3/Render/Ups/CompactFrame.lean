import ZkFormal.NearV3.Render.Ups.CompactCells

namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Near.Render.EvI ZkFormal.Algebra ZkFormal.Air UpsGen

def CompactGroupOk (insts : List UpsInst) (H : Nat) (es : List Expr) : Prop :=
  ∀ q,q<H → ∀ C D P : Nat→Int,
    (∀ x,x<200 → C x=compactCell insts q x) →
    (∀ x,x<200 → D x=compactCell insts ((q+1)%H) x) →
    ∀ ex∈es,((ev C D (if q=0 then 1 else 0) (if q+1=H then 1 else 0)
      (if q+1=H then 0 else 1) P ex : Int) : Fp)=0

def compactNextCell (insts : List UpsInst) (q x : Nat) : Int := compactCell insts (q+1) x

theorem compact_pad_all : compactConstraints.all
    (vz (fun x=>decide (x<200)) (fun x=>decide (x<200)) true false false)=true := by decide +kernel

theorem compact_pad_last : compactConstraints.all
    (vz (fun x=>decide (x<200)) (fun x=>x==113) true false true)=true := by decide +kernel

theorem compact_groupOk_of {insts : List UpsInst} (hpos : 0<insts.length) {H : Nat} (hH : compactR insts + 1 ≤ H) {es : List Expr}
    (hsub : ∀ e ∈ es, e ∈ compactConstraints)
    (hact : ∀ q, q < compactR insts → ∀ (C D P : Nat → Int),
      (∀ x, x < 200 → C x = compactRowCell insts q ((compactRecs insts).getD q default) x) →
      (∀ x, x < 200 → D x = compactNextCell insts q x) →
      ∀ ex ∈ es, ((ev C D (if q = 0 then 1 else 0) 0 1 P ex : Int) : Fp) = 0) :
    CompactGroupOk insts H es := by
  intro q hq C D P hC hD ex hex
  by_cases ha : q < compactR insts
  · have h1 : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt (by omega)
    rw [ite_eq_right (show q + 1 ≠ H by omega), ite_eq_right (show q + 1 ≠ H by omega)]
    apply hact q ha C D P (fun x hx => by rw [hC x hx]; simp [compactCell, ha]) (fun x hx => by
      rw [hD x hx, h1]; simp only [compactNextCell,compactCell]) ex hex
  · have hpz : ∀ x, x < 200 → C x = 0 := fun x hx => by rw [hC x hx]; simp [compactCell, ha]
    have hq0 : q ≠ 0 := by have := compactR_pos hpos; omega
    rw [ite_eq_right hq0]
    have he := hsub ex hex
    by_cases hl : q + 1 = H
    · rw [ite_eq_left hl, ite_eq_left hl]
      have hz := List.all_eq_true.1 compact_pad_last ex he
      rw [ev_vz (zc := fun x => decide (x < 200)) (zn := fun x => x == 113) (zf := true) (zl := false) (zt := true)
        (fun x h => hpz x (by simpa using h)) (fun x h => ?_) (fun _ => rfl) (fun h => absurd h (by decide))
        (fun _ => rfl) ex hz]
      · rfl
      · simp only [beq_iff_eq] at h; subst h
        rw [hD 113 (by decide), hl, Nat.mod_self]
        simp only [compactCell, compactR_pos hpos, ite_true, compact_first hpos, compactRowCell]
        rfl
    · rw [ite_eq_right hl, ite_eq_right hl]
      have hz := List.all_eq_true.1 compact_pad_all ex he
      rw [ev_vz (zc := fun x => decide (x < 200)) (zn := fun x => decide (x < 200)) (zf := true) (zl := false)
        (zt := false) (fun x h => hpz x (by simpa using h)) (fun x h => ?_) (fun _ => rfl)
        (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) ex hz]
      · rfl
      · simp only [decide_eq_true_eq] at h
        rw [hD x h, Nat.mod_eq_of_lt (by omega)]
        simp [compactCell, show ¬ q + 1 < compactR insts by omega]

end ZkFormal.NearV3.Render.UpsRelay
