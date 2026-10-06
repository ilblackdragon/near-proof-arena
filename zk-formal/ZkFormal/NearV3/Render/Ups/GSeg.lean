import ZkFormal.NearV3.Render.Ups.Tac

/-!
# ZkFormal.NearV3.Render.Ups.GSeg — `cSeg` on the honest table

Every constraint of `cSeg` is gated by `sf`: on `W0` they are the case facts of `InstOk`
(one-hot selectors, terminal class vs case, the bits of `x`, `px`, the split-branch bitmap
bytes, the number of parts); on every other row they vanish (`vz`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

namespace UpsGen

section
variable {I : UpsInst} (iok : InstOk I) {C D P : Nat → Int} {fst lst trn : Int}
  (hC : ∀ x, x < 187 → C x = WC I 0 x)
include iok hC

theorem seg_w0 : ∀ ex ∈ UpsV3.cSeg, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  apply cast0
  simp only [UpsV3.cSeg, List.mem_cons, List.not_mem_nil, or_false] at hex
  have hci := iok.ci
  have hts := iok.ts
  have hti := iok.ti
  have hD := iok.D
  have hx := iok.x
  rcases hex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ups_ev [hC] <;> cellsimp
  · rcases lt11 hci with h | h | h | h | h | h | h | h | h | h | h <;> simp [h, ind]
  · rcases lt3 hD with h | h | h <;> simp [h, ind]
  · rcases (show I.ts = 1 ∨ I.ts = 2 ∨ I.ts = 3 by omega) with h | h | h <;> simp [h, ind]
  · rcases lt3 hti with h | h | h <;> simp [h, ind]
  · by_cases h3 : I.ts = 3
    · rcases iok.tsEnd h3 with h | h | h | h | h | h <;> simp [h, h3, ind]
    · simp [h3, ind]
  · by_cases h3 : I.ts = 3
    · simp [h3, ind]
    · rcases iok.tsNib h3 with h | h | h | h | h <;> simp [h, h3, ind]
  · simp only [xbit]
    rcases lt16 hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  · simp only [xbit, pxV]
    rcases lt16 hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  · simp only [bmLV, spYc, cin, List.map, List.sum_cons, List.sum_nil]; grind
  · simp only [bmHV, spYc, cin, List.map, List.sum_cons, List.sum_nil]; grind
  · rw [iok.nQ]
    rcases lt11 hci with h | h | h | h | h | h | h | h | h | h | h <;>
    rcases lt3 hti with h' | h' | h' <;> rcases lt3 hD with h'' | h'' | h'' <;>
      simp [h, h', h'', ind, UpsRows.nTof, UpsRows.termPlan, UpsRows.UCase.all, UpsRows.UCase.split] <;> omega

end

theorem mem_cons_of {e : Expr} {l : List Expr} (h : e ∈ l) (hl : ∀ y ∈ l, y ∈ UpsV3.constraints) :
    e ∈ UpsV3.constraints := hl e h

/-- **`cSeg`.** -/
theorem cSeg_ok {insts : List UpsInst} (ok : UpsOk insts) {H : Nat} (hH : R insts + 1 ≤ H) :
    GroupOk insts H UpsV3.cSeg := by
  apply groupOk_of ok.shape hH (fun e he => by simp [UpsV3.constraints, he])
  intro q hq C D P hC hD ex hex
  obtain ⟨i, hi, -, hk⟩ := actRow ok.shape hq
  have iok := ok.inst _ (inst_mem hi)
  rcases hk with ⟨t, ht, hr⟩ | ⟨p, hp, hr⟩ | ⟨k, p, hk, hp, hr⟩ <;> rw [hr] at hC
  · rw [rowCell_w] at hC
    rcases (show t = 0 ∨ 1 ≤ t by omega) with rfl | ht1
    · exact seg_w0 iok hC ex hex
    · refine vzC (zc := fun x => zW x || x == 4) (fun x hx => ?_)
        (List.all_eq_true.1 (show UpsV3.cSeg.all (vz (fun x => zW x || x == 4) (fun _ => false) false false false) = true
          by decide) ex hex)
      simp only [Bool.or_eq_true, beq_iff_eq] at hx
      rcases hx with hx | rfl
      · rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx
      · rw [hC 4 (by decide)]; simp [WC, isSeg, wCell, ind]; omega
  · rw [rowCell_v] at hC
    refine vzC (zc := zV) (fun x hx => ?_)
      (List.all_eq_true.1 (show UpsV3.cSeg.all (vz zV (fun _ => false) false false false) = true by decide) ex hex)
    rw [hC x (by simp [zV] at hx; omega)]; exact zV_cell _ _ _ hx
  · rw [rowCell_q] at hC
    refine vzC (zc := zQ) (fun x hx => ?_)
      (List.all_eq_true.1 (show UpsV3.cSeg.all (vz zQ (fun _ => false) false false false) = true by decide) ex hex)
    rw [hC x (by simp [zQ] at hx; omega)]; exact zQ_cell _ _ _ _ _ _ _ _ _ _ hx

end UpsGen

end ZkFormal.NearV3.Render
