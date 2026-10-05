import ZkFormal.Near.Render.Proof.MrkFacts
import ZkFormal.Near.Render.Proof.MrkLocal

/-!
# ZkFormal.Near.Render.Proof.MrkTraffic — `MrkTrafficStmt`
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace MrkTraffic
open SortLocal (ofNat0 ofNat1)
open MrkGen

/-- Child `k` of a node on level `j`. -/
def ch (lv : List (List MNode)) (j k : Nat) : MNode := (lv.getD (j - 1) []).getD k default

/-- The window child of row `p` of hashed node `(j, i)`. -/
def chp (lv : List (List MNode)) (j i p : Nat) : MNode := if p / 32 = 0 then ch lv j (2 * i) else ch lv j (2 * i + 1)

def digRow (m : MNode) (off : Nat) : List Fp :=
  [Fp.ofNat m.id, Fp.ofNat m.len] ++ (List.range 32).map fun x => Fp.ofNat (m.dig.getD (off + x) 0)

/-- Traffic of node row `r`. -/
def rowM (n : Nat) (lv : List (List MNode)) (r : Rec) (b : Nat) (s : Bool) : List (List Fp) :=
  let (j, i, h, p) := r
  if h then
    (if b = B_BYTES ∧ s = true then
      [[Fp.ofNat (K_MRK + 16 * (qBase n j + i)), Fp.ofNat (32 * (p / 32) + p % 32),
        Fp.ofNat ((chp lv j i p).dig.getD (p % 32 + 0) 0)]] else []) ++
    (if b = B_DIGEST ∧ s = false ∧ p % 32 = 0 then [digRow (chp lv j i p) (p % 32)] else []) ++
    (if b = B_MPOS ∧ s = false ∧ p % 32 = 0 then
      [[Fp.ofNat (j - 1), Fp.ofNat (2 * i + p / 32), Fp.ofNat (chp lv j i p).id, Fp.ofNat (chp lv j i p).len]]
      else []) ++
    (if b = B_MPOS ∧ s = true ∧ p = 0 then
      [[Fp.ofNat j, Fp.ofNat i, Fp.ofNat (K_MRK + 16 * (qBase n j + i)), Fp.ofNat 64]] else [])
  else
    (if b = B_MPOS ∧ s = false then
      [[Fp.ofNat (j - 1), Fp.ofNat (2 * i), Fp.ofNat (ch lv j (2 * i)).id, Fp.ofNat (ch lv j (2 * i)).len]]
      else []) ++
    (if b = B_MPOS ∧ s = true then
      [[Fp.ofNat j, Fp.ofNat i, Fp.ofNat (ch lv j (2 * i)).id, Fp.ofNat (ch lv j (2 * i)).len]] else [])

/-- Traffic of the root row. -/
def rowRoot (n : Nat) (lv : List (List MNode)) (pub : List Fp) (b : Nat) (s : Bool) : List (List Fp) :=
  let root := (lv.getD (topJ n) []).getD 0 default
  (if b = B_DIGEST ∧ s = false then
    [[Fp.ofNat root.id, Fp.ofNat root.len] ++ (List.range 32).map fun x => pub.getD (PV_OUT + x) 0] else []) ++
  (if b = B_MPOS ∧ s = false then [[Fp.ofNat (topJ n), Fp.ofNat 0, Fp.ofNat root.id, Fp.ofNat root.len]] else [])

section
variable {tr : Trace Fp} {pub : List Fp} {H n : Nat} {lv : List (List MNode)} {rs : List Rec}
  (hcell : ∀ q col, q < H → col < 58 → tr.cell T_MRK q col = Fp.ofNat (cell n lv rs q col))
include hcell

theorem row_node {q : Nat} (hq : q < H) (hq0 : q ≠ 0) (hr : q - 1 < rs.length)
    (hrec : ∀ j i p, rs.getD (q - 1) default = (j, i, true, p) → p < 64) (b : Nat) (s : Bool) :
    rowTraffic Mrk.interactions tr T_MRK q pub b s = rowM n lv (rs.getD (q - 1) default) b s := by
  have hc : ∀ col, col < 58 → tr.cell T_MRK q col = Fp.ofNat (nodeCell n lv (rs.getD (q - 1) default) col) := by
    intro col h; rw [hcell q col hq h]; simp [cell, hq0, hr]
  have hregs : ∀ j i p, rs.getD (q - 1) default = (j, i, true, p) →
      ((List.range 32).map (fun x => c (Mrk.reg x))).map (fun e => e.eval tr T_MRK q pub) =
        (List.range 32).map fun x => Fp.ofNat ((chp lv j i p).dig.getD (p % 32 + x) 0) := by
    intro j i p hrr
    rw [List.map_map]
    apply List.map_congr_left; intro x hx
    have hx' := List.mem_range.1 hx
    simp only [Function.comp_apply]
    rw [eval_c, hc _ (by simp only [Mrk.reg]; omega), hrr, MrkLocal.nodeCell_reg n lv j i p x hx']; rfl
  rcases hrr : rs.getD (q - 1) default with ⟨j, i, h, p⟩
  rw [hrr] at hc
  simp only [rowTraffic, Mrk.interactions, send, recv, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    multNat_one, Interaction.msgVal, List.map_cons, List.map_nil, List.map_append]
  cases h with
  | true =>
    have hp := hrec j i p hrr
    rw [hregs j i p hrr]
    simp only [eval_c, eval_mid, eval_add, eval_smul, Mrk.rt, Mrk.sg, Mrk.pr, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.cId, Mrk.cLen, Mrk.mj, Mrk.mi, Mrk.oId, Mrk.oLen, Mrk.gM, Mrk.gO, Mrk.reg, Nat.reduceAdd, hc, Nat.reduceLT, Nat.reduceLeDiff, nodeCell, Nat.reduceEqDiff,
      and_true, and_false, true_and, false_and, if_true, if_false, natCast_eq, ofNat_add', ofNat_mul', ofNat1, ofNat0, rowM, msgId]
    clear hcell hc hregs hrec hrr
    rcases (show b = 0 ∨ b = 1 ∨ b = 9 ∨ (b ≠ 0 ∧ b ≠ 1 ∧ b ≠ 9) by omega) with rfl | rfl | rfl | ⟨b0, b1, b9⟩ <;>
    cases s <;> by_cases hp0 : p = 0 <;> by_cases hpw : p % 32 = 0 <;>
    simp [B_BYTES, B_DIGEST, B_MPOS, hp0, hpw, fp_zero_ne_one, digRow, chp, ch, ofNat0, ofNat1, *] <;> omega
  | false =>
    simp only [eval_c, Mrk.rt, Mrk.sg, Mrk.pr, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl, Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil, Mrk.top, Mrk.inv, Mrk.cId, Mrk.cLen, Mrk.mj, Mrk.mi, Mrk.oId, Mrk.oLen, Mrk.gM, Mrk.gO, Mrk.reg, hc, Nat.reduceLT, Nat.reduceLeDiff, nodeCell, Nat.reduceEqDiff, Bool.false_eq_true,
      and_true, and_false, true_and, false_and,
      if_true, if_false, ofNat1, ofNat0, rowM]
    clear hcell hc hregs hrec hrr
    rcases (show b = 0 ∨ b = 1 ∨ b = 9 ∨ (b ≠ 0 ∧ b ≠ 1 ∧ b ≠ 9) by omega) with rfl | rfl | rfl | ⟨b0, b1, b9⟩ <;>
    cases s <;> simp [B_BYTES, B_DIGEST, B_MPOS, fp_zero_ne_one, ch, ofNat0, ofNat1, *] <;> omega

end

end MrkTraffic

end ZkFormal.Near.Render
