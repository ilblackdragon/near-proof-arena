import ZkFormal.NearV3.Render.Node.TBm

/-!
# ZkFormal.NearV3.Render.Node.TEdge — record traffic: EDGE (rows → `(edge, index)` pairs)
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)

namespace NodeGen3

/-- The `(edge, index)` pairs a row provides. -/
def ePairs (vs : List NodeS3) (r : NRec) : List (List Nat × Nat) := (edgeAOf vs r).toList ++ (edgeBOf vs r).toList

def eMsg (uses : List Nat) (sd : Bool) (x : List Nat × Nat) : ZkFormal.Near.Msg :=
  x.1 ++ [if sd then 0 else uses.getD x.2 0]

theorem edgeA_len (vs : List NodeS3) (r : NRec) : ∀ x ∈ (edgeAOf vs r).toList, ∃ e1 e2 e3 e4 e5,
    x.1 = [r.n, e1, e2, e3, e4, e5] := by
  intro x hx
  obtain ⟨rn, pos, f, j, b, pb⟩ := r
  cases f <;> simp only [edgeAOf] at hx <;> (repeat' split at hx) <;> simp at hx <;> subst hx <;> simp

theorem edgeB_len (vs : List NodeS3) (r : NRec) : ∀ x ∈ (edgeBOf vs r).toList, ∃ e1 e2 e3 e4 e5,
    x.1 = [r.n, e1, e2, e3, e4, e5] := by
  intro x hx
  obtain ⟨rn, pos, f, j, b, pb⟩ := r
  cases f <;> simp only [edgeBOf] at hx <;> (repeat' split at hx) <;> simp at hx <;> subst hx <;> simp

theorem rowN_edge (vs : List NodeS3) (r : NRec) (sd : Bool) :
    rowN (rowCell vs r) B_EDGE sd = (ePairs vs r).map (eMsg (rec vs r.n).uses sd) := by
  have hA := edgeA_len vs r
  have hB := edgeB_len vs r
  cases sd <;> rown_simp <;>
  simp only [Rc.c145, Rc.c146, Rc.c147, Rc.c148, Rc.c149, Rc.c174, Rc.c150, Rc.c160, Rc.c176, Rc.c177, Rc.c161,
    Rc.c162, Rc.c175, Rc.c151, Rc.c4, ePairs, List.map_append] <;>
  (congr 1) <;>
  first
    | (rcases h : edgeAOf vs r with _ | ⟨e, i⟩
       · simp [gCell, gt]
       · obtain ⟨e1, e2, e3, e4, e5, he⟩ := hA (e, i) (by simp [h])
         simp only at he; subst he
         simp [gCell, eCell, uCell, gt, eMsg])
    | (rcases h : edgeBOf vs r with _ | ⟨e, i⟩
       · simp [gCell, gt]
       · obtain ⟨e1, e2, e3, e4, e5, he⟩ := hB (e, i) (by simp [h])
         simp only at he; subst he
         simp [gCell, eCell, uCell, gt, eMsg])

end NodeGen3

end ZkFormal.NearV3.Render

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
namespace NodeGen3

/-- The pairs of a field position of record `n` (`b` read off the field). -/
def gE (vs : List NodeS3) (n : Nat) (fi : F × Nat) : List (List Nat × Nat) :=
  ePairs vs ⟨n, 0, fi.1, fi.2, (fbytes (rec vs n).v false fi.1).getD fi.2 0, 0⟩

theorem rowN_edge_lay {vs : List NodeS3} (ok : NodeOk vs) {n p : Nat} (hn : n < vs.length)
    (hp : p < (layN vs n).length) (sd : Bool) :
    rowN (rowCell vs (mkR vs n p)) B_EDGE sd = (gE vs n ((layN vs n).getD p default)).map (eMsg (rec vs n).uses sd) := by
  rw [rowN_edge]
  simp only [mkR, gE, row_b ok hn hp false]
  rfl

/-- Key nibbles: the odd first nibble, then two per key byte. -/
theorem nib_enum {α : Type} (P : Nat → α) (s : Nat) :
    (if s % 2 = 1 then [P 0] else []) ++ (List.range (s / 2)).flatMap (fun m => [P (2 * m + s % 2), P (2 * m + s % 2 + 1)]) =
      (List.range s).map P := by
  have key : ∀ (o h : Nat), o ≤ 1 → (if o = 1 then [P 0] else []) ++
      (List.range h).flatMap (fun m => [P (2 * m + o), P (2 * m + o + 1)]) = (List.range (2 * h + o)).map P := by
    intro o h ho
    induction h with
    | zero => rcases (show o = 0 ∨ o = 1 by omega) with rfl | rfl <;> simp
    | succ h ih =>
      rw [List.range_succ, List.flatMap_append, ← List.append_assoc, ih,
        show 2 * (h + 1) + o = (2 * h + o) + 1 + 1 by omega, List.range_succ, List.range_succ]
      simp [List.map_append, show 2 * h + o + 1 = 2 * h + o + 1 from rfl]
  have := key (s % 2) (s / 2) (by omega)
  rw [show 2 * (s / 2) + s % 2 = s by omega] at this
  exact this

end NodeGen3
end ZkFormal.NearV3.Render

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
namespace NodeGen3

/-- The key-nibble edge `i` of record `n`. -/
def keyP (n : Nat) (v : NodeV3) (i : Nat) : List Nat × Nat :=
  (if i + 1 = sOf v ∧ isExt v = true then [n, i, (keyOf v).getD i 0, xtgtOf n v, xtgJOf v, EK_KEY]
   else [n, i, (keyOf v).getD i 0, n, i + 1, EK_KEY], i)

section
variable (vs : List NodeS3) (n : Nat)

theorem gE_other (f : F) (i : Nat) (h1 : f ≠ .hpf) (h2 : f ≠ .key) (h3 : ∀ w, f ≠ .vh w) (h4 : ∀ w, f ≠ .ch w)
    (h5 : f ≠ .mem) : gE vs n (f, i) = [] := by
  cases f <;> simp_all [gE, ePairs, edgeAOf, edgeBOf]

theorem gE_hpf (hw : (rec vs n).v.wf) (hle : isLE (rec vs n).v = true) :
    gE vs n (.hpf, 0) = if oddOf (rec vs n).v = 1 then [keyP n (rec vs n).v 0] else [] := by
  have hnib := key_nib hw
  have hh := NodeLay.hp_head (keyOf (rec vs n).v) (isLeaf (rec vs n).v) hnib
  simp only [gE, ePairs, edgeAOf, edgeBOf, fbytes, NodeLay.hpf_byte, hh, Option.toList, List.append_nil]
  generalize rec vs n = s at *
  obtain ⟨v, tau, d, res, uses, ubm, dup, hd, repE, ucid, mU⟩ := s
  simp only at hnib hh hle ⊢
  cases v with
  | branch => simp [isLE] at hle
  | leaf k sv m =>
    simp only [oddOf, isLE, keyOf, if_true, rec] at *
    by_cases ho : k.length % 2 = 1
    · have hk0 : k.getD 0 0 < 16 := by
        cases k with
        | nil => simp at ho
        | cons x l => exact hnib x (by simp)
      have hk0' : k[0]?.getD 0 < 16 := by simpa [List.getD_eq_getElem?_getD] using hk0
      simp [ho, keyP, isExt, sOf, keyOf, xlast0Of, b2n, isLeaf]
      omega
    · simp [ho]
  | ext k kid m =>
    simp only [oddOf, isLE, keyOf, if_true] at *
    by_cases ho : k.length % 2 = 1
    · have hk0 : k.getD 0 0 < 16 := by
        cases k with
        | nil => simp at ho
        | cons x l => exact hnib x (by simp)
      have hk0' : k[0]?.getD 0 < 16 := by simpa [List.getD_eq_getElem?_getD] using hk0
      by_cases h1 : k.length = 1
      · have hk00 : k[0]'(by omega) < 16 := hnib _ (List.getElem_mem _)
        simp [ho, keyP, isExt, sOf, keyOf, xlast0Of, nokeyOf, isLE, hplenOf, b2n, isLeaf, h1, Nat.mod_eq_of_lt hk00,
          Nat.mod_eq_of_lt hk0']
      · have : ¬ (k.length / 2 = 0) := by omega
        simp [ho, keyP, isExt, sOf, keyOf, xlast0Of, nokeyOf, isLE, hplenOf, b2n, isLeaf, h1, this,
          show ¬ (1 = k.length) by omega, Nat.mod_eq_of_lt hk0']
    · simp [ho]

end

end NodeGen3
end ZkFormal.NearV3.Render

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
namespace NodeGen3

theorem gE_key (vs : List NodeS3) (n : Nat) (hw : (rec vs n).v.wf) (hle : isLE (rec vs n).v = true) {m : Nat}
    (hm : m < (keyOf (rec vs n).v).length / 2) :
    gE vs n (.key, m) = [keyP n (rec vs n).v (2 * m + oddOf (rec vs n).v),
      keyP n (rec vs n).v (2 * m + oddOf (rec vs n).v + 1)] := by
  have hnib := key_nib hw
  have ht := NodeLay.hp_tail (keyOf (rec vs n).v) (isLeaf (rec vs n).v) hnib m hm
  simp only [gE, ePairs, edgeAOf, edgeBOf, fbytes, NodeLay.key_byte, ht, Option.toList, List.singleton_append]
  generalize rec vs n = s at *
  obtain ⟨v, tau, d, res, uses, ubm, dup, hd, repE, ucid, mU⟩ := s
  simp only at hnib ht hle hm ⊢
  have hodd : oddOf v = (keyOf v).length % 2 := by simp [oddOf, hle]
  rw [hodd]
  have h1 : (keyOf v).getD (2 * m + (keyOf v).length % 2) 0 < 16 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact hnib _ (List.getElem_mem _)
  have h2 : (keyOf v).getD (2 * m + (keyOf v).length % 2 + 1) 0 < 16 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact hnib _ (List.getElem_mem _)
  have hdiv : (16 * (keyOf v).getD (2 * m + (keyOf v).length % 2) 0 + (keyOf v).getD (2 * m + (keyOf v).length % 2 + 1) 0) / 16 =
      (keyOf v).getD (2 * m + (keyOf v).length % 2) 0 := by omega
  have hmod : (16 * (keyOf v).getD (2 * m + (keyOf v).length % 2) 0 + (keyOf v).getD (2 * m + (keyOf v).length % 2 + 1) 0) % 16 =
      (keyOf v).getD (2 * m + (keyOf v).length % 2 + 1) 0 := by omega
  have hlen : F.len (hplenOf v) F.key = (keyOf v).length / 2 := by simp [F.len, hplenOf, hle]
  simp only [hdiv, hmod, hlen, keyP, sOf]
  have hA : ¬ (2 * m + (keyOf v).length % 2 + 1 = (keyOf v).length) := by omega
  by_cases hl : m + 1 = (keyOf v).length / 2 ∧ isExt v = true
  · have h3 : 2 * m + (keyOf v).length % 2 + 1 + 1 = (keyOf v).length := by omega
    simp [hl, h3, hA]
  · have h3 : ¬ (2 * m + (keyOf v).length % 2 + 1 + 1 = (keyOf v).length ∧ isExt v = true) :=
      fun h => hl ⟨by omega, h.2⟩
    simp only [hA, false_and, if_false, hl, h3, List.cons.injEq, Prod.mk.injEq, and_true, true_and]

end NodeGen3
end ZkFormal.NearV3.Render

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Dsl
open ZkFormal.Near.Render.NodeGen (F Win layout bitOf b2n)
namespace NodeGen3

theorem gE_vh (vs : List NodeS3) (n : Nat) (w : Win) (i : Nat) :
    gE vs n (.vh w, i) = if i = 0 ∧ tvOf (rec vs n).v = true then
      [([n, (typeOf (rec vs n).v).1 * sOf (rec vs n).v, SYM_END, vidOf (rec vs n).v, 0, EK_VAL],
        if isLeaf (rec vs n).v then sOf (rec vs n).v else nRev (rec vs n).v)] else [] := by
  simp only [gE, ePairs, edgeAOf, edgeBOf]; split <;> simp

theorem gE_ch (vs : List NodeS3) (n : Nat) (w : Win) (i : Nat) :
    gE vs n (.ch w, i) = if i = 0 ∧ w.look = true ∧ isLE (rec vs n).v = false then
      [([n, 0, w.slot.getD 0, w.cres, 0, EK_DOWN], revBelow (kidsOf (rec vs n).v) (w.slot.getD 0))] else [] := by
  simp only [gE, ePairs, edgeAOf, edgeBOf]; split <;> simp

theorem gE_mem (vs : List NodeS3) (n : Nat) (i : Nat) :
    gE vs n (.mem, i) = if i = 0 ∧ isLeaf (rec vs n).v = true then
      [([n, sOf (rec vs n).v, SYM_END, n, sOf (rec vs n).v, EK_LEND], sOf (rec vs n).v + b2n (tvOf (rec vs n).v))]
      else [] := by
  simp only [gE, ePairs, edgeAOf, edgeBOf]; split <;> simp

/-- Enumerated list. -/
def enumL (l : List (List Nat)) : List (List Nat × Nat) := (List.range l.length).map fun i => (l.getD i [], i)

theorem enumL_append (a b : List (List Nat)) :
    enumL (a ++ b) = enumL a ++ (enumL b).map (fun x => (x.1, a.length + x.2)) := by
  simp only [enumL, List.length_append, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left; intro i hi
    have := List.mem_range.1 hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left this]
  · apply List.map_congr_left; intro i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem enumL_single (e : List Nat) : enumL [e] = [(e, 0)] := rfl

end NodeGen3
end ZkFormal.NearV3.Render
