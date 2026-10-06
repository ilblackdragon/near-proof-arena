import ZkFormal.NearV3.Extract.ValProof
import ZkFormal.NearV3.Render.WalkLocal

/-!
# ZkFormal.NearV3.Render.ValGen — honest rows of the `valV3` table

Rows: the records `(t, p)` (record `t = es[t]`, row `p < nOf es[t]`, `nOf = 1` for an empty
value, else `len`), then the `SUM` row (index `R = Σ nOf`), then padding.  Record row
`(t, p)` of `e`: `act = 1`, `vf = [p = 0]`, `vl = [p + 1 = nOf e]`, `vid`, `len`, `pos = p`,
`b = bytes[p]` (`0` for an empty value), the flags `vz dup hd`, `repE`, `sumr = 0`,
`gb = [¬ vz]`, `gdu = [p = 0 ∧ dup]`.  The `SUM` row has `sumr = 1`; padding is zero.  On every
row `sz` is the number of earlier record rows of non-empty non-duplicate records
(`szAt`), so the `SUM` row sends `SIZE (1, Σ non-vz non-dup len)`.
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra

/-- What the honest `valV3` trace needs: the view's well-formedness (which includes the row
cap).  The record list may be empty. -/
structure ValOk (es : List ValE) : Prop where
  wf : ValWf es

namespace ValGen

def nOf (e : ValE) : Nat := if e.vz then 1 else e.len
def ent (es : List ValE) (t : Nat) : ValE := es.getD t default
/-- Number of record rows. -/
def R (es : List ValE) : Nat := (es.map nOf).sum

def recs (es : List ValE) : List (Nat × Nat) :=
  (List.range es.length).flatMap fun t => (List.range (nOf (ent es t))).map fun p => (t, p)

/-- Weight of a record row in `sz`. -/
def gw (es : List ValE) (tp : Nat × Nat) : Nat := if (ent es tp.1).vz || (ent es tp.1).dup then 0 else 1

def szAt (es : List ValE) (q : Nat) : Nat := (((recs es).take q).map (gw es)).sum

/-- Cells of a record row (columns other than `sz`). -/
def recCell (es : List ValE) (tp : Nat × Nat) : Nat → Nat
  | 0 => 1
  | 1 => if tp.2 = 0 then 1 else 0
  | 2 => if tp.2 + 1 = nOf (ent es tp.1) then 1 else 0
  | 3 => (ent es tp.1).vid
  | 4 => (ent es tp.1).len
  | 5 => tp.2
  | 6 => (ent es tp.1).bytes.getD tp.2 0
  | 7 => if (ent es tp.1).vz then 1 else 0
  | 8 => if (ent es tp.1).dup then 1 else 0
  | 9 => if (ent es tp.1).hd then 1 else 0
  | 10 => (ent es tp.1).repE
  | 13 => if (ent es tp.1).vz then 0 else 1
  | 14 => if tp.2 = 0 ∧ (ent es tp.1).dup = true then 1 else 0
  | _ => 0

def cell (es : List ValE) (_H q col : Nat) : Nat :=
  if col = 11 then szAt es q
  else if q < R es then recCell es ((recs es).getD q default) col
  else if q = R es ∧ col = 12 then 1 else 0

end ValGen

/-- The honest `valV3` rows. -/
def valRows (es : List ValE) : Array Row :=
  mkTab (2 ^ logOf (ValGen.R es + 1)) ValV3.width (ValGen.cell es (2 ^ logOf (ValGen.R es + 1)))

namespace ValGen

theorem map_getD {α β : Type} (d : α) (F : α → β) (l : List α) :
    (List.range l.length).map (fun t => F (l.getD t d)) = l.map F := by
  apply List.ext_getElem (by simp)
  intro i h1 h2; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by simpa using h1)]

theorem recs_length (es : List ValE) : (recs es).length = R es := by
  simp only [recs, List.length_flatMap, List.length_map, List.length_range, R]
  rw [show (fun t => nOf (ent es t)) = (fun t => nOf (es.getD t default)) from rfl, map_getD]

theorem recs_mem {es : List ValE} {tp : Nat × Nat} (h : tp ∈ recs es) :
    tp.1 < es.length ∧ tp.2 < nOf (ent es tp.1) := by
  simp only [recs, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨t, ht, p, hp, rfl⟩ := h
  exact ⟨ht, hp⟩

theorem recs_getD_mem {es : List ValE} {q : Nat} (hq : q < R es) : (recs es).getD q default ∈ recs es := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [recs_length]; exact hq)]
  exact List.getElem_mem _

theorem ent_mem {es : List ValE} {t : Nat} (ht : t < es.length) : ent es t ∈ es := by
  simp only [ent, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
  exact List.getElem_mem _

theorem sum_flatMap' {α β : Type} (f : β → Nat) (g : α → List β) : ∀ (l : List α),
    ((l.flatMap g).map f).sum = (l.map fun x => ((g x).map f).sum).sum
  | [] => rfl
  | x :: r => by simp [List.flatMap_cons, List.map_append, List.sum_append, sum_flatMap' f g r]

/-- Consecutive record rows. -/
def RAdj (es : List ValE) (a b : Nat × Nat) : Prop :=
  (b.1 = a.1 ∧ b.2 = a.2 + 1) ∨ (a.2 + 1 = nOf (ent es a.1) ∧ b.1 = a.1 + 1 ∧ b.2 = 0)

variable {es : List ValE} (ok : ValOk es)
include ok

theorem nOf_pos {t : Nat} (ht : t < es.length) : 1 ≤ nOf (ent es t) := by
  have := ok.wf.shape _ (ent_mem ht)
  simp only [nOf]; split
  · omega
  · rename_i h; exact (this.2 (by simpa using h)).2

theorem recs_adj : Adj2 (RAdj es) (recs es) := by
  apply Adj2.flatMap
  · intro t _
    apply Adj2.of_get
    intro q hq
    simp only [List.length_map, List.length_range] at hq
    simp [RAdj]
  · apply Adj2.of_get
    intro q hq a b' ha hb
    simp only [List.length_range] at hq
    simp only [List.getElem_range] at ha hb
    obtain ⟨m, hm⟩ : ∃ m, nOf (ent es q) = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (nOf_pos ok (by omega))).symm⟩
    obtain ⟨m', hm'⟩ : ∃ m, nOf (ent es (q + 1)) = m + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (nOf_pos ok hq)).symm⟩
    rw [hm, List.range_succ, List.map_append] at ha
    rw [hm', List.range_succ_eq_map] at hb
    simp at ha hb
    subst ha hb
    right; simp [hm]
  · intro t ht h
    have := nOf_pos ok (List.mem_range.1 ht)
    simp only [List.map_eq_nil_iff, List.range_eq_nil] at h; omega

theorem adjAt {q : Nat} (h : q + 1 < R es) : RAdj es ((recs es).getD q default) ((recs es).getD (q + 1) default) := by
  have := (recs_adj ok).get q (by rw [recs_length]; exact h)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [recs_length]; omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [recs_length]; exact h)]
  exact this

theorem recs_head (hR : 0 < R es) : (recs es).getD 0 default = (0, 0) := by
  cases hes : es with
  | nil => simp [R, hes] at hR
  | cons e l =>
    have h1 := nOf_pos ok (t := 0) (by simp [hes])
    obtain ⟨m, hm⟩ : ∃ m, nOf (ent es 0) = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h1).symm⟩
    rw [hes] at hm
    simp only [recs, List.length_cons, List.range_succ_eq_map, List.flatMap_cons, hm, List.map_cons]
    rfl

/-- The record row after `(t, p)` with `p + 1 = nOf` is `(t + 1, 0)` or the `SUM` row. -/
theorem next_after_last {q : Nat} (hq : q + 1 < R es)
    (hl : ((recs es).getD q default).2 + 1 = nOf (ent es ((recs es).getD q default).1)) :
    ((recs es).getD (q + 1) default).1 = ((recs es).getD q default).1 + 1 ∧ ((recs es).getD (q + 1) default).2 = 0 := by
  rcases adjAt ok hq with h | h
  · have := (recs_mem (recs_getD_mem hq)).2; rw [h.1, h.2] at this; omega
  · exact h.2

theorem recs_last (hR : 0 < R es) :
    ((recs es).getD (R es - 1) default).2 + 1 = nOf (ent es ((recs es).getD (R es - 1) default).1) := by
  have hne : es.length ≠ 0 := by intro h; simp [R, List.length_eq_zero_iff.1 h] at hR
  obtain ⟨m, hm⟩ : ∃ m, es.length = m + 1 := ⟨es.length - 1, by omega⟩
  have h1 := nOf_pos ok (t := m) (by omega)
  have hsplit : recs es = ((List.range m).flatMap fun t => (List.range (nOf (ent es t))).map fun p => (t, p)) ++
      (List.range (nOf (ent es m))).map (fun p => (m, p)) := by
    simp only [recs, hm, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
  have hlen := recs_length es
  rw [hsplit, List.length_append, List.length_map, List.length_range] at hlen
  rw [hsplit, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  rw [show R es - 1 - ((List.range m).flatMap fun t => (List.range (nOf (ent es t))).map fun p => (t, p)).length =
    nOf (ent es m) - 1 by omega]
  simp only [List.getElem?_map, List.getElem?_range, show nOf (ent es m) - 1 < nOf (ent es m) by omega, if_true]
  simp; omega

theorem next_within {q : Nat} (hq : q < R es)
    (hl : ¬ ((recs es).getD q default).2 + 1 = nOf (ent es ((recs es).getD q default).1)) :
    q + 1 < R es ∧ ((recs es).getD (q + 1) default).1 = ((recs es).getD q default).1 ∧
      ((recs es).getD (q + 1) default).2 = ((recs es).getD q default).2 + 1 := by
  have h1 : q + 1 < R es := by
    apply Classical.byContradiction; intro hn
    exact hl (by rw [show q = R es - 1 by omega]; exact recs_last ok (by omega))
  rcases adjAt ok h1 with h | h
  · exact ⟨h1, h⟩
  · exact absurd h.1 hl

/-- `sz` steps by the weight of the row. -/
theorem szAt_succ (q : Nat) :
    szAt es (q + 1) = szAt es q + (if q < R es then gw es ((recs es).getD q default) else 0) := by
  simp only [szAt, List.take_succ, List.map_append, List.sum_append]
  congr 1
  split
  · rename_i h
    rw [List.getElem?_eq_getElem (by rw [recs_length]; exact h), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [recs_length]; exact h)]
    simp
  · rename_i h
    rw [List.getElem?_eq_none (by rw [recs_length]; omega)]; simp

omit ok in
theorem szAt_zero : szAt es 0 = 0 := by simp [szAt]

/-- The total `sz` is the number of bytes of non-empty non-duplicate records. -/
theorem szAt_R : szAt es (R es) = ((es.filter fun e => !e.vz && !e.dup).map ValE.len).sum := by
  simp only [szAt, ← recs_length, List.take_length]
  rw [recs, sum_flatMap']
  have hfun : (fun t => (((List.range (nOf (ent es t))).map fun p => (t, p)).map (gw es)).sum) =
      fun t => (fun e => if !e.vz && !e.dup then e.len else 0) (es.getD t default) := by
    funext t
    show _ = (fun e => if !e.vz && !e.dup then e.len else 0) (ent es t)
    rw [List.map_map, show (gw es ∘ fun p => (t, p)) = fun _ => (if (ent es t).vz || (ent es t).dup then 0 else 1)
      from rfl]
    cases hv : (ent es t).vz <;> cases hd : (ent es t).dup <;>
      simp [nOf, hv, hd, ValProof.sum_map_zero', ValProof.sum_map_one]
  rw [hfun, map_getD default (fun e => if (!e.vz && !e.dup) = true then e.len else 0) es]
  rw [ValProof.sum_filter_map (fun e => if (!e.vz && !e.dup) = true then e.len else 0) id
    (fun e => !e.vz && !e.dup) ValE.len es (fun e _ => rfl)]
  simp

theorem ids' {t : Nat} (ht : t + 1 < es.length) :
    (ent es (t + 1)).vid = ((ent es t).vid + 1) % ZkFormal.Algebra.P := by
  have := ok.wf.ids t ht
  simp only [ent, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht,
    List.getElem?_eq_getElem (show t < es.length by omega), Option.getD_some]
  exact this

theorem shapeAt {t : Nat} (ht : t < es.length) :
    ((ent es t).vz = true → (ent es t).len = 0 ∧ (ent es t).bytes = []) ∧
    ((ent es t).vz = false → (ent es t).bytes.length = (ent es t).len ∧ 0 < (ent es t).len) :=
  ok.wf.shape _ (ent_mem ht)

end ValGen

end ZkFormal.NearV3.Render
