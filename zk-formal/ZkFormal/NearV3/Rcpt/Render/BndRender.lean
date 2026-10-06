import ZkFormal.NearV3.Rcpt.Extract.BndProof
import ZkFormal.Near.Render.Proof.Base

/-!
# ZkFormal.NearV3.Rcpt.Render.BndRender — completeness of the `bndV3` table

Honest rows (`bndRows es`): row `q < |es|` holds record `es[q]` (`act = 1`), then zero padding to
`2^logOf |es|` rows.  For any trace whose table `t` has these cells:
* `bnd_render_local`: `TableLocal BndV3.table` (given `|es| ≤ 2^13`);
* `bnd_render_traffic`: traffic `bndTraffic es`.
-/

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace BndGen

def rowCell (e : BndE) : Nat → Nat
  | 0 => 1
  | 1 => e.x
  | 2 => e.lo
  | 3 => e.hi
  | 4 => e.hn
  | 5 => e.U
  | _ => 0

def cell (es : List BndE) (q col : Nat) : Nat := if q < es.length then rowCell (es.getD q default) col else 0

end BndGen

/-- The honest `bndV3` rows. -/
def bndRows (es : List BndE) : Array Row := mkTab (2 ^ logOf es.length) BndV3.width (BndGen.cell es)

namespace BndRender

theorem ofNat0 : Fp.ofNat 0 = 0 := rfl
theorem ofNat1 : Fp.ofNat 1 = 1 := rfl
theorem ofNat_mod (x : Nat) : Fp.ofNat (x % ZkFormal.Algebra.P) = Fp.ofNat x :=
  Fp.ext (by rw [Fp.toNat_ofNat, Fp.toNat_ofNat, Nat.mod_mod])

theorem height_ge {es : List BndE} {tr : Trace Fp} {t : Nat} (hlog : tr.log t = logOf es.length) :
    es.length ≤ tr.height t := by
  simp only [Trace.height, hlog]; exact le_pow_logOf _

end BndRender

open BndRender in
/-- **The honest `bndV3` table is locally legal.** -/
theorem bnd_render_local (es : List BndE) (hn : es.length ≤ 2 ^ BndV3.maxLog) (tr : Trace Fp) (t : Nat)
    (pub : List Fp) (hlog : tr.log t = logOf es.length)
    (hcell : ∀ r x, r < tr.height t → x < BndV3.width → tr.cell t r x = Fp.ofNat (BndGen.cell es r x)) :
    TableLocal BndV3.table tr t pub := by
  have hact : ∀ r, r < tr.height t → tr.cell t r BndV3.act = if r < es.length then 1 else 0 := by
    intro r hr
    rw [hcell r BndV3.act hr (by decide)]
    simp only [BndGen.cell, BndV3.act]
    split <;> rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlog]; exact one_le_logOf _
  · rw [hlog]; exact logOf_le (by decide) hn
  · intro r hr e he
    simp only [BndV3.table, BndV3.constraints, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · simp only [eval_bool, eval_c, hact r hr]; split <;> grind
    · simp only [eval_mul3, eval_c, eval_not, eval_n, eval_isTransition]
      by_cases hl : r + 1 = tr.height t
      · rw [if_pos hl]; grind
      · rw [if_neg hl, Nat.mod_eq_of_lt (by omega), hact r hr, hact (r + 1) (by omega)]
        by_cases h1 : r < es.length
        · rw [if_pos h1]; grind
        · rw [if_neg h1, if_neg (show ¬ r + 1 < es.length by omega)]; grind
  · intro r hr it hi bb hb
    simp only [BndV3.table, BndV3.interactions, Dsl.send, Dsl.recv, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      simp only [eval_c, hact r hr]
      split
      · right; rfl
      · left; rfl

open BndRender in
/-- **The honest `bndV3` table has the traffic of `es`.** -/
theorem bnd_render_traffic (es : List BndE) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf es.length)
    (hcell : ∀ r x, r < tr.height t → x < BndV3.width → tr.cell t r x = Fp.ofNat (BndGen.cell es r x)) :
    TableTraffic BndV3.interactions tr t pub (bndTraffic es) := by
  have hle := height_ge (tr := tr) (t := t) hlog
  have hrow : ∀ b sd q, q < tr.height t → rowTraffic BndV3.interactions tr t q pub b sd =
      if q < es.length then
        (if sd then bndSends [es.getD q default] b else bndRecvs [es.getD q default] b).map Msg.toFp
      else [] := by
    intro b sd q hq
    rw [BndProof.rowT]
    have hc := fun x (hx : x < BndV3.width) => hcell q x hq hx
    by_cases hqn : q < es.length
    · have cc : ∀ x, x < BndV3.width → tr.cell t q x = Fp.ofNat (BndGen.rowCell (es.getD q default) x) :=
        fun x hx => by rw [hc x hx]; simp [BndGen.cell, hqn]
      have ha : BndProof.isA tr t q = true := by
        simp only [BndProof.isA, cc BndV3.act (by decide)]; rfl
      rw [if_pos ha, if_pos hqn]
      simp only [BndProof.rowOf, cc BndV3.x (by decide), cc BndV3.lo (by decide), cc BndV3.hi (by decide),
        cc BndV3.hn (by decide), cc BndV3.uu (by decide)]
      simp only [BndGen.rowCell, BndV3.x, BndV3.lo, BndV3.hi, BndV3.hn, BndV3.uu, Fp.toNat_ofNat]
      cases sd <;> simp only [bndSends, bndRecvs] <;> repeat' split
      all_goals simp [BndE.rec4, Msg.toFp, ofNat_mod]
    · have ha : BndProof.isA tr t q = false := by
        simp only [BndProof.isA, hc BndV3.act (by decide)]; simp [BndGen.cell, hqn]; decide
      rw [if_neg (by simp [ha]), if_neg hqn]
  apply traffic_of
  all_goals
    intro b
    refine List.Perm.of_eq ?_
    rw [ZkFormal.Near.Render.flatMap_congr' (fun q hq => hrow b _ q (List.mem_range.1 hq)), range_split hle, List.flatMap_append,
      flatMap_nil' (l := List.map _ _) (fun q hq => by
        obtain ⟨q', -, rfl⟩ := List.mem_map.1 hq
        exact if_neg (by omega)),
      List.append_nil, ZkFormal.Near.Render.flatMap_congr' (g := fun q => _) (fun q hq => if_pos (List.mem_range.1 hq))]
  · simp only [if_true, ↓reduceIte]
    rw [← List.map_flatMap, ← flatMap_getD default es (fun e => bndSends [e] b), ← BndProof.bndSends_flat]; rfl
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← List.map_flatMap, ← flatMap_getD default es (fun e => bndRecvs [e] b), ← BndProof.bndRecvs_flat]; rfl

end ZkFormal.NearV3.Render
