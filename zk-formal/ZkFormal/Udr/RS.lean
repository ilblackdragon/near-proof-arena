import ZkFormal.Udr.Code
import ZkFormal.Udr.Poly

/-!
# ZkFormal.Udr.RS — Reed–Solomon codes (scalar and interleaved)

`rsCode xs n D` is the evaluation code of polynomials of length `D`
(degree `< D`) at the pairwise distinct points `xs 0, …, xs (n-1)`; its
minimum distance is `n - D + 1` (root bound).  Interleaved RS codes are
`(rsCode …).interleave J`.
-/

namespace ZkFormal.Udr

open ArenaCore.Security
open Lean.Grind

set_option linter.unusedSectionVars false

variable {K : Type} [Field K]

/-- The points `xs 0, …, xs (n-1)` are pairwise distinct. -/
def Distinct (xs : Nat → K) (n : Nat) : Prop := ∀ i j, i < n → j < n → xs i = xs j → i = j

/-- Points at a duplicate-free list of positions form a duplicate-free list. -/
theorem Distinct.map_nodup {xs : Nat → K} {n : Nat} (h : Distinct xs n) {l : List Nat}
    (hl : l.Nodup) (hlt : ∀ i ∈ l, i < n) : (l.map xs).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, ih hl.2 fun i hi => hlt i (List.mem_cons_of_mem _ hi)⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.mp hm
    have := h b a (hlt b (List.mem_cons_of_mem _ hb)) (hlt a (List.mem_cons_self ..)) e
    exact hl.1 (this ▸ hb)

/-- Two length-`D` polynomials agreeing at `≥ D` of the distinct points agree everywhere. -/
theorem ev_eq_of_agree {xs : Nat → K} {n D : Nat} (hxs : Distinct xs n) (p q : Nat → K)
    (A : Nat → Prop) (hA : D ≤ count (List.range n) A)
    (hagree : ∀ i, i < n → A i → ev D p (xs i) = ev D q (xs i)) (x : K) :
    ev D p x = ev D q x := by
  obtain ⟨l, hlen, hmem, hnd⟩ := filter_props (List.range n) A
  have hlt : ∀ i ∈ l, i < n := fun i hi => List.mem_range.mp (hmem i hi).1
  have := (IsPoly.sub (IsPoly.of_ev D p) (IsPoly.of_ev D q)).eq_zero_of_roots (l.map xs)
    (hxs.map_nodup (hnd List.nodup_range) hlt) (by rw [List.length_map]; omega)
    (fun r hr => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
      show ev D p (xs i) - ev D q (xs i) = 0
      rw [hagree i (hlt i hi) (hmem i hi).2]; grind) x
  have h : ev D p x - ev D q x = 0 := this
  grind

/-- The scalar Reed–Solomon code `RS[xs, n, D]` with distance `n - D + 1`. -/
def rsCode (xs : Nat → K) (n D : Nat) (hD : D ≤ n) (hxs : Distinct xs n) :
    LinCode Unit K n (n - D + 1) where
  mem u := ∃ p : Nat → K, ∀ i, i < n → u i () = ev D p (xs i)
  zero := ⟨fun _ => 0, fun i _ => (ev_eq_zero (fun _ _ => rfl) _).symm⟩
  lin u v a b := fun ⟨p, hp⟩ ⟨q, hq⟩ => ⟨fun k => a * p k + b * q k, fun i hi => by
    show a * u i () + b * v i () = _
    rw [ev_lin, hp i hi, hq i hi]⟩
  sep u v := fun ⟨p, hp⟩ ⟨q, hq⟩ hd i hi => by
    have hc := count_add_count_not (List.range n) (fun i => u i ≠ v i)
    rw [List.length_range] at hc
    have hd' : count (List.range n) (fun i => u i ≠ v i) < n - D + 1 := hd
    have := hD
    have := ev_eq_of_agree (D := D) hxs p q (fun i => ¬ u i ≠ v i) (by omega) (fun j hj hA => by
      rw [← hp j hj, ← hq j hj, Classical.not_not.mp hA]) (xs i)
    funext c; cases c; rw [hp i hi, hq i hi, this]

/-- Interleaved Reed–Solomon code: every coordinate `j : J` is an RS codeword. -/
abbrev rsInterleaved (xs : Nat → K) (n D : Nat) (hD : D ≤ n) (hxs : Distinct xs n) (J : Type) :
    LinCode J K n (n - D + 1) :=
  (rsCode xs n D hD hxs).interleave J

end ZkFormal.Udr
