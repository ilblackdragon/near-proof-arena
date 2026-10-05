import ZkFormal.Udr.Count

/-!
# ZkFormal.Udr.Code — linear codes with vector symbols, line lemmas (UDR)

Words are `Nat → ι → K`: position `i < n`, coordinate `c : ι`.  Scalar codes
take `ι = Unit`; an *interleaved* code (one RS codeword per column, as
batching needs) takes `ι` = the column index type, and the Hamming distance
counts *positions* at which the symbol vectors differ.

Main results (all over an arbitrary `Lean.Grind.Field`, no Mathlib):

* `strong_of_ca`, `strong_of_gap` — **correlated agreement ⇒ strong
  (containment) line lemma**: if `2e < d` and the line `u0 + z·u1` has a
  proximity gap with threshold `ε`, then at most `max ε e` challenges `z`
  violate the containment conclusion `Strong`.
* `gap_d3` — every linear code (any symbol type, hence interleaved codes)
  has a line proximity gap at radius `3e < d` with threshold `e + 1`.
* `gap_interleave` — the gap of a scalar code at `2e < d` lifts to its
  interleaved code with the **same threshold** (Diamond–Gruen style
  counting).
* `strong_line_d3` — the containment lemma at `3e < d` for every linear
  code with vector symbols: at most `e + 1` bad challenges (this sharpens
  and generalizes `ZkFormal.LineLemma.strong_line`, which had `max 1 n` and
  scalar symbols).
-/

namespace ZkFormal.Udr

open ArenaCore.Security
open Lean.Grind

set_option linter.unusedSectionVars false

/-- Words: position ↦ symbol vector. -/
abbrev Word (ι K : Type) := Nat → ι → K

section
variable {K : Type} [Field K] {ι : Type}

/-- Hamming distance on positions `[0, n)` (symbols compared as vectors). -/
noncomputable def dist (n : Nat) (u v : Word ι K) : Nat :=
  count (List.range n) fun i => u i ≠ v i

/-- A linear code of length `n` and minimum distance `d` with symbols `ι → K`. -/
structure LinCode (ι K : Type) [Field K] (n d : Nat) where
  mem : Word ι K → Prop
  zero : mem fun _ _ => 0
  lin : ∀ u v (a b : K), mem u → mem v → mem fun i c => a * u i c + b * v i c
  sep : ∀ u v, mem u → mem v → dist n u v < d → ∀ i, i < n → u i = v i

/-- `u0 + z·u1`. -/
def line (u0 u1 : Word ι K) (z : K) : Word ι K := fun i c => u0 i c + z * u1 i c

/-- `z` is good: the line point is `e`-close to the code. -/
def Good {n d : Nat} (C : LinCode ι K n d) (e : Nat) (u0 u1 : Word ι K) (z : K) : Prop :=
  ∃ w, C.mem w ∧ dist n (line u0 u1 z) w ≤ e

/-- The strong (containment) conclusion at `z`: every `e`-close codeword `w`
of the line point comes with codewords `v0, v1` that agree with `u0, u1` on
the whole agreement set of `u0 + z·u1` and `w`. -/
def Strong {n d : Nat} (C : LinCode ι K n d) (e : Nat) (u0 u1 : Word ι K) (z : K) : Prop :=
  ∀ w, C.mem w → dist n (line u0 u1 z) w ≤ e →
    ∃ v0 v1, C.mem v0 ∧ C.mem v1 ∧
      ∀ i, i < n → line u0 u1 z i = w i → u0 i = v0 i ∧ u1 i = v1 i

/-- Correlated agreement: `(u0, u1)` agrees with a pair of codewords outside
at most `e` positions. -/
def CA {n d : Nat} (C : LinCode ι K n d) (e : Nat) (u0 u1 : Word ι K) : Prop :=
  ∃ v0 v1, C.mem v0 ∧ C.mem v1 ∧
    count (List.range n) (fun i => u0 i ≠ v0 i ∨ u1 i ≠ v1 i) ≤ e

/-- Line proximity gap with threshold `ε`: more than `ε` good challenges in
any duplicate-free list force correlated agreement. -/
def LineGap {n d : Nat} (C : LinCode ι K n d) (e ε : Nat) : Prop :=
  ∀ (u0 u1 : Word ι K) (Ks : List K), Ks.Nodup → ε < count Ks (Good C e u0 u1) → CA C e u0 u1

/-! ## Distance lemmas -/

theorem dist_mono {ι' : Type} {n : Nat} {u v : Word ι K} {u' v' : Word ι' K}
    (h : ∀ i, i < n → u i ≠ v i → u' i ≠ v' i) : dist n u v ≤ dist n u' v' :=
  count_mono_mem _ fun i hi => h i (List.mem_range.mp hi)

theorem dist_triangle (n : Nat) (u v w : Word ι K) : dist n u w ≤ dist n u v + dist n v w := by
  refine Nat.le_trans (count_mono_mem _ (F := fun i => u i ≠ v i ∨ v i ≠ w i) ?_)
    (count_or_le _ _ _)
  intro i _ h
  by_cases huv : u i = v i
  · exact Or.inr (huv ▸ h)
  · exact Or.inl huv

theorem dist_comm (n : Nat) (u v : Word ι K) : dist n u v = dist n v u := by
  unfold dist
  congr 1
  funext i
  exact propext ⟨fun h e => h e.symm, fun h e => h e.symm⟩

theorem dist_congr {n : Nat} {u v u' v' : Word ι K} (hu : ∀ i, i < n → u i = u' i)
    (hv : ∀ i, i < n → v i = v' i) : dist n u v = dist n u' v' :=
  Nat.le_antisymm (dist_mono fun i hi h => by rwa [← hu i hi, ← hv i hi])
    (dist_mono fun i hi h => by rwa [hu i hi, hv i hi])

/-- Codewords within `e` of a common word, with `2e < d`, coincide. -/
theorem LinCode.unique {n d : Nat} (C : LinCode ι K n d) {e : Nat} (he : 2 * e < d)
    {u w w' : Word ι K} (hw : C.mem w) (hw' : C.mem w') (h1 : dist n u w ≤ e)
    (h2 : dist n u w' ≤ e) : ∀ i, i < n → w i = w' i := by
  apply C.sep w w' hw hw'
  have := dist_triangle n w u w'
  rw [dist_comm n w u] at this
  omega

/-- The line through two codewords stays in the code. -/
theorem LinCode.line_mem {n d : Nat} (C : LinCode ι K n d) {v0 v1 : Word ι K}
    (h0 : C.mem v0) (h1 : C.mem v1) (z : K) : C.mem (line v0 v1 z) := by
  have := C.lin v0 v1 1 z h0 h1
  have e : (fun i c => 1 * v0 i c + z * v1 i c) = line v0 v1 z := by
    funext i c; simp only [line]; grind
  rwa [e] at this

/-- A symbol at which `(u0, u1) ≠ (v0, v1)` lies on the line for at most one `z`. -/
theorem line_agree_unique {u0 u1 v0 v1 : Word ι K} {i : Nat}
    (hne : u0 i ≠ v0 i ∨ u1 i ≠ v1 i) {a b : K}
    (ha : line u0 u1 a i = line v0 v1 a i) (hb : line u0 u1 b i = line v0 v1 b i) : a = b := by
  refine Classical.byContradiction fun hab => ?_
  have hab' : a - b ≠ 0 := fun h => hab (by grind)
  have hinv := Field.mul_inv_cancel hab'
  have h1 : u1 i = v1 i := by
    funext c
    have ea := congrFun ha c
    have eb := congrFun hb c
    simp only [line] at ea eb
    have : (u1 i c - v1 i c) * (a - b) = 0 := by grind
    grind
  have h0 : u0 i = v0 i := by
    funext c
    have ea := congrFun ha c
    have e1 := congrFun h1 c
    simp only [line] at ea
    grind
  rcases hne with h | h
  · exact h h0
  · exact h h1

/-- Number of challenges in `Ks` at which some position of `S` lies on the
line: at most `|S|`. -/
theorem count_onLine_le {n : Nat} (u0 u1 v0 v1 : Word ι K) (Ks : List K) (hKs : Ks.Nodup) :
    count Ks (fun z => ∃ i ∈ List.range n, (u0 i ≠ v0 i ∨ u1 i ≠ v1 i) ∧
        line u0 u1 z i = line v0 v1 z i) ≤
      count (List.range n) (fun i => u0 i ≠ v0 i ∨ u1 i ≠ v1 i) := by
  classical
  refine Nat.le_trans (count_exists_mem_le _ _ _) ?_
  have hs := sum_map_ite (List.range n) (fun i => u0 i ≠ v0 i ∨ u1 i ≠ v1 i) 1
  rw [Nat.mul_one] at hs
  rw [← hs]
  apply sum_le_of_le
  intro i _
  by_cases hS : u0 i ≠ v0 i ∨ u1 i ≠ v1 i
  · rw [ite_eq_left hS]
    exact count_le_one_of_unique hKs _ fun a b ha hb => line_agree_unique hS ha.2 hb.2
  · rw [ite_eq_right hS]
    have : count Ks (fun z => (u0 i ≠ v0 i ∨ u1 i ≠ v1 i) ∧
        line u0 u1 z i = line v0 v1 z i) ≤ count Ks (fun _ => False) :=
      count_mono _ fun _ h => hS h.1
    rw [count_const] at this
    simpa using this

/-! ## Correlated agreement ⇒ strong line lemma -/

theorem strong_of_ca {n d : Nat} (C : LinCode ι K n d) {e : Nat} (he : 2 * e < d)
    {u0 u1 : Word ι K} (hca : CA C e u0 u1) (Ks : List K) (hKs : Ks.Nodup) :
    count Ks (fun z => ¬ Strong C e u0 u1 z) ≤ e := by
  obtain ⟨v0, v1, hv0, hv1, hS⟩ := hca
  refine Nat.le_trans (count_mono _ ?_) (Nat.le_trans (count_onLine_le u0 u1 v0 v1 Ks hKs) hS)
  intro z hz
  refine Classical.byContradiction fun hno => hz ?_
  intro w hw hdw
  refine ⟨v0, v1, hv0, hv1, fun i hi hwi => ?_⟩
  have hdv : dist n (line u0 u1 z) (line v0 v1 z) ≤ e := by
    refine Nat.le_trans (count_mono_mem _ ?_) hS
    intro j _ hj
    refine Classical.byContradiction fun h => hj ?_
    simp only [_root_.not_or, Classical.not_not] at h
    funext c; simp only [line]; rw [h.1, h.2]
  have hwl := C.unique he hw (C.line_mem hv0 hv1 z) hdw hdv i hi
  refine Classical.byContradiction fun hne => hno ⟨i, List.mem_range.mpr hi, ?_, hwi.trans hwl⟩
  by_cases h0 : u0 i = v0 i
  · exact Or.inr fun h1 => hne ⟨h0, h1⟩
  · exact Or.inl h0

/-- **Strong line lemma from a proximity gap.** -/
theorem strong_of_gap {n d : Nat} (C : LinCode ι K n d) {e ε : Nat} (he : 2 * e < d)
    (hgap : LineGap C e ε) (u0 u1 : Word ι K) (Ks : List K) (hKs : Ks.Nodup) :
    count Ks (fun z => ¬ Strong C e u0 u1 z) ≤ max ε e := by
  by_cases hfew : ε < count Ks (Good C e u0 u1)
  · exact Nat.le_trans (strong_of_ca C he (hgap u0 u1 Ks hKs hfew) Ks hKs) (Nat.le_max_right _ _)
  · refine Nat.le_trans (count_mono _ ?_) (Nat.le_trans (Nat.le_of_not_lt hfew) (Nat.le_max_left _ _))
    intro z hz
    exact Classical.byContradiction fun hg => hz fun w hw hd => absurd ⟨w, hw, hd⟩ hg

/-! ## Counting step: an affine family of codewords gives correlated agreement -/

theorem count_and_eq_ite {α : Type} (l : List α) (P : Prop) (Q : α → Prop) :
    count l (fun a => P ∧ Q a) = (open Classical in if P then count l Q else 0) := by
  classical
  by_cases hP : P
  · rw [ite_eq_left hP]; congr 1; funext a; exact propext ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩
  · rw [ite_eq_right hP]
    have : count l (fun a => P ∧ Q a) ≤ count l (fun _ => False) := count_mono _ fun _ h => hP h.1
    rw [count_const] at this
    simpa using this

/-- If every good challenge's line point is within `e` of the line
`v0 + z·v1` and there are more than `e + 1` good challenges, then `(u0, u1)`
agrees with `(v0, v1)` outside at most `e` positions. -/
theorem ca_of_affine {n d : Nat} (C : LinCode ι K n d) {e : Nat} {u0 u1 v0 v1 : Word ι K}
    (hv0 : C.mem v0) (hv1 : C.mem v1) (Ks : List K) (hKs : Ks.Nodup)
    (hG : e + 1 < count Ks (Good C e u0 u1))
    (hclose : ∀ z, Good C e u0 u1 z → dist n (line u0 u1 z) (line v0 v1 z) ≤ e) :
    CA C e u0 u1 := by
  classical
  refine ⟨v0, v1, hv0, hv1, ?_⟩
  generalize hGc : count Ks (Good C e u0 u1) = G at hG
  let S : Nat → Prop := fun i => u0 i ≠ v0 i ∨ u1 i ≠ v1 i
  let R : K → Nat → Prop := fun z i => Good C e u0 u1 z ∧ line u0 u1 z i ≠ line v0 v1 z i
  -- upper bound on the incidence sum
  have hup : (Ks.map fun z => count (List.range n) (R z)).sum ≤ G * e := by
    have e1 : (Ks.map fun z => count (List.range n) (R z)) =
        Ks.map fun z => if Good C e u0 u1 z then dist n (line u0 u1 z) (line v0 v1 z) else 0 :=
      List.map_congr_left fun z _ => count_and_eq_ite _ _ _
    rw [e1, ← hGc, ← sum_map_ite]
    apply sum_le_of_le
    intro z _
    by_cases hz : Good C e u0 u1 z
    · rw [ite_eq_left hz, ite_eq_left hz]; exact hclose z hz
    · rw [ite_eq_right hz, ite_eq_right hz]; exact Nat.le_refl _
  -- lower bound: every position of `S` is off the line for all but one good `z`
  have hlow : count (List.range n) S * (G - 1) ≤
      ((List.range n).map fun i => count Ks (fun z => R z i)).sum := by
    rw [← sum_map_ite]
    apply sum_le_of_le
    intro i _
    by_cases hS : S i
    · rw [ite_eq_left hS]
      have h1 := count_le_and_add_not Ks (Good C e u0 u1)
        (fun z => line u0 u1 z i ≠ line v0 v1 z i)
      have h2 : count Ks (fun z => ¬ line u0 u1 z i ≠ line v0 v1 z i) ≤ 1 :=
        count_le_one_of_unique hKs _ fun a b ha hb =>
          line_agree_unique hS (Classical.not_not.mp ha) (Classical.not_not.mp hb)
      have : count Ks (fun z => R z i) = count Ks (fun z => Good C e u0 u1 z ∧
          line u0 u1 z i ≠ line v0 v1 z i) := rfl
      omega
    · rw [ite_eq_right hS]; exact Nat.zero_le _
  have hswap := sum_count_swap Ks (List.range n) R
  have key : count (List.range n) S * (G - 1) ≤ G * e := by omega
  refine Classical.byContradiction fun hne => ?_
  have hS1 : e + 1 ≤ count (List.range n) S := Nat.lt_of_not_le hne
  have := Nat.le_trans (Nat.mul_le_mul_right (G - 1) hS1) key
  obtain ⟨G', rfl⟩ : ∃ G', G = G' + 1 := ⟨G - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul] at this
  rw [Nat.mul_comm e G'] at this
  omega

/-! ## Radius `d/3`: every linear code -/

/-- Line proximity gap at `3e < d` for every linear code (any symbol type). -/
theorem gap_d3 {n d : Nat} (C : LinCode ι K n d) {e : Nat} (he : 3 * e < d) :
    LineGap C e (e + 1) := by
  intro u0 u1 Ks hKs hG
  obtain ⟨z1, z2, hz12, ⟨w1, hw1, hd1⟩, ⟨w2, hw2, hd2⟩⟩ :=
    two_of_count (Good C e u0 u1) hKs (by omega)
  have hz : z1 - z2 ≠ 0 := by intro h; exact hz12 (by grind)
  have hinv := Field.mul_inv_cancel hz
  let v1 : Word ι K := fun i c => (z1 - z2)⁻¹ * w1 i c + (-(z1 - z2)⁻¹) * w2 i c
  let v0 : Word ι K := fun i c => 1 * w1 i c + (-z1) * v1 i c
  have hv1 : C.mem v1 := C.lin _ _ _ _ hw1 hw2
  have hv0 : C.mem v0 := C.lin _ _ _ _ hw1 hv1
  -- where both `z1` and `z2` agree, `(u0, u1) = (v0, v1)`
  have hsolve : ∀ i, line u0 u1 z1 i = w1 i → line u0 u1 z2 i = w2 i →
      u0 i = v0 i ∧ u1 i = v1 i := by
    intro i h1 h2
    have h1' := fun c => congrFun h1 c
    have h2' := fun c => congrFun h2 c
    simp only [line] at h1' h2'
    constructor <;> funext c <;> simp only [v0, v1] <;> grind
  have h2e : ∀ z, dist n (line u0 u1 z) (line v0 v1 z) ≤ 2 * e := by
    intro z
    refine Nat.le_trans (count_mono_mem _ (F := fun i => line u0 u1 z1 i ≠ w1 i ∨
        line u0 u1 z2 i ≠ w2 i) ?_) (Nat.le_trans (count_or_le _ _ _) (by unfold dist at hd1 hd2; omega))
    intro i _ h
    refine Classical.byContradiction fun hno => h ?_
    simp only [_root_.not_or, Classical.not_not] at hno
    obtain ⟨e0, e1⟩ := hsolve i hno.1 hno.2
    funext c; simp only [line]; rw [e0, e1]
  refine ca_of_affine C hv0 hv1 Ks hKs (by omega) fun z ⟨w, hw, hdw⟩ => ?_
  have hwl : ∀ i, i < n → w i = line v0 v1 z i := by
    apply C.sep w _ hw (C.line_mem hv0 hv1 z)
    have := dist_triangle n w (line u0 u1 z) (line v0 v1 z)
    have := dist_comm n w (line u0 u1 z)
    have := h2e z
    omega
  rwa [dist_congr (fun _ _ => rfl) hwl] at hdw

/-- **Strong line lemma at `d/3`** for every linear code with vector symbols
(interleaved codes included): at most `e + 1` challenges in any
duplicate-free list violate the containment conclusion. -/
theorem strong_line_d3 {n d : Nat} (C : LinCode ι K n d) {e : Nat} (he : 3 * e < d)
    (u0 u1 : Word ι K) (Ks : List K) (hKs : Ks.Nodup) :
    count Ks (fun z => ¬ Strong C e u0 u1 z) ≤ e + 1 := by
  have := strong_of_gap C (by omega) (gap_d3 C he) u0 u1 Ks hKs
  rwa [Nat.max_eq_left (Nat.le_succ e)] at this

end

/-! ## Interleaving a scalar code -/

section
variable {K : Type} [Field K]

/-- The interleaved code: every column (coordinate `j : J`) is a codeword of
the scalar code `C`. -/
def LinCode.interleave {n d : Nat} (C : LinCode Unit K n d) (J : Type) : LinCode J K n d where
  mem U := ∀ j, C.mem fun i _ => U i j
  zero := fun _ => C.zero
  lin u v a b hu hv j := C.lin _ _ a b (hu j) (hv j)
  sep u v hu hv hd i hi := by
    funext j
    have := C.sep _ _ (hu j) (hv j)
      (Nat.lt_of_le_of_lt (dist_mono (u := fun i (_ : Unit) => u i j) (v := fun i _ => v i j)
        (u' := u) (v' := v) fun i _ h e => h (by funext _; exact congrFun e j)) hd) i hi
    exact congrFun this ()

/-- Rows of a scalar code are `Unit`-indexed: eta for `Unit`. -/
theorem unit_eta (w : Word Unit K) : (fun i (_ : Unit) => w i ()) = w := by
  funext i u; cases u; rfl

/-- **Interleaving preserves the line proximity gap** (same threshold), for
`2e < d` and `e + 1 ≤ ε`. -/
theorem gap_interleave {n d : Nat} (C : LinCode Unit K n d) {e ε : Nat} (he : 2 * e < d)
    (hε : e + 1 ≤ ε) (hgap : LineGap C e ε) (J : Type) : LineGap (C.interleave J) e ε := by
  classical
  intro U0 U1 Ks hKs hG
  let row : Word J K → J → Word Unit K := fun U j i _ => U i j
  have hrowd : ∀ (U V : Word J K) j, dist n (row U j) (row V j) ≤ dist n U V :=
    fun U V j => dist_mono (u := row U j) (v := row V j) (u' := U) (v' := V)
      fun i _ h e => h (by funext _; exact congrFun e j)
  have hgood : ∀ j z, Good (C.interleave J) e U0 U1 z → Good C e (row U0 j) (row U1 j) z :=
    fun j z ⟨w, hw, hd⟩ => ⟨row w j, hw j, Nat.le_trans (hrowd (line U0 U1 z) w j) hd⟩
  have hca : ∀ j, CA C e (row U0 j) (row U1 j) := fun j =>
    hgap _ _ Ks hKs (Nat.lt_of_lt_of_le hG (count_mono _ (hgood j)))
  let v0 : J → Word Unit K := fun j => Classical.choose (hca j)
  let v1 : J → Word Unit K := fun j => Classical.choose (Classical.choose_spec (hca j))
  have hv : ∀ j, C.mem (v0 j) ∧ C.mem (v1 j) ∧ count (List.range n)
      (fun i => row U0 j i ≠ v0 j i ∨ row U1 j i ≠ v1 j i) ≤ e :=
    fun j => Classical.choose_spec (Classical.choose_spec (hca j))
  let V0 : Word J K := fun i j => v0 j i ()
  let V1 : Word J K := fun i j => v1 j i ()
  have hV0 : (C.interleave J).mem V0 := fun j => by
    show C.mem fun i _ => v0 j i (); rw [unit_eta]; exact (hv j).1
  have hV1 : (C.interleave J).mem V1 := fun j => by
    show C.mem fun i _ => v1 j i (); rw [unit_eta]; exact (hv j).2.1
  refine ca_of_affine (C.interleave J) hV0 hV1 Ks hKs (by omega) fun z ⟨w, hw, hdw⟩ => ?_
  have hwl : ∀ i, i < n → w i = line V0 V1 z i := by
    intro i hi
    funext j
    have hdl : dist n (line (row U0 j) (row U1 j) z) (line (v0 j) (v1 j) z) ≤ e := by
      refine Nat.le_trans (count_mono_mem _ ?_) (hv j).2.2
      intro i' _ h
      refine Classical.byContradiction fun hno => h ?_
      simp only [_root_.not_or, Classical.not_not] at hno
      funext c; simp only [line]; rw [hno.1, hno.2]
    have hdw' : dist n (line (row U0 j) (row U1 j) z) (row w j) ≤ e :=
      Nat.le_trans (hrowd (line U0 U1 z) w j) hdw
    have := C.unique he (hw j) (C.line_mem (hv j).1 (hv j).2.1 z) hdw' hdl i hi
    exact congrFun this ()
  rwa [dist_congr (fun _ _ => rfl) hwl] at hdw

end
end ZkFormal.Udr
