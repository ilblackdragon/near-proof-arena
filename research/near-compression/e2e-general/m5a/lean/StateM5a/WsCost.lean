import StateM5a.Ws
import StateM5a.FieldRows

/-!
# StateM5a.WsCost — the M5a-3 working-set segment: memory chain and row facts

M5a-3 replaces the per-write Merkle path (`WSA` hashing `4 + 2D` compressions) by

* write accesses linked per working-set entry by **offline memory checking** on `WM`: the
  segment's leaf row (`WSL`) sends the entry's value at time `0`, an access at time `t` consumes
  `(old, prev)` with `prev < t` (`WSA`'s gap bytes) and sends `(new, t)`, and the leaf row
  consumes the last `(new', id')`;
* one batched path update per segment (`WSL`, `WSP`; `Merkle.batch_update_sound`).

`chain_sound`: if the messages of one entry balance (the sends are a permutation of the
receives) and every access consumed an earlier time, then — listing the accesses latest first —
every access read the value written by the access just before it in time (the opening value for
the first one), the times are distinct, and the leaf row closes with the latest written value
(`chain_sound_any`: for the accesses in any order, through the time-sorted permutation).  For the
`WM` bus, whose messages carry `(seg, kd)`, this applies to the sub-multiset of each `(seg, kd)`
(a filter of a permutation is a permutation).

Row facts at field level (BabyBear, as `FieldRows`): `wsa_gap` (the time gap bytes force
`idp < t` for segment-local times `< 2^24`), `wsp_keep` (an untouched child is the same digest
in both trees), `wsp_child` (an active path node has a touched child), `wsp_off` (an inactive
row has no multiplicity), `wsl_kd` (a touched leaf's `kd` limbs are 16-bit), and
`leafLimb_inj` (a leaf block high limb `kd + 2^16·x` determines `kd < 2^16` and `x < 2^8`).
-/

namespace StateM5a.WsCost

/-! ## Offline memory checking of one entry -/

/-- One access of an entry on `WM`: it consumes `(old, prev)` and sends `(new, t)`. -/
structure Acc (V : Type) where
  t : Nat
  prev : Nat
  old : V
  new : V

variable {V : Type}

def Acc.snd (a : Acc V) : V × Nat := (a.new, a.t)
def Acc.rcv (a : Acc V) : V × Nat := (a.old, a.prev)

/-- The latest written value (accesses listed latest first), or the opening value. -/
def lastVal (v0 : V) : List (Acc V) → V
  | [] => v0
  | a :: _ => a.new

def lastT : List (Acc V) → Nat
  | [] => 0
  | a :: _ => a.t

/-- Every access read the value and time of the access just before it. -/
def Reads (v0 : V) : List (Acc V) → Prop
  | [] => True
  | a :: rest => (a.old = lastVal v0 rest ∧ a.prev = lastT rest) ∧ Reads v0 rest

/-- **Memory chain, time-sorted.** -/
theorem chain_sound (v0 : V) : ∀ (acc : List (Acc V)) (vEnd : V) (idEnd : Nat),
    acc.Pairwise (fun a b => b.t ≤ a.t) → (∀ a ∈ acc, a.prev < a.t) →
    List.Perm ((v0, 0) :: acc.map Acc.snd) ((vEnd, idEnd) :: acc.map Acc.rcv) →
    vEnd = lastVal v0 acc ∧ idEnd = lastT acc ∧ Reads v0 acc
  | [], vEnd, idEnd, _, _, hp => by
    have h := List.singleton_perm_singleton.mp hp
    simp only [Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm, trivial⟩
  | m :: rest, vEnd, idEnd, hs, ht, hp => by
    rw [List.pairwise_cons] at hs
    have hmem : m.snd ∈ (vEnd, idEnd) :: (m :: rest).map Acc.rcv :=
      hp.subset (by simp)
    have hm := ht m (by simp)
    have hend : (vEnd, idEnd) = m.snd := by
      simp only [List.map_cons, List.mem_cons, List.mem_map] at hmem
      rcases hmem with h | h | ⟨a, ha, h⟩
      · exact h.symm
      · simp only [Acc.snd, Acc.rcv, Prod.mk.injEq] at h; omega
      · simp only [Acc.snd, Acc.rcv, Prod.mk.injEq] at h
        have := hs.1 a ha
        have := ht a (by simp [ha])
        omega
    rw [hend] at hp
    have hp' : List.Perm ((v0, 0) :: rest.map Acc.snd) (m.rcv :: rest.map Acc.rcv) := by
      have := (List.Perm.swap (v0, 0) m.snd (rest.map Acc.snd)).trans (by simpa using hp)
      exact this.cons_inv
    obtain ⟨h1, h2, h3⟩ := chain_sound v0 rest m.old m.prev hs.2
      (fun a ha => ht a (by simp [ha])) hp'
    simp only [Acc.snd, Prod.mk.injEq] at hend
    exact ⟨hend.1, hend.2, ⟨h1, h2⟩, h3⟩

/-- In a balanced chain the times strictly decrease along the latest-first list. -/
theorem chain_strict (v0 : V) : ∀ (acc : List (Acc V)),
    acc.Pairwise (fun a b => b.t ≤ a.t) → (∀ a ∈ acc, a.prev < a.t) → Reads v0 acc →
    acc.Pairwise (fun a b => b.t < a.t)
  | [], _, _, _ => List.Pairwise.nil
  | m :: rest, hs, ht, hr => by
    rw [List.pairwise_cons] at hs ⊢
    refine ⟨fun b hb => ?_, chain_strict v0 rest hs.2 (fun a ha => ht a (by simp [ha])) hr.2⟩
    have hm := ht m (by simp)
    have hprev := hr.1.2
    match rest, hb, hs with
    | c :: rest', hb, hs =>
      simp only [lastT] at hprev
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · omega
      · have := (List.pairwise_cons.mp hs.2).1 b hb
        omega

/-- **Memory chain, any order**: the accesses, sorted by time (latest first), are a permutation
of the given ones with strictly decreasing times, each reading its predecessor's value, and the
closing message is the latest value. -/
theorem chain_sound_any (v0 : V) (acc : List (Acc V)) (vEnd : V) (idEnd : Nat)
    (ht : ∀ a ∈ acc, a.prev < a.t)
    (hp : List.Perm ((v0, 0) :: acc.map Acc.snd) ((vEnd, idEnd) :: acc.map Acc.rcv)) :
    ∃ s : List (Acc V), s.Perm acc ∧ s.Pairwise (fun a b => b.t < a.t) ∧
      vEnd = lastVal v0 s ∧ idEnd = lastT s ∧ Reads v0 s := by
  let le : Acc V → Acc V → Bool := fun a b => decide (b.t ≤ a.t)
  let s := acc.mergeSort le
  have hperm : s.Perm acc := List.mergeSort_perm acc le
  have hsort : s.Pairwise (fun a b => b.t ≤ a.t) := by
    have := List.pairwise_mergeSort (le := le)
      (fun a b c h1 h2 => by simp only [le, decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) acc
    exact this.imp (fun h => by simpa [le] using h)
  have ht' : ∀ a ∈ s, a.prev < a.t := fun a ha => ht a (hperm.subset ha)
  have hp' : List.Perm ((v0, 0) :: s.map Acc.snd) ((vEnd, idEnd) :: s.map Acc.rcv) :=
    ((hperm.map Acc.snd).cons _).trans (hp.trans ((hperm.symm.map Acc.rcv).cons _))
  obtain ⟨h1, h2, h3⟩ := chain_sound v0 s vEnd idEnd hsort ht' hp'
  exact ⟨s, hperm, chain_strict v0 s hsort ht' h3, h1, h2, h3⟩

/-! ## The leaf block's high limbs -/

/-- `kd + 2^16·x` with `kd < 2^16` and `x < 2^8` determines both (as BabyBear elements too: the
value is `< 2^24 < p`). -/
theorem leafLimb_inj {k x k' x' : Nat} (hk : k < 2 ^ 16) (hk' : k' < 2 ^ 16) (hx : x < 2 ^ 8)
    (hx' : x' < 2 ^ 8) (h : (k + 65536 * x) % 2013265921 = (k' + 65536 * x') % 2013265921) :
    k = k' ∧ x = x' := by
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  omega

/-! ## Row facts from the constraints (BabyBear) -/

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound FieldRows

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp} {D : Nat}

local notation "P" => 2013265921

theorem wsa_mem_gap : Wsa.c "act" * (Wsa.c "t" - Wsa.c "idp" - 1 -
    sumE ((List.range DT_BYTES).map fun k => K (256 ^ k) * Wsa.c "dt" k)) ∈ Wsa.constraints := by
  unfold Wsa.constraints; simp

/-- **`WSA` time gap**: an active access with gap bytes `< 2^8` and segment-local times `< 2^24`
consumed an earlier time (`chain_sound`'s premise `prev < t`). -/
theorem wsa_gap (hc : ∀ e ∈ Wsa.table.constraints, e.eval tr t r pub = 0)
    (hact : ev tr t r pub (Wsa.c "act") = 1)
    (hdt : ∀ k < DT_BYTES, ev tr t r pub (Wsa.c "dt" k) < 256)
    (htt : ev tr t r pub (Wsa.c "t") < 2 ^ 24) (hip : ev tr t r pub (Wsa.c "idp") < 2 ^ 24) :
    ev tr t r pub (Wsa.c "idp") < ev tr t r pub (Wsa.c "t") := by
  have h := hold rfl hc wsa_mem_gap
  change ev tr t r pub (Expr.mul _ _) = 0 at h
  rw [ev_mul_gate _ hact] at h
  have h' := eq_of_sub h
  rw [ev_sub, ev_sub, ev_sumE] at h'
  have d0 := hdt 0 (by decide); have d1 := hdt 1 (by decide); have d2 := hdt 2 (by decide)
  simp only [DT_BYTES, List.range, List.range.loop, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, ev_hmul, K, ev_const, ev_one, Nat.reducePow, Nat.reduceMod, Nat.add_zero] at h'
  generalize ev tr t r pub (Wsa.c "dt" 0) = y0 at d0 h'
  generalize ev tr t r pub (Wsa.c "dt" 1) = y1 at d1 h'
  generalize ev tr t r pub (Wsa.c "dt" 2) = y2 at d2 h'
  generalize ev tr t r pub (Wsa.c "t") = a at htt h' ⊢
  generalize ev tr t r pub (Wsa.c "idp") = b at hip h' ⊢
  simp only [Nat.reduceSub, Nat.reduceMod, Nat.one_mul] at h'
  rw [Nat.mod_eq_of_lt (show y0 < P by omega), Nat.mod_eq_of_lt (show 256 * y1 < P by omega),
    Nat.mod_eq_of_lt (show 65536 * y2 < P by omega),
    Nat.mod_eq_of_lt (show y0 + (256 * y1 + 65536 * y2) < P by omega)] at h'
  rcases Nat.eq_zero_or_pos b with h0 | h0
  · subst h0; simp only [Nat.sub_zero, Nat.mod_self, Nat.add_zero] at h'
    rw [Nat.mod_eq_of_lt (show a < P by omega)] at h'
    omega
  · rw [Nat.mod_eq_of_lt (show P - b < P by omega)] at h'
    omega

theorem wsp_mem_keepL (j : Nat) (hj : j < 18) :
    (1 - Wsp.c "tl") * (Wsp.c "lo" j - Wsp.c "ln" j) ∈ Wsp.constraints D := by
  unfold Wsp.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  exact Or.inr ⟨j, hj, Or.inl rfl⟩

theorem wsp_mem_keepR (j : Nat) (hj : j < 18) :
    (1 - Wsp.c "tr") * (Wsp.c "ro" j - Wsp.c "rn" j) ∈ Wsp.constraints D := by
  unfold Wsp.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  exact Or.inr ⟨j, hj, Or.inr (Or.inl rfl)⟩

theorem one_sub_gate {x : Expr} (h : ev tr t r pub x = 0) : ev tr t r pub (1 - x) = 1 := by
  rw [ev_sub, h]; simp

/-- **`WSP` untouched child**: with `tl = 0` (`tr = 0`) the left (right) child is one digest in
the old and the new tree (`Merkle.Upd.keep`). -/
theorem wsp_keep (hc : ∀ e ∈ (Wsp.table D).constraints, e.eval tr t r pub = 0) (j : Nat) (hj : j < 18) :
    (ev tr t r pub (Wsp.c "tl") = 0 → ev tr t r pub (Wsp.c "lo" j) = ev tr t r pub (Wsp.c "ln" j)) ∧
    (ev tr t r pub (Wsp.c "tr") = 0 → ev tr t r pub (Wsp.c "ro" j) = ev tr t r pub (Wsp.c "rn" j)) := by
  constructor
  · intro h0
    have h := hold rfl hc (wsp_mem_keepL (D := D) j hj)
    change ev tr t r pub (Expr.mul _ _) = 0 at h
    rw [ev_mul_gate _ (one_sub_gate h0)] at h
    exact eq_of_sub h
  · intro h0
    have h := hold rfl hc (wsp_mem_keepR (D := D) j hj)
    change ev tr t r pub (Expr.mul _ _) = 0 at h
    rw [ev_mul_gate _ (one_sub_gate h0)] at h
    exact eq_of_sub h

theorem wsp_mem (s : String) (hs : s ∈ ["act", "tl", "tr"]) : bool (Wsp.c s) ∈ Wsp.constraints D := by
  unfold Wsp.constraints
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> simp

/-- **`WSP` active row**: it receives at least one touched child (so a path node never stands
for a free subtree; levels below `0` cannot be reached). -/
theorem wsp_child (hc : ∀ e ∈ (Wsp.table D).constraints, e.eval tr t r pub = 0)
    (hact : ev tr t r pub (Wsp.c "act") = 1) :
    ev tr t r pub (Wsp.c "tl") = 1 ∨ ev tr t r pub (Wsp.c "tr") = 1 := by
  have h := hold rfl hc (show Wsp.c "act" * (1 - Wsp.c "tl") * (1 - Wsp.c "tr") ∈ Wsp.constraints D by
    unfold Wsp.constraints; simp)
  have bl := bool_le (hold (tr := tr) (t := t) (r := r) (pub := pub) rfl hc (wsp_mem (D := D) "tl" (by simp)))
  have br := bool_le (hold (tr := tr) (t := t) (r := r) (pub := pub) rfl hc (wsp_mem (D := D) "tr" (by simp)))
  change ev tr t r pub (Expr.mul (Expr.mul _ _) _) = 0 at h
  rcases ev_mul_eq_zero h with h | h
  · rw [ev_mul_gate _ hact] at h
    rw [ev_sub] at h
    simp only [ev_one] at h
    generalize ev tr t r pub (Wsp.c "tl") = a at bl h ⊢
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp_all
  · rw [ev_sub] at h
    simp only [ev_one] at h
    generalize ev tr t r pub (Wsp.c "tr") = a at br h ⊢
    rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> simp_all

/-- **`WSP` inactive row**: no multiplicity (it cannot absorb a child's `PT` message or a root). -/
theorem wsp_off (hc : ∀ e ∈ (Wsp.table D).constraints, e.eval tr t r pub = 0)
    (h0 : ev tr t r pub (Wsp.c "act") = 0) :
    ev tr t r pub (Wsp.c "top") = 0 ∧ ev tr t r pub (Wsp.c "tl") = 0 ∧ ev tr t r pub (Wsp.c "tr") = 0 := by
  have g := one_sub_gate (tr := tr) (t := t) (r := r) (pub := pub) h0
  have k : ∀ s, (1 - Wsp.c "act") * Wsp.c s ∈ Wsp.constraints D → ev tr t r pub (Wsp.c s) = 0 := by
    intro s hs
    have h := hold rfl hc hs
    change ev tr t r pub (Expr.mul _ _) = 0 at h
    rwa [ev_mul_gate _ g] at h
  exact ⟨k "top" (by unfold Wsp.constraints; simp), k "tl" (by unfold Wsp.constraints; simp),
    k "tr" (by unfold Wsp.constraints; simp)⟩

/-- **`WSL` key digest**: with bytes `kb < 2^8` (`RNG`), every `kd` limb is `< 2^16`
(`leafLimb_inj`'s premise for the touched leaf's block). -/
theorem wsl_kd (hc : ∀ e ∈ Wsl.table.constraints, e.eval tr t r pub = 0) (j : Nat) (hj : j < 16)
    (hb : ∀ b < 32, ev tr t r pub (Wsl.c "kb" b) < 256) :
    ev tr t r pub (Wsl.c "kd" j) = 256 * ev tr t r pub (Wsl.c "kb" (2 * j)) + ev tr t r pub (Wsl.c "kb" (2 * j + 1)) ∧
    ev tr t r pub (Wsl.c "kd" j) < 2 ^ 16 := by
  have h := hold rfl hc (show Wsl.c "kd" j - (K 256 * Wsl.c "kb" (2 * j) + Wsl.c "kb" (2 * j + 1)) ∈
      Wsl.constraints by
    unfold Wsl.constraints
    simp only [List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨j, hj, rfl⟩)
  have h' := eq_of_sub h
  have b0 := hb (2 * j) (by omega); have b1 := hb (2 * j + 1) (by omega)
  simp only [ev_hadd, ev_hmul, K, ev_const, Nat.reduceMod] at h'
  rw [Nat.mod_eq_of_lt (show 256 * ev tr t r pub (Wsl.c "kb" (2 * j)) < P by omega),
    Nat.mod_eq_of_lt (by omega)] at h'
  omega

end StateM5a.WsCost
