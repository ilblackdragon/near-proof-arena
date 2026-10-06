import ZkFormal.NearV3.Sched.Model

/-!
# ZkFormal.NearV3.Sched.View.ScanSpec — the scan order of `incsOf` (spec side of `sscV3`)

The scan table walks the 40 bitmap positions keeping `(cur, j)`: the value of the last set bit
(or `base`) and the number of set bits seen. `stAt vals bm b c` is that state before position
`c`. Facts:

* `incsOf_getD` — at a set position `c < 40`, the increase with index `(stAt … c).2` is
  `vals[c] − (stAt … c).1`;
* `incsOf_length_stAt` — `(incsOf p bm).length = (stAt … 40).2`;
* `stAt_snd_lt` — set positions get strictly increasing indices (each increase is sent once);
* `stAt_fst_le` — the running value is below the value of any later position (so the
  increases are natural differences).
-/

namespace ZkFormal.NearV3.Sched.ScanSpec

open NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched

/-- Scan state before bit position `c`: (value of the last set bit below `c`, or `b`;
number of set bits below `c`). -/
def stAt (vals : List Nat) (bm : List UInt8) (b : Nat) : Nat → Nat × Nat
  | 0 => (b, 0)
  | c + 1 => if getBit bm c then (vals.getD c 0, (stAt vals bm b c).2 + 1) else stAt vals bm b c

theorem stAt_succ (vals : List Nat) (bm : List UInt8) (b c : Nat) :
    stAt vals bm b (c + 1) =
      if getBit bm c then (vals.getD c 0, (stAt vals bm b c).2 + 1) else stAt vals bm b c := rfl

/-- Value of the last element of a position list (or `p`). -/
def lastv (vals : List Nat) : Nat → List Nat → Nat
  | p, [] => p
  | _, a :: as => lastv vals (vals.getD a 0) as

theorem incsFrom_append (vals : List Nat) :
    ∀ (p : Nat) (A B : List Nat),
      incsFrom vals p (A ++ B) = incsFrom vals p A ++ incsFrom vals (lastv vals p A) B
  | _, [], _ => rfl
  | p, a :: A, B => by
    simp only [List.cons_append, incsFrom, lastv, incsFrom_append vals _ A B]

theorem lastv_append (vals : List Nat) :
    ∀ (p : Nat) (A B : List Nat), lastv vals p (A ++ B) = lastv vals (lastv vals p A) B
  | _, [], _ => rfl
  | p, a :: A, B => by simp only [List.cons_append, lastv, lastv_append vals _ A B]

theorem incsFrom_length' (vals : List Nat) :
    ∀ (p : Nat) (cs : List Nat), (incsFrom vals p cs).length = cs.length
  | _, [] => rfl
  | p, c :: cs => by simp [incsFrom, incsFrom_length' vals _ cs]

theorem filter_range_succ (g : Nat → Bool) (c : Nat) :
    (List.range (c + 1)).filter g = (List.range c).filter g ++ (if g c then [c] else []) := by
  rw [List.range_succ, List.filter_append]
  cases h : g c <;> simp [h]

theorem stAt_spec (vals : List Nat) (bm : List UInt8) (b : Nat) :
    ∀ c, lastv vals b ((List.range c).filter (getBit bm)) = (stAt vals bm b c).1 ∧
      ((List.range c).filter (getBit bm)).length = (stAt vals bm b c).2
  | 0 => by simp [stAt, lastv]
  | c + 1 => by
    obtain ⟨h1, h2⟩ := stAt_spec vals bm b c
    rw [filter_range_succ, stAt_succ]
    cases h : getBit bm c
    · simp [h1, h2]
    · simp [lastv_append, lastv, h1, h2]

theorem stAt_snd_le (vals : List Nat) (bm : List UInt8) (b : Nat) :
    ∀ c, (stAt vals bm b c).2 ≤ c
  | 0 => Nat.le_refl _
  | c + 1 => by
    have := stAt_snd_le vals bm b c
    rw [stAt_succ]; split <;> (try dsimp only) <;> omega

theorem stAt_snd_mono (vals : List Nat) (bm : List UInt8) (b c : Nat) :
    ∀ d, (stAt vals bm b c).2 ≤ (stAt vals bm b (c + d)).2
  | 0 => Nat.le_refl _
  | d + 1 => by
    have := stAt_snd_mono vals bm b c d
    rw [show c + (d + 1) = c + d + 1 by omega, stAt_succ]; split <;> (try dsimp only) <;> omega

/-- Set positions get strictly increasing indices. -/
theorem stAt_snd_lt (vals : List Nat) (bm : List UInt8) (b : Nat) {c c' : Nat} (hcc : c < c')
    (hc : getBit bm c = true) : (stAt vals bm b c).2 < (stAt vals bm b c').2 := by
  have h1 : (stAt vals bm b (c + 1)).2 = (stAt vals bm b c).2 + 1 := by rw [stAt_succ, if_pos hc]
  have h2 := stAt_snd_mono vals bm b (c + 1) (c' - (c + 1))
  rw [show c + 1 + (c' - (c + 1)) = c' by omega] at h2
  omega

/-- The increase list split at a set position `c`. -/
theorem incsFrom_at (vals : List Nat) (bm : List UInt8) (b : Nat) {c : Nat} (hc40 : c < 40)
    (hc : getBit bm c = true) :
    incsFrom vals b ((List.range 40).filter (getBit bm)) =
      incsFrom vals b ((List.range c).filter (getBit bm)) ++
        ((vals.getD c 0 - (stAt vals bm b c).1) ::
          incsFrom vals (vals.getD c 0) ((List.range' (c + 1) (39 - c)).filter (getBit bm))) := by
  have e : List.range 40 = List.range (c + 1) ++ List.range' (c + 1) (39 - c) := by
    have h := (List.range'_append_1 (s := 0) (m := c + 1) (n := 39 - c))
    rw [Nat.zero_add, show c + 1 + (39 - c) = 40 by omega] at h
    rw [List.range_eq_range', List.range_eq_range', h]
  rw [e, List.filter_append, filter_range_succ, if_pos hc, List.append_assoc,
    incsFrom_append, List.singleton_append, incsFrom, (stAt_spec vals bm b c).1]

theorem incsOf_getD (p : Params) (bm : List UInt8) {c : Nat} (hc40 : c < 40)
    (hc : getBit bm c = true) :
    (incsOf p bm).getD (stAt (requestValues p) bm p.base c).2 0 =
      (requestValues p).getD c 0 - (stAt (requestValues p) bm p.base c).1 := by
  unfold incsOf setBits
  rw [incsFrom_at _ bm _ hc40 hc]
  have hl : (incsFrom (requestValues p) p.base ((List.range c).filter (getBit bm))).length =
      (stAt (requestValues p) bm p.base c).2 := by
    rw [incsFrom_length', (stAt_spec _ bm _ c).2]
  rw [← hl, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem incsOf_length_stAt (p : Params) (bm : List UInt8) :
    (incsOf p bm).length = (stAt (requestValues p) bm p.base 40).2 := by
  unfold incsOf setBits
  rw [incsFrom_length', (stAt_spec _ bm _ 40).2]

theorem requestValues_getD (p : Params) {c : Nat} (hc : c < 40) :
    (requestValues p).getD c 0 = p.base + (p.maxSingleGrant - p.base) * (c + 1) / 40 := by
  simp [requestValues, List.getD_eq_getElem?_getD, hc]

theorem rv_mono (p : Params) {c c' : Nat} (hcc : c ≤ c') (hc' : c' < 40) :
    (requestValues p).getD c 0 ≤ (requestValues p).getD c' 0 := by
  rw [requestValues_getD p (by omega), requestValues_getD p hc']
  have := Nat.div_le_div_right (c := 40)
    (Nat.mul_le_mul_left (p.maxSingleGrant - p.base) (show c + 1 ≤ c' + 1 by omega))
  omega

/-- The running value is at most the value of any position `≥ c`. -/
theorem stAt_fst_le (p : Params) (bm : List UInt8) :
    ∀ c, ∀ c', c ≤ c' → c' < 40 → (stAt (requestValues p) bm p.base c).1 ≤ (requestValues p).getD c' 0
  | 0, c', _, hc' => by
    show p.base ≤ _
    rw [requestValues_getD p hc']; omega
  | c + 1, c', hcc, hc' => by
    rw [stAt_succ]
    split
    · exact rv_mono p (by omega) hc'
    · exact stAt_fst_le p bm c c' (by omega) hc'

end ZkFormal.NearV3.Sched.ScanSpec
