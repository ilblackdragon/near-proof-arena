import NearSpecV3.Successor.ReshardCore
import FinalM5d.Init

/-!
# FinalM5d.WalkSel — the main slot of `walkSegment` on a single-epoch segment (G-4)

The checker's resharding walk (`Successor.walkSegment`, `chunk_validation.rs:144-253`) picks the
main block `b2i`, its shard and its layout; the intake then reads the main chunk slot
`B2.slots[Lmain.index mainShard]` and its `prev_state_root` (`E2E/Machine.lean`, `intakeC`).

**`walk_single`.** If the claim's epoch table has one record `ep` (`c.epochs = [ep]`, what the
INIT AIR checks: `#epochs = 1`) and its layout decodes to `L`, then every successful walk from
`shard0` has `mainShard = shard0`, `mainLayout = ep.shardLayout`, and `b2i` is the **first** block
whose slot `L.index shard0` is new (`height_included = height`) — the D2 rule
`blks.findIdx? isNew` (`ChunkValidationD2`). No layout boundary can occur (every layout lookup
returns `ep.shardLayout`), so neither the resharding transitions nor the parent-shard step apply.
**`main_slot_single`** restates it for the intake's `mainIdx` / `slotB2`. This is the definition
the INIT AIR's selection mirrors (`InitSel`: `LAY` finds `L.index shard`, `BLK` the first new slot
at that index).

The proof follows the loop: `pre` (before the first new block: `seen = 0`, `shard = shard0`,
`main` = the current block), then `forIn_inv` (after it: `seen ≥ 1`, `main` frozen).
-/

namespace FinalM5d.WalkSel
open NearSpec NearSpecV3 NearSpecV3.Successor

/-- `P_CH`: the claim's `chain_id` length prefix follows the two fixed tags and the `u32` protocol
version (`ClaimV3.decodeClaimE`). -/
theorem p_ch_eq : InitT.P_CH = (borshBytes claimTag).length + (borshBytes statementIdV3).length + 4 := by
  decide

abbrev St := Nat × Nat × List WalkTransition × List (Nat × Nat) × Option (Nat × Nat × Bytes) × Option Nat

theorem bind_ok {α β ε : Type} {x : Except ε α} {g : α → Except ε β} {y : β}
    (h : (x >>= g) = .ok y) : ∃ a, x = .ok a ∧ g a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Generic: an invariant preserved by every successful step holds of `forIn`'s result. -/
theorem forIn_inv {α σ ε : Type} (f : α → σ → Except ε (ForInStep σ)) (I : σ → Prop)
    (hf : ∀ x s s', I s → f x s = .ok (.yield s') → I s')
    (hd : ∀ x s s', I s → f x s = .ok (.done s') → I s') :
    ∀ (xs : List α) (s r : σ), I s → forIn xs s f = .ok r → I r := by
  intro xs
  induction xs with
  | nil => intro s r hs h; simp at h; cases h; exact hs
  | cons x xs ih =>
    intro s r hs h
    rw [List.forIn_cons] at h
    obtain ⟨a, ha, hk⟩ := bind_ok h
    cases a with
    | done s' =>
      have e : s' = r := by simpa [pure, Except.pure] using hk
      subst e; exact hd x s s' hs ha
    | yield s' => exact ih s' r (hf x s s' hs ha) hk


theorem pre {F : Nat → St → Except String (ForInStep St)} (q : Nat → Bool) (s0 : Nat) (lb : Bytes)
    (hstep : ∀ i pu m sp res, F i (s0, 0, pu, [], m, sp) = .ok res →
      (q i = true ∧ ∃ pu' sp', res = .yield (s0, 1, pu', [(i, s0)], some (i, s0, lb), sp')) ∨
      (q i = false ∧ ∃ pu' sp', res = .yield (s0, 0, pu', [], some (i, s0, lb), sp')))
    (hpost : ∀ i se pu so m sp (s' : St), 1 ≤ se →
      (F i (s0, se, pu, so, m, sp) = .ok (.yield s') ∨ F i (s0, se, pu, so, m, sp) = .ok (.done s')) →
      s'.1 = s0 ∧ 1 ≤ s'.2.1 ∧ s'.2.2.2.2.1 = m) :
    ∀ n k pu m sp (r : St), forIn (List.range' k n) (s0, 0, pu, [], m, sp) F = .ok r →
      (∃ j, k ≤ j ∧ j < k + n ∧ q j = true ∧ (∀ i, k ≤ i → i < j → q i = false) ∧
        r.2.2.2.2.1 = some (j, s0, lb)) ∨
      (r.2.2.2.1 = [] ∧ ∀ i, k ≤ i → i < k + n → q i = false) := by
  intro n
  induction n with
  | zero =>
    intro k pu m sp r h
    simp [pure, Except.pure] at h
    subst h
    right; exact ⟨rfl, fun i h1 h2 => by omega⟩
  | succ n ih =>
    intro k pu m sp r h
    rw [List.range'_succ, List.forIn_cons] at h
    obtain ⟨a, ha, hk⟩ := bind_ok h
    rcases hstep k pu m sp a ha with ⟨hq, pu', sp', rfl⟩ | ⟨hq, pu', sp', rfl⟩
    · left
      have hI := forIn_inv F (fun s : St => s.1 = s0 ∧ 1 ≤ s.2.1 ∧ s.2.2.2.2.1 = some (k, s0, lb))
        (fun x s s' hs hx => by
          obtain ⟨sh, se, pu, so, m, sp⟩ := s
          obtain ⟨h1, h2, h3⟩ := hs
          simp only at h1 h2 h3; subst h1 h3
          exact hpost x se pu so _ sp s' h2 (Or.inl hx))
        (fun x s s' hs hx => by
          obtain ⟨sh, se, pu, so, m, sp⟩ := s
          obtain ⟨h1, h2, h3⟩ := hs
          simp only at h1 h2 h3; subst h1 h3
          exact hpost x se pu so _ sp s' h2 (Or.inr hx))
        _ _ r ⟨rfl, by simp, rfl⟩ hk
      exact ⟨k, Nat.le_refl _, by omega, hq, fun i h1 h2 => by omega, hI.2.2⟩
    · rcases ih (k + 1) pu' (some (k, s0, lb)) sp' r hk with ⟨j, h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩
      · left
        refine ⟨j, by omega, by omega, h3, fun i hi1 hi2 => ?_, h5⟩
        by_cases e : i = k
        · subst e; exact hq
        · exact h4 i (by omega) hi2
      · right
        refine ⟨h1, fun i hi1 hi2 => ?_⟩
        by_cases e : i = k
        · subst e; exact hq
        · exact h2 i (by omega) (by omega)

def isNewAt (L : NearSpecV3.Layout) (s : Nat) (b : Blk) : Bool :=
  match L.index s with
  | some x => (match b.slots[x]? with | some (sl, _) => sl.heightIncluded == b.hdr.height | none => false)
  | none => false

theorem walk_single {c : Claim} {ep : EpochRec} {blks : List Blk} {ae : List Bytes} {s0 : Nat}
    {wk : Walk} {L : NearSpecV3.Layout} (hE : c.epochs = [ep]) (hL : decodeLayout ep.shardLayout = .ok L)
    (hw : walkSegment c blks ae s0 = .ok wk) :
    wk.mainShard = s0 ∧ wk.mainLayout = ep.shardLayout ∧
      (∃ b, blks[wk.b2i]? = some b ∧ isNewAt L s0 b = true) ∧
      ∀ i, i < wk.b2i → ∃ b, blks[i]? = some b ∧ isNewAt L s0 b = false := by
  unfold walkSegment at hw
  dsimp only at hw
  obtain ⟨r, hr, hk⟩ := bind_ok hw
  rw [List.range_eq_range'] at hr
  have hlb : ∀ e y, layoutBytesOf c e = .ok y → y = ep.shardLayout := by
    intro e y h
    simp only [layoutBytesOf, hE, List.find?] at h
    cases hq : (ep.epochId == e) <;> simp only [hq] at h
    · cases h
    · cases h; rfl
  refine (fun this => ?_) (pre (fun i => match blks[i]? with | some b => isNewAt L s0 b | none => false)
    s0 ep.shardLayout ?hs ?hp blks.length 0 [] none none r hr)
  case hs =>
    clear hk hr hw
    intro i pu m sp res h
    split at h
    · rename_i b hb
      simp only [hb]
      split at h
      · rename_i e he
        cases hA : layoutBytesOf c e with
        | error _ => simp [hA, bind, Except.bind, pure, Except.pure] at h
        | ok y =>
        cases hO : layoutBytesOf c b.hdr.epochId with
        | error _ => simp [hA, hO, bind, Except.bind, pure, Except.pure] at h
        | ok y' =>
        obtain rfl := hlb _ _ hA
        obtain rfl := hlb _ _ hO
        simp only [hA, hO, hL, bind, Except.bind, pure, Except.pure, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add,
          beq_self_eq_true, List.nil_append] at h
        split at h
        · simp at h
        · split at h
          · rename_i x hx
            rcases hs : b.slots[x]? with _ | ⟨sl, ci⟩
            · cases hg : b.isGenesis <;>
                simp [isNewAt, hx, hs, hg, throw, throwThe, MonadExceptOf.throw] at h ⊢ <;>
                exact ⟨_, _, h.symm⟩
            · cases hh : (sl.heightIncluded == b.hdr.height) <;> cases hg : b.isGenesis <;>
                simp [isNewAt, hx, hs, hh, hg, throw, throwThe, MonadExceptOf.throw] at h ⊢ <;>
                exact ⟨_, _, h.symm⟩
          · simp [throw, throwThe, MonadExceptOf.throw] at h
      · simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    · simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  case hp =>
    clear hk hr hw
    intro i se pu so m sp s' hse h
    have h0 : (se == 0) = false := by simp; omega
    rcases h with h | h <;>
    · split at h
      · rename_i b hb
        split at h
        · rename_i e he
          cases hA : layoutBytesOf c e with
          | error _ => simp [hA, bind, Except.bind, pure, Except.pure] at h
          | ok y =>
          cases hO : layoutBytesOf c b.hdr.epochId with
          | error _ => simp [hA, hO, bind, Except.bind, pure, Except.pure] at h
          | ok y' =>
          obtain rfl := hlb _ _ hA
          obtain rfl := hlb _ _ hO
          simp only [hA, hO, hL, bind, Except.bind, pure, Except.pure, bne_self_eq_false, Bool.and_false,
            Bool.false_eq_true, ↓reduceIte, h0] at h
          split at h
          · simp at h
          · split at h
            · rename_i x hx
              have h1 : se ≠ 0 := by omega
              rcases hs : b.slots[x]? with _ | ⟨sl, ci⟩
              · cases hg : b.isGenesis <;>
                by_cases h2 : se = 1 <;>
                simp [hs, hg, h1, h2, throw, throwThe, MonadExceptOf.throw] at h ⊢ <;>
                (try subst h) <;> simp <;> omega
              · cases hh : (sl.heightIncluded == b.hdr.height) <;>
                cases hg : b.isGenesis <;>
                by_cases h2 : se = 1 <;>
                simp [hs, hh, hg, h1, h2, throw, throwThe, MonadExceptOf.throw] at h ⊢ <;>
                (try subst h) <;> simp <;> omega
            · simp [throw, throwThe, MonadExceptOf.throw] at h
        · simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
      · simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨sh, se, pu, so, m, sp⟩ := r
  rcases this with ⟨j, -, hj, hq, hlt, hm⟩ | ⟨hso, -⟩
  · simp only at hm; subst hm
    cases hse : so.isEmpty <;> cases sp <;>
      simp [hse, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hk
    subst hk
    refine ⟨rfl, rfl, ?_, fun i hi => ?_⟩
    · simp only; revert hq; cases blks[j]? <;> simp
    · simp only at hi ⊢
      have := hlt i (Nat.zero_le _) hi
      have hib : i < blks.length := by omega
      rw [List.getElem?_eq_getElem hib] at this ⊢
      exact ⟨_, rfl, this⟩
  · simp only at hso; subst hso
    cases m with
    | none => simp [throw, throwThe, MonadExceptOf.throw] at hk
    | some t =>
      obtain ⟨a, b, d⟩ := t
      simp [throw, throwThe, MonadExceptOf.throw] at hk

/-- **The intake's main slot on a single-epoch segment** (`intakeC` reads `Lmain := decodeLayout
wk.mainLayout`, `mainIdx := Lmain.index wk.mainShard`, `slotB2 := B2.slots[mainIdx]`): the index
is `L.index shard0 = some x`, the main block is the first whose slot `x` is new, and that slot is
new. -/
theorem main_slot_single {c : Claim} {ep : EpochRec} {blks : List Blk} {ae : List Bytes} {s0 : Nat}
    {wk : Walk} {L : NearSpecV3.Layout} (hE : c.epochs = [ep]) (hL : decodeLayout ep.shardLayout = .ok L)
    (hw : walkSegment c blks ae s0 = .ok wk) :
    decodeLayout wk.mainLayout = .ok L ∧ wk.mainShard = s0 ∧
      ∃ x, L.index s0 = some x ∧
        (∃ b sl ci, blks[wk.b2i]? = some b ∧ b.slots[x]? = some (sl, ci) ∧
          sl.heightIncluded = b.hdr.height) ∧
        ∀ i, i < wk.b2i → ∃ b, blks[i]? = some b ∧
          ∀ sl ci, b.slots[x]? = some (sl, ci) → sl.heightIncluded ≠ b.hdr.height := by
  obtain ⟨h1, h2, ⟨b, hb, hn⟩, hlt⟩ := walk_single hE hL hw
  refine ⟨h2 ▸ hL, h1, ?_⟩
  unfold isNewAt at hn
  rcases hx : L.index s0 with _ | x
  · rw [hx] at hn; cases hn
  · rw [hx] at hn
    refine ⟨x, rfl, ?_, fun i hi => ?_⟩
    · simp only at hn
      rcases hs : b.slots[x]? with _ | ⟨sl, ci⟩
      · rw [hs] at hn; cases hn
      · rw [hs] at hn
        exact ⟨b, sl, ci, hb, hs, by simpa using hn⟩
    · obtain ⟨b', hb', hn'⟩ := hlt i hi
      refine ⟨b', hb', fun sl ci hs => ?_⟩
      unfold isNewAt at hn'
      rw [hx] at hn'
      simp only at hn'
      rw [hs] at hn'
      simpa using hn'

end FinalM5d.WalkSel