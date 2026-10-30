import NearSpecV3.Successor.TierMono

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 O6 — resharding on segments without a genesis block (verdict level)

A resharding tier checks a segment without a genesis block with `checkReshardCoreObs`, which walks
the segment block by block in each block's own layout (`walkSegment`) and recomputes the split gate.
The non-resharding whole-state tiers run `checkD2CoreWithObs` (through the genesis-capable shell,
which on such segments is the same function, `checkD2CoreGWith_eq_of_segment`). That shell excludes
every segment whose epochs differ in layout (`c.same_layout`) or whose facts carry a split gate
(`c.no_split_gate`). On the remaining segments:

* `walk_one_layout`: the per-block walk with one layout and no genesis block is the plain two-phase
  scan for the first two new chunks; it yields `expectedWalk` exactly when the plain shell's
  `findIdx?` scans succeed with every slot count right, and otherwise rejects (never excludes).
* `checkD2CoreWithObs_vr_reshard`: the two shells then decide alike (`VR`): where the plain shell
  accepts, `ReshardCore` accepts; where it rejects, `ReshardCore` rejects, possibly with another
  reason (the check order differs; fixture `seed23-02-h10062-s5-c.child_layout_is_parent`:
  `slot count` vs `shard not in layout`), so only the verdict-level form `VRefines` holds.
* `checkSuccessor_resharding_vmono`: `VLift cfg {cfg with resharding := true}` on every whole-state
  configuration with the genesis main transition and the Gate-B bounds in force; the named
  instances are `relSuccessor_resharding_vmono` (`.curveHosts ⊑ .resharding`) and the resharding
  premises of the two `allFeatures` compositions.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## Verdict-level simulation -/

/-- Verdict-level simulation with a relation on results: where `x` succeeds, `y` succeeds with a
related value; where `x` rejects (an error that is not an exclusion), `y` rejects (any reason). -/
def VR {α β : Type} (R : α → β → Prop) (x : Except String α) (y : Except String β) : Prop :=
  (∀ a, x = .ok a → ∃ b, y = .ok b ∧ R a b) ∧
    (∀ e, x = .error e → isExclusion e = false → ∃ e', y = .error e' ∧ isExclusion e' = false)

theorem throw_bind' {ε α β : Type} (e : ε) (f : α → Except ε β) :
    ((throw e : Except ε α) >>= f) = throw e := rfl

theorem pure_bind' {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((pure a : Except ε α) >>= f) = f a := rfl

theorem ok_bind' {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl

theorem error_bind' {ε α β : Type} (e : ε) (f : α → Except ε β) :
    ((Except.error e : Except ε α) >>= f) = .error e := rfl

theorem check_true_bind {β : Type} (m : String) (k : Unit → Except String β) :
    (check true m >>= k) = k () := rfl

theorem check_false_bind {β : Type} (m : String) (k : Unit → Except String β) :
    (check false m >>= k) = .error m := rfl

theorem check_ok {b : Bool} {m : String} {u : Unit} (h : check b m = .ok u) : b = true := by
  cases b
  · cases h
  · rfl

namespace VR

variable {α β γ δ : Type} {R : α → β → Prop}

theorem bind_same {S : γ → δ → Prop} {p : Except String α} {f : α → Except String γ}
    {g : α → Except String δ} (h : ∀ a, p = .ok a → VR S (f a) (g a)) : VR S (p >>= f) (p >>= g) := by
  cases hp : p with
  | error e =>
    exact ⟨fun _ hx => (by cases hx), fun e' hx hne => ⟨e', by rw [error_bind'] at hx ⊢; injection hx with hx; rw [hx], hne⟩⟩
  | ok a => exact h a hp

theorem of_x_err {x : Except String α} {y : Except String β} {e : String} (hx : x = .error e)
    (hy : isExclusion e = false → ∃ e', y = .error e' ∧ isExclusion e' = false) : VR R x y := by
  subst hx
  exact ⟨fun _ h => (by cases h), fun e' h hne => by cases h; exact hy hne⟩

theorem of_x_ood {x : Except String α} {y : Except String β} {e : String} (hx : x = .error e)
    (he : isExclusion e = true) : VR R x y :=
  of_x_err hx (fun h => by rw [he] at h; cases h)

theorem err_err {x : Except String α} {y : Except String β} {e e' : String} (hx : x = .error e)
    (hy : y = .error e') (he' : isExclusion e' = false) : VR R x y :=
  of_x_err hx (fun _ => ⟨e', hy, he'⟩)

/-- An exclusion check only on the left: when it fails the left side excludes. -/
theorem xood {b : Bool} {m : String} (hm : isExclusion m = true) {k : Unit → Except String α}
    {y : Except String β} (h : b = true → VR R (k ()) y) : VR R (check b m >>= k) y := by
  cases b
  · exact of_x_ood rfl hm
  · exact h rfl

theorem ok_ok {a : α} {b : β} (h : R a b) : VR R (.ok a) (.ok b) :=
  ⟨fun a' ha => by cases ha; exact ⟨b, rfl, h⟩, fun _ hx => by cases hx⟩

theorem toV {x y : Except String Unit} (h : VR (fun _ _ => True) x y) : VRefines x y :=
  ⟨fun hx => by
    obtain ⟨b, hb, _⟩ := h.1 () hx
    cases b; exact hb, h.2⟩

theorem map {x : Except String α} {y : Except String β} (f : α → Unit) (g : β → Unit) (h : VR R x y) :
    VR (fun _ _ => True) (x.map f) (y.map g) := by
  refine ⟨fun a ha => ?_, fun e he hne => ?_⟩
  · cases hx : x with
    | error e => rw [hx] at ha; cases ha
    | ok a' =>
      obtain ⟨b, hb, _⟩ := h.1 a' hx
      exact ⟨g b, by rw [hb]; rfl, trivial⟩
  · cases hx : x with
    | ok a' => rw [hx] at he; cases he
    | error e₀ =>
      have he₀ : e₀ = e := by rw [hx] at he; injection he
      subst he₀
      obtain ⟨e', hy, hne'⟩ := h.2 _ hx hne
      exact ⟨e', by rw [hy]; rfl, hne'⟩

end VR

/-! ## The walk over one layout, abstractly

The loop of `walkSegment` with every block in one layout and no genesis block is a two-phase scan:
before the first new chunk (`st0`), after it (`st1`), and stopping at the second (`stD`). A block
whose slot count is wrong (`good = false`) is rejected. -/

section Scan

variable {σ : Type} (f : Nat → σ → Except String (ForInStep σ)) (N : Nat) (good new : Nat → Bool)
  (st0 : Nat → σ) (st1 : Nat → Nat → σ) (stD : Nat → Nat → σ) (stopOf : σ → Option Nat)

/-- The next new chunk is at `t`, scanning from position `k`. -/
def Found1 (k t : Nat) : Prop :=
  k ≤ t ∧ t < N ∧ new t = true ∧ (∀ j, k ≤ j → j < t → new j = false) ∧
    (∀ j, k ≤ j → j ≤ t → good j = true)

theorem forIn_except_cons {α : Type} (a : α) (as : List α) (s : σ)
    (g : α → σ → Except String (ForInStep σ)) :
    forIn (a :: as) s g = (g a s >>= fun r => match r with
      | .done b => pure b
      | .yield b => forIn as b g) := List.forIn_cons _ _ _ _

theorem scan_phase1
    (hbad : ∀ i st, i < N → good i = false → ∃ e, f i st = .error e ∧ isExclusion e = false)
    (h1 : ∀ b i, b < i → i < N → good i = true →
      f i (st1 b i) = .ok (if new i then .done (stD b i) else .yield (st1 b (i + 1))))
    (hs1 : ∀ b k, stopOf (st1 b k) = none) :
    ∀ m k b, b < k → k + m = N →
      (∀ e, forIn (List.range' k m) (st1 b k) f = .error e → isExclusion e = false) ∧
      (∀ st, forIn (List.range' k m) (st1 b k) f = .ok st →
        stopOf st = none ∨ ∃ t, Found1 N good new k t ∧ st = stD b t) ∧
      (∀ t, Found1 N good new k t → forIn (List.range' k m) (st1 b k) f = .ok (stD b t)) := by
  intro m
  induction m with
  | zero =>
    intro k b _ hkN
    refine ⟨fun e h => (by cases h), fun st h => ?_, fun t ht => ?_⟩
    · cases h; exact Or.inl (hs1 b k)
    · obtain ⟨h1', h2', _⟩ := ht; omega
  | succ m ih =>
    intro k b hbk hkN
    have hk : k < N := by omega
    rw [List.range'_succ, forIn_except_cons]
    cases hg : good k with
    | false =>
      obtain ⟨e, he, hne⟩ := hbad k (st1 b k) hk hg
      rw [he, error_bind']
      refine ⟨fun e' h => by cases h; exact hne, fun st h => (by cases h), fun t ht => ?_⟩
      have := ht.2.2.2.2 k (Nat.le_refl _) ht.1
      rw [hg] at this; cases this
    | true =>
      rw [h1 b k hbk hk hg]
      cases hn : new k with
      | true =>
        simp only [ite_true, ok_bind']
        refine ⟨fun e h => (by cases h), fun st h => ?_, fun t ht => ?_⟩
        · cases h
          refine Or.inr ⟨k, ⟨Nat.le_refl _, hk, hn, fun j h₁ h₂ => by omega, fun j h₁ h₂ => ?_⟩, rfl⟩
          have : j = k := by omega
          subst this; exact hg
        · have htk : t = k := by
            rcases Nat.lt_or_ge k t with h | h
            · have := ht.2.2.2.1 k (Nat.le_refl _) h; rw [hn] at this; cases this
            · have := ht.1; omega
          subst htk; rfl
      | false =>
        simp only [Bool.false_eq_true, ite_false, ok_bind']
        obtain ⟨ihe, iho, ihc⟩ := ih (k + 1) b (by omega) (by omega)
        refine ⟨ihe, fun st h => ?_, fun t ht => ?_⟩
        · rcases iho st h with h' | ⟨t, ⟨ht1, ht2, ht3, ht4, ht5⟩, rfl⟩
          · exact Or.inl h'
          · refine Or.inr ⟨t, ⟨by omega, ht2, ht3, fun j h₁ h₂ => ?_, fun j h₁ h₂ => ?_⟩, rfl⟩
            · rcases Nat.lt_or_ge j (k + 1) with h | h
              · have : j = k := by omega
                subst this; exact hn
              · exact ht4 j h h₂
            · rcases Nat.lt_or_ge j (k + 1) with h | h
              · have : j = k := by omega
                subst this; exact hg
              · exact ht5 j h h₂
        · obtain ⟨ht1, ht2, ht3, ht4, ht5⟩ := ht
          have htk : k + 1 ≤ t := by
            rcases Nat.lt_or_ge k t with h | h
            · omega
            · have : t = k := by omega
              subst this; rw [hn] at ht3; cases ht3
          exact ihc t ⟨htk, ht2, ht3, fun j h₁ h₂ => ht4 j (by omega) h₂,
            fun j h₁ h₂ => ht5 j (by omega) h₂⟩

/-- The first new chunk at `b` and the second at `t`, scanning from position `k`. -/
def Found0 (k b t : Nat) : Prop :=
  k ≤ b ∧ new b = true ∧ (∀ j, k ≤ j → j < b → new j = false) ∧
    (∀ j, k ≤ j → j ≤ b → good j = true) ∧ Found1 N good new (b + 1) t

theorem scan_phase0
    (hbad : ∀ i st, i < N → good i = false → ∃ e, f i st = .error e ∧ isExclusion e = false)
    (h0 : ∀ i, i < N → good i = true →
      f i (st0 i) = .ok (if new i then .yield (st1 i (i + 1)) else .yield (st0 (i + 1))))
    (h1 : ∀ b i, b < i → i < N → good i = true →
      f i (st1 b i) = .ok (if new i then .done (stD b i) else .yield (st1 b (i + 1))))
    (hs0 : ∀ k, stopOf (st0 k) = none) (hs1 : ∀ b k, stopOf (st1 b k) = none) :
    ∀ m k, k + m = N →
      (∀ e, forIn (List.range' k m) (st0 k) f = .error e → isExclusion e = false) ∧
      (∀ st, forIn (List.range' k m) (st0 k) f = .ok st →
        stopOf st = none ∨ ∃ b t, Found0 N good new k b t ∧ st = stD b t) ∧
      (∀ b t, Found0 N good new k b t → forIn (List.range' k m) (st0 k) f = .ok (stD b t)) := by
  intro m
  induction m with
  | zero =>
    intro k hkN
    refine ⟨fun e h => (by cases h), fun st h => ?_, fun b t ht => ?_⟩
    · cases h; exact Or.inl (hs0 k)
    · obtain ⟨h1', _, _, _, h5', h6', _⟩ := ht; omega
  | succ m ih =>
    intro k hkN
    have hk : k < N := by omega
    rw [List.range'_succ, forIn_except_cons]
    cases hg : good k with
    | false =>
      obtain ⟨e, he, hne⟩ := hbad k (st0 k) hk hg
      rw [he, error_bind']
      refine ⟨fun e' h => by cases h; exact hne, fun st h => (by cases h), fun b t ht => ?_⟩
      have := ht.2.2.2.1 k (Nat.le_refl _) ht.1
      rw [hg] at this; cases this
    | true =>
      rw [h0 k hk hg]
      cases hn : new k with
      | true =>
        simp only [ite_true, ok_bind']
        obtain ⟨p1e, p1o, p1c⟩ := scan_phase1 f N good new st1 stD stopOf hbad h1 hs1 m (k + 1) k
          (by omega) (by omega)
        refine ⟨p1e, fun st h => ?_, fun b t ht => ?_⟩
        · rcases p1o st h with h' | ⟨t, ht, rfl⟩
          · exact Or.inl h'
          · refine Or.inr ⟨k, t, ⟨Nat.le_refl _, hn, fun j h₁ h₂ => by omega, fun j h₁ h₂ => ?_, ht⟩, rfl⟩
            have : j = k := by omega
            subst this; exact hg
        · obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := ht
          have hbk : b = k := by
            rcases Nat.lt_or_ge k b with h | h
            · have := hb3 k (Nat.le_refl _) h; rw [hn] at this; cases this
            · omega
          subst hbk
          exact p1c t hb5
      | false =>
        simp only [Bool.false_eq_true, ite_false, ok_bind']
        obtain ⟨ihe, iho, ihc⟩ := ih (k + 1) (by omega)
        refine ⟨ihe, fun st h => ?_, fun b t ht => ?_⟩
        · rcases iho st h with h' | ⟨b, t, ⟨hb1, hb2, hb3, hb4, hb5⟩, rfl⟩
          · exact Or.inl h'
          · refine Or.inr ⟨b, t, ⟨by omega, hb2, fun j h₁ h₂ => ?_, fun j h₁ h₂ => ?_, hb5⟩, rfl⟩
            · rcases Nat.lt_or_ge j (k + 1) with h | h
              · have : j = k := by omega
                subst this; exact hn
              · exact hb3 j h h₂
            · rcases Nat.lt_or_ge j (k + 1) with h | h
              · have : j = k := by omega
                subst this; exact hg
              · exact hb4 j h h₂
        · obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := ht
          have hbk : k + 1 ≤ b := by
            rcases Nat.lt_or_ge k b with h | h
            · omega
            · have : b = k := by omega
              subst this; rw [hn] at hb2; cases hb2
          exact ihc b t ⟨hbk, hb2, fun j h₁ h₂ => hb3 j (by omega) h₂,
            fun j h₁ h₂ => hb4 j (by omega) h₂, hb5⟩

theorem scan_post {τ : Type}
    (hbad : ∀ i st, i < N → good i = false → ∃ e, f i st = .error e ∧ isExclusion e = false)
    (h0 : ∀ i, i < N → good i = true →
      f i (st0 i) = .ok (if new i then .yield (st1 i (i + 1)) else .yield (st0 (i + 1))))
    (h1 : ∀ b i, b < i → i < N → good i = true →
      f i (st1 b i) = .ok (if new i then .done (stD b i) else .yield (st1 b (i + 1))))
    (hs0 : ∀ k, stopOf (st0 k) = none) (hs1 : ∀ b k, stopOf (st1 b k) = none)
    (POST : σ → Except String τ) (W : Nat → Nat → τ)
    (hpn : ∀ st, stopOf st = none → ∃ e, POST st = .error e ∧ isExclusion e = false)
    (hpD : ∀ b t, Found0 N good new 0 b t → POST (stD b t) = .ok (W b t)) :
    (∀ e, (forIn (List.range' 0 N) (st0 0) f >>= POST) = .error e → isExclusion e = false) ∧
    (∀ r, (forIn (List.range' 0 N) (st0 0) f >>= POST) = .ok r →
      ∃ b t, Found0 N good new 0 b t ∧ r = W b t) ∧
    (∀ b t, Found0 N good new 0 b t → (forIn (List.range' 0 N) (st0 0) f >>= POST) = .ok (W b t)) := by
  obtain ⟨pe, po, pc⟩ := scan_phase0 f N good new st0 st1 stD stopOf hbad h0 h1 hs0 hs1 N 0 (by omega)
  refine ⟨fun e h => ?_, fun r h => ?_, fun b t hf => ?_⟩
  · cases hl : forIn (List.range' 0 N) (st0 0) f with
    | error e' =>
      rw [hl, error_bind'] at h; cases h; exact pe _ hl
    | ok st =>
      rw [hl, ok_bind'] at h
      rcases po st hl with hn | ⟨b, t, hf, rfl⟩
      · obtain ⟨e', he', hne'⟩ := hpn st hn
        rw [he'] at h; cases h; exact hne'
      · rw [hpD b t hf] at h; cases h
  · cases hl : forIn (List.range' 0 N) (st0 0) f with
    | error e' => rw [hl, error_bind'] at h; cases h
    | ok st =>
      rw [hl, ok_bind'] at h
      rcases po st hl with hn | ⟨b, t, hf, rfl⟩
      · obtain ⟨e', he', hne'⟩ := hpn st hn
        rw [he'] at h; cases h
      · rw [hpD b t hf] at h; cases h; exact ⟨b, t, hf, rfl⟩
  · rw [pc b t hf, ok_bind', hpD b t hf]

end Scan

/-! ## The concrete walk on one layout -/

section Walk

variable (c : Claim) (blks : List Blk) (s idx : Nat) (lb : Bytes) (L : Layout)

/-- A new chunk of the shard at slot `idx` in block `b`. -/
def newIn (b : Blk) : Bool :=
  match b.slots[idx]? with
  | some p => p.1.heightIncluded == b.hdr.height
  | none => false

def newAt (j : Nat) : Bool :=
  match blks[j]? with
  | some b => newIn idx b
  | none => false

def goodAt (j : Nat) : Bool :=
  match blks[j]? with
  | some b => b.slots.length == L.numShards
  | none => true

abbrev WSt := Nat × Nat × List WalkTransition × List (Nat × Nat) × Option (Nat × Nat × Bytes) × Option Nat

def wst0 (k : Nat) : WSt :=
  (s, 0, (List.range k).map (fun i => WalkTransition.old i s), [],
    (if k = 0 then none else some (k - 1, s, lb)), none)

def wst1 (b k : Nat) : WSt :=
  (s, 1, (List.range b).map (fun i => WalkTransition.old i s), (List.range' b (k - b)).map (fun j => (j, s)),
    some (b, s, lb), none)

def wstD (b t : Nat) : WSt :=
  (s, 1, (List.range b).map (fun i => WalkTransition.old i s), (List.range' b (t - b)).map (fun j => (j, s)),
    some (b, s, lb), some t)

/-- The walk the one-layout segment yields. -/
def expectedWalk (b t : Nat) : Walk :=
  { b2i := b, mainShard := s, mainLayout := lb, sources := (List.range' b (t - b)).map (fun j => (j, s)),
    transitions := (List.range b).reverse.map (fun i => WalkTransition.old i s), stop := t }

theorem walk_prep
    (hlb : ∀ e ∈ c.epochId :: blks.map (·.hdr.epochId), layoutBytesOf c e = .ok lb)
    (hng : blks.any (·.isGenesis) = false) (i : Nat) (hi : i < blks.length) :
    ∃ b, blks[i]? = some b ∧ ∃ e, (c.epochId :: blks.map (·.hdr.epochId))[i]? = some e ∧
      layoutBytesOf c e = .ok lb ∧ layoutBytesOf c b.hdr.epochId = .ok lb ∧ b.isGenesis = false := by
  have hbi : blks[i]? = some blks[i] := List.getElem?_eq_getElem hi
  have hmem : blks[i] ∈ blks := List.getElem_mem hi
  have hi' : i < (c.epochId :: blks.map (·.hdr.epochId)).length := by simp; omega
  refine ⟨blks[i], hbi, _, List.getElem?_eq_getElem hi', hlb _ (List.getElem_mem hi'), hlb _ ?_, ?_⟩
  · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hmem)
  · rw [List.any_eq_false] at hng
    simpa using hng _ hmem

theorem walk_one_layout
    (hlb : ∀ e ∈ c.epochId :: blks.map (·.hdr.epochId), layoutBytesOf c e = .ok lb)
    (hL : decodeLayout lb = .ok L) (hidx : L.index s = some idx)
    (hng : blks.any (·.isGenesis) = false) :
    (∀ e, walkSegment c blks (c.epochId :: blks.map (·.hdr.epochId)) s = .error e →
      isExclusion e = false) ∧
    (∀ wk, walkSegment c blks (c.epochId :: blks.map (·.hdr.epochId)) s = .ok wk →
      ∃ b t, Found0 blks.length (goodAt blks L) (newAt blks idx) 0 b t ∧ wk = expectedWalk s lb b t) ∧
    (∀ b t, Found0 blks.length (goodAt blks L) (newAt blks idx) 0 b t →
      walkSegment c blks (c.epochId :: blks.map (·.hdr.epochId)) s = .ok (expectedWalk s lb b t)) := by
  unfold walkSegment
  rw [List.range_eq_range']
  refine scan_post _ blks.length (goodAt blks L) (newAt blks idx) (wst0 s lb) (wst1 s lb) (wstD s lb)
    (fun st => st.2.2.2.2.2) ?hbad ?h0 ?h1 (fun _ => rfl) (fun _ _ => rfl) _ (expectedWalk s lb) ?hpn ?hpD
  case hbad =>
    intro i st hi hg
    obtain ⟨b, hbi, e, he, hlbA, hlbO, _⟩ := walk_prep c blks lb hlb hng i hi
    simp only [goodAt, hbi] at hg
    simp only [hbi, he, hlbA, hlbO, hL, pure_bind', ok_bind', hg, check_false_bind]
    exact ⟨_, rfl, by decide⟩
  case h0 =>
    intro i hi hg
    obtain ⟨b, hbi, e, he, hlbA, hlbO, hgen⟩ := walk_prep c blks lb hlb hng i hi
    simp only [goodAt, hbi] at hg
    simp only [hbi, he, hlbA, hlbO, hL, pure_bind', ok_bind', hg, check_true_bind, bne_self_eq_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte, wst0, newAt, newIn, hidx, hgen]
    rcases hsl : b.slots[idx]? with _ | ⟨p1, p2⟩
    · simp [List.range_succ]; rfl
    · cases hn : (p1.heightIncluded == b.hdr.height) <;> simp [hn, wst1, List.range_succ] <;> rfl
  case h1 =>
    intro b2 i hbi2 hi hg
    obtain ⟨b, hbi, e, he, hlbA, hlbO, hgen⟩ := walk_prep c blks lb hlb hng i hi
    simp only [goodAt, hbi] at hg
    simp only [hbi, he, hlbA, hlbO, hL, pure_bind', ok_bind', hg, check_true_bind, bne_self_eq_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte, wst1, newAt, newIn, hidx, hgen]
    have hr : (List.range' b2 (i + 1 - b2)).map (fun j => (j, s)) =
        (List.range' b2 (i - b2)).map (fun j => (j, s)) ++ [(i, s)] := by
      have : i + 1 - b2 = (i - b2) + 1 := by omega
      rw [this, List.range'_concat, List.map_append, show b2 + 1 * (i - b2) = i by omega]
      rfl
    rcases hsl : b.slots[idx]? with _ | ⟨p1, p2⟩
    · simp [hr]; rfl
    · cases hn : (p1.heightIncluded == b.hdr.height) <;> simp [hn, wstD, hr] <;> rfl
  case hpn =>
    intro st hst
    obtain ⟨sh, seen, pushed, src, main, stop⟩ := st
    simp only at hst
    subst hst
    rcases main with _ | ⟨a, b', c'⟩
    · exact ⟨_, rfl, by decide⟩
    · cases hs : src.isEmpty
      · exact ⟨_, by simp only [hs, Bool.false_eq_true, ↓reduceIte]; rfl, by decide⟩
      · exact ⟨_, by simp only [hs, ↓reduceIte]; rfl, by decide⟩
  case hpD =>
    intro b t hf
    obtain ⟨_, _, _, _, ht1, _⟩ := hf
    have hne : ((List.range' b (t - b)).map (fun j => (j, s))).isEmpty = false := by
      obtain ⟨n, hn⟩ : ∃ n, t - b = n + 1 := ⟨t - b - 1, by omega⟩
      rw [hn, List.range'_succ]; rfl
    simp only [wstD, hne, Bool.false_eq_true, ↓reduceIte, expectedWalk, List.map_reverse]
    rfl

theorem newAt_eq (j : Nat) (hj : j < blks.length) : newAt blks idx j = newIn idx blks[j] := by
  simp only [newAt, List.getElem?_eq_getElem hj]

theorem goodAt_eq (j : Nat) (hj : j < blks.length) :
    goodAt blks L j = (blks[j].slots.length == L.numShards) := by
  simp only [goodAt, List.getElem?_eq_getElem hj]

/-- The non-resharding checker's scan (`findIdx?` twice, every slot count) from a walk result. -/
theorem d2_of_found (P : Blk → Bool) (hP : ∀ B, P B = newIn idx B) (b t : Nat)
    (hf : Found0 blks.length (goodAt blks L) (newAt blks idx) 0 b t) (ht : t + 1 = blks.length) :
    blks.all (fun B => B.slots.length == L.numShards) = true ∧ blks.findIdx? P = some b ∧
      (blks.drop (b + 1)).findIdx? P = some (t - b - 1) := by
  obtain ⟨_, hb2, hb3, hb4, ht1, ht2, ht3, ht4, ht5⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro B hB
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hB
    rw [← goodAt_eq blks L j hj]
    rcases Nat.lt_or_ge b j with h | h
    · exact ht5 j (by omega) (by omega)
    · exact hb4 j (by omega) h
  · rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨by omega, ?_, fun j hj => ?_⟩
    · rw [hP, ← newAt_eq blks idx b (by omega)]; exact hb2
    · rw [hP, ← newAt_eq blks idx j (by omega), hb3 j (Nat.zero_le _) hj]; simp
  · rw [List.findIdx?_eq_some_iff_getElem]
    refine ⟨by simp; omega, ?_, fun j hj => ?_⟩
    · rw [List.getElem_drop, hP, ← newAt_eq blks idx _ (by omega), show b + 1 + (t - b - 1) = t by omega]
      exact ht3
    · rw [List.getElem_drop, hP, ← newAt_eq blks idx _ (by omega), ht4 _ (by omega) (by omega)]; simp

/-- The walk's scan from the non-resharding checker's. -/
theorem found_of_d2 (P : Blk → Bool) (hP : ∀ B, P B = newIn idx B) (b j : Nat)
    (hall : blks.all (fun B => B.slots.length == L.numShards) = true) (hb : blks.findIdx? P = some b)
    (hj : (blks.drop (b + 1)).findIdx? P = some j) :
    Found0 blks.length (goodAt blks L) (newAt blks idx) 0 b (b + 1 + j) := by
  rw [List.findIdx?_eq_some_iff_getElem] at hb hj
  obtain ⟨hbl, hb1, hb2⟩ := hb
  obtain ⟨hjl, hj1, hj2⟩ := hj
  simp only [List.length_drop] at hjl
  rw [List.all_eq_true] at hall
  have hgood : ∀ k, k < blks.length → goodAt blks L k = true := fun k hk => by
    rw [goodAt_eq blks L k hk]; exact hall _ (List.getElem_mem hk)
  refine ⟨Nat.zero_le _, ?_, fun k _ hk => ?_, fun k _ hk => hgood k (by omega), by omega, by omega, ?_,
    fun k h₁ h₂ => ?_, fun k _ h₂ => hgood k (by omega)⟩
  · rw [newAt_eq blks idx b hbl, ← hP]; exact hb1
  · rw [newAt_eq blks idx k (by omega), ← hP]
    have := hb2 k hk
    simpa using this
  · rw [newAt_eq blks idx _ (by omega), ← hP]
    rw [List.getElem_drop] at hj1
    exact hj1
  · obtain ⟨m, rfl⟩ : ∃ m, k = b + 1 + m := ⟨k - (b + 1), by omega⟩
    rw [newAt_eq blks idx _ (by omega), ← hP]
    have := hj2 m (by omega)
    rw [List.getElem_drop] at this
    simpa using this

/-! ## The epoch table -/

theorem mem_insertSorted (x : Bytes × Option Bytes) (p : Bytes × Option Bytes) :
    ∀ l : List (Bytes × Option Bytes), x ∈ insertSorted p l ↔ x = p ∨ x ∈ l := by
  intro l
  induction l with
  | nil => simp [insertSorted]
  | cons q qs ih =>
    unfold insertSorted
    split
    · simp
    · simp only [List.mem_cons, ih]
      constructor
      · rintro (h | h | h) <;> simp [h]
      · rintro (h | h | h) <;> simp [h]

theorem mem_foldl_insertSorted (x : Bytes × Option Bytes) :
    ∀ (l acc : List (Bytes × Option Bytes)),
      x ∈ l.foldl (fun acc p => insertSorted p acc) acc ↔ x ∈ acc ∨ x ∈ l := by
  intro l
  induction l with
  | nil => simp
  | cons p ps ih =>
    intro acc
    simp only [List.foldl_cons, ih, mem_insertSorted, List.mem_cons]
    constructor
    · rintro ((h | h) | h) <;> simp [h]
    · rintro (h | h | h) <;> simp [h]

def dedupStep : Bytes × Option Bytes → List Bytes → List Bytes := fun (k, _) acc =>
  match acc with
  | k' :: _ => if k == k' then acc else k :: acc
  | [] => [k]

theorem dedupSorted_eq (l : List Bytes) :
    dedupSorted l = (sortKV (l.map fun k => (k, none))).foldr dedupStep [] := rfl

theorem dedupStep_sub (kv : Bytes × Option Bytes) (acc : List Bytes) (y : Bytes) (hy : y ∈ acc) :
    y ∈ dedupStep kv acc := by
  obtain ⟨k, v⟩ := kv
  cases acc with
  | nil => cases hy
  | cons k' tl =>
    simp only [dedupStep]
    split
    · exact hy
    · exact List.mem_cons_of_mem _ hy

theorem dedupStep_self (k : Bytes) (v : Option Bytes) (acc : List Bytes) : k ∈ dedupStep (k, v) acc := by
  cases acc with
  | nil => simp [dedupStep]
  | cons k' tl =>
    simp only [dedupStep]
    split
    · rename_i hk
      have : k = k' := by simpa using hk
      subst this; exact List.mem_cons_self
    · exact List.mem_cons_self

theorem mem_dedup_foldr (k : Bytes) :
    ∀ (L : List (Bytes × Option Bytes)) (v : Option Bytes), (k, v) ∈ L → k ∈ L.foldr dedupStep [] := by
  intro L
  induction L with
  | nil => intro v h; cases h
  | cons kv rest ih =>
    intro v h
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with h | h
    · subst h; exact dedupStep_self _ _ _
    · exact dedupStep_sub _ _ _ (ih v h)

theorem mem_dedupSorted (x : Bytes) (l : List Bytes) (h : x ∈ l) : x ∈ dedupSorted l := by
  rw [dedupSorted_eq]
  apply mem_dedup_foldr x _ none
  unfold sortKV
  rw [mem_foldl_insertSorted]
  right
  exact List.mem_map_of_mem h

theorem layoutBytes_of_table (c : Claim) (ae : List Bytes) (ep : EpochRec)
    (htab : (c.epochs.map (·.epochId) == dedupSorted ae) = true)
    (hsl : c.epochs.all (·.shardLayout == ep.shardLayout) = true) :
    ∀ e ∈ ae, layoutBytesOf c e = .ok ep.shardLayout := by
  intro e he
  have htab' : c.epochs.map (·.epochId) = dedupSorted ae := by simpa using htab
  have hm : e ∈ c.epochs.map (·.epochId) := by rw [htab']; exact mem_dedupSorted e ae he
  obtain ⟨r, hr, hre⟩ := List.mem_map.mp hm
  unfold layoutBytesOf
  cases hf : c.epochs.find? (·.epochId == e) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp [hre]) (hf r hr)
  | some r' =>
    have hr' := List.mem_of_find?_eq_some hf
    rw [List.all_eq_true] at hsl
    have := hsl r' hr'
    simp only [beq_iff_eq] at this
    simp only [this]; rfl

/-! ## Loops -/

/-- Two lists related pointwise. -/
def Rel2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Rel2 R as bs
  | _, _ => False

theorem forIn_forall2 {α β σ : Type} (R : α → β → Prop) (f : α → σ → Except String (ForInStep σ))
    (g : β → σ → Except String (ForInStep σ)) (hfg : ∀ a b st, R a b → f a st = g b st) :
    ∀ (xs : List α) (ys : List β), Rel2 R xs ys → ∀ st, forIn xs st f = forIn ys st g := by
  intro xs
  induction xs with
  | nil =>
    intro ys h st
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons a as ih =>
    intro ys h st
    cases ys with
    | nil => cases h
    | cons b bs =>
      obtain ⟨hab, hr⟩ := h
      rw [forIn_except_cons, forIn_except_cons, hfg _ _ _ hab]
      cases g _ st with
      | error e => rfl
      | ok r =>
        cases r with
        | done b => rfl
        | yield b => exact ih bs hr b

theorem forall2_sources (blks : List Blk) (s : Nat) :
    ∀ m k, k + m ≤ blks.length →
      Rel2 (fun (p : Nat × Nat) S => blks[p.1]? = some S ∧ p.2 = s)
        ((List.range' k m).map (fun j => (j, s))) (List.take m (List.drop k blks)) := by
  intro m
  induction m with
  | zero => intro k _; simp [Rel2]
  | succ m ih =>
    intro k hk
    rw [List.range'_succ, List.drop_eq_getElem_cons (by omega), List.map_cons, List.take_succ_cons]
    exact ⟨⟨List.getElem?_eq_getElem (by omega), rfl⟩, ih (k + 1) (by omega)⟩

/-- `ForInStep.map`. -/
def fsMap {α β : Type} (g : α → β) : ForInStep α → ForInStep β
  | .yield r => .yield (g r)
  | .done r => .done (g r)

theorem map_bind_check {α σ : Type} (q : Except String α) (c : α → Bool) (m : String) (g : α → σ) :
    (q >>= fun r => check (c r) m >>= fun _ => pure (ForInStep.yield (g r))) =
      (q >>= fun r => check (c r) m >>= fun _ => pure (ForInStep.yield r)).map (fsMap g) := by
  cases q with
  | error e => rfl
  | ok r =>
    simp only [ok_bind']
    cases hc : c r
    · simp only [check_false_bind]; rfl
    · simp only [check_true_bind]; rfl

theorem bind_check_yield_ne_done {α : Type} (q : Except String α) (c : α → Bool) (m : String) (b : α) :
    (q >>= fun r => check (c r) m >>= fun _ => pure (ForInStep.yield r)) ≠ .ok (.done b) := by
  cases q with
  | error e => intro h; cases h
  | ok r =>
    simp only [ok_bind']
    cases hc : c r
    · simp only [check_false_bind]; intro h; cases h
    · simp only [check_true_bind]; intro h; cases h

/-- The implicit-transition loops: the resharding loop carries the congestion and the remaining
facts, and otherwise runs the non-resharding loop's body. -/
theorem forIn_implicit {T F C : Type} (s : Nat)
    (FX : (Nat × F) × T → Bytes → Except String (ForInStep Bytes))
    (FY : WalkTransition × T → Bytes × C × List F → Except String (ForInStep (Bytes × C × List F)))
    (cong : C) (hnd : ∀ a r b, FX a r ≠ .ok (.done b))
    (hb : ∀ i f fs T root, FY (.old i s, T) (root, cong, f :: fs) =
      (FX ((i, f), T) root).map (fsMap fun r => (r, cong, fs))) :
    ∀ (is : List Nat) (fs : List F) (Ts : List T) (root : Bytes), is.length = fs.length →
      is.length = Ts.length →
      forIn ((is.map (fun i => WalkTransition.old i s)).zip Ts) (root, cong, fs) FY =
        (forIn ((is.zip fs).zip Ts) root FX).map (fun r => (r, cong, [])) := by
  intro is
  induction is with
  | nil =>
    intro fs Ts root h1 _
    cases fs with
    | nil => rfl
    | cons _ _ => cases h1
  | cons i is ih =>
    intro fs Ts root h1 h2
    cases fs with
    | nil => cases h1
    | cons f fs =>
      cases Ts with
      | nil => cases h2
      | cons T Ts =>
        simp only [List.map_cons, List.zip_cons_cons]
        rw [forIn_except_cons, forIn_except_cons, hb]
        cases hfx : FX ((i, f), T) root with
        | error e => rfl
        | ok r =>
          cases r with
          | done b => exact absurd ‹_› (hnd _ _ b)
          | yield b =>
            simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
            exact ih fs Ts b h1 h2

theorem VR.bind_eq {α β γ δ : Type} {S : γ → δ → Prop} {p : Except String α} {p' : Except String β}
    (h : α → β) (hp : p' = p.map h) {f : α → Except String γ} {g : β → Except String δ}
    (hk : ∀ a, p = .ok a → VR S (f a) (g (h a))) : VR S (p >>= f) (p' >>= g) := by
  subst hp
  cases hq : p with
  | error e =>
    refine ⟨fun _ hx => (by cases hx), fun e' hx hne => ⟨e', ?_, hne⟩⟩
    rw [error_bind'] at hx; injection hx with hx; subst hx; rfl
  | ok a => exact hk a hq

theorem VR.bind_eq' {α γ δ : Type} {S : γ → δ → Prop} {p p' : Except String α}
    (hp : p' = p) {f : α → Except String γ} {g : α → Except String δ}
    (hk : ∀ a, p = .ok a → VR S (f a) (g a)) : VR S (p >>= f) (p' >>= g) := by
  subst hp; exact VR.bind_same hk

theorem VR.y_rw {α β : Type} {R : α → β → Prop} {x : Except String α} {y y' : Except String β}
    (h : y = y') (hv : VR R x y') : VR R x y := by subst h; exact hv

theorem VR.y_ok {α β γ : Type} {R : α → β → Prop} {x : Except String α} {q : Except String γ}
    {b : γ} {k : γ → Except String β} (h : q = .ok b) (hv : VR R x (k b)) : VR R x (q >>= k) := by
  rw [h]; exact hv

/-- The resharding checker's walk fails (with a reject) when no scan to the last block exists. -/
theorem y_walk_err {β : Type}
    (hlb : ∀ e ∈ c.epochId :: blks.map (·.hdr.epochId), layoutBytesOf c e = .ok lb)
    (hL : decodeLayout lb = .ok L) (hidx : L.index s = some idx)
    (hng : blks.any (·.isGenesis) = false) (m : String) (hm : isExclusion m = false)
    (K : Walk → Except String β)
    (hnot : ¬ ∃ b t, Found0 blks.length (goodAt blks L) (newAt blks idx) 0 b t ∧ t + 1 = blks.length) :
    ∃ e', (walkSegment c blks (c.epochId :: blks.map (·.hdr.epochId)) s >>= fun wk =>
      check (wk.stop + 1 == blks.length) m >>= fun _ => K wk) = .error e' ∧ isExclusion e' = false := by
  obtain ⟨we, wo, _⟩ := walk_one_layout c blks s idx lb L hlb hL hidx hng
  cases hw : walkSegment c blks (c.epochId :: blks.map (·.hdr.epochId)) s with
  | error e => exact ⟨e, rfl, we e hw⟩
  | ok wk =>
    obtain ⟨b, t, hf, rfl⟩ := wo wk hw
    have : (t + 1 == blks.length) = false := by
      cases h : (t + 1 == blks.length)
      · rfl
      · exact absurd ⟨b, t, hf, by simpa using h⟩ hnot
    exact ⟨m, by simp only [ok_bind', expectedWalk, this, check_false_bind], hm⟩

theorem y_walk_ok {β : Type}
    (hlb : ∀ e ∈ c.epochId :: blks.map (·.hdr.epochId), layoutBytesOf c e = .ok lb)
    (hL : decodeLayout lb = .ok L) (hidx : L.index s = some idx)
    (hng : blks.any (·.isGenesis) = false) (m : String) (K : Walk → Except String β) (b t : Nat)
    (hf : Found0 blks.length (goodAt blks L) (newAt blks idx) 0 b t) (ht : t + 1 = blks.length) :
    (walkSegment c blks (c.epochId :: blks.map (·.hdr.epochId)) s >>= fun wk =>
      check (wk.stop + 1 == blks.length) m >>= fun _ => K wk) = K (expectedWalk s lb b t) := by
  obtain ⟨_, _, wc⟩ := walk_one_layout c blks s idx lb L hlb hL hidx hng
  rw [wc b t hf, ok_bind']
  simp only [expectedWalk, ht, beq_self_eq_true, check_true_bind]

theorem nf_none1 (P : Blk → Bool) (hP : ∀ B, P B = newIn idx B) (heq : blks.findIdx? P = none) :
    ¬ ∃ b t, Found0 blks.length (goodAt blks L) (newAt blks idx) 0 b t ∧ t + 1 = blks.length := by
  rintro ⟨b, t, hf, ht⟩
  have := (d2_of_found blks idx L P hP b t hf ht).2.1
  rw [heq] at this; cases this

theorem nf_none2 (P : Blk → Bool) (hP : ∀ B, P B = newIn idx B) (b2i : Nat)
    (heq1 : blks.findIdx? P = some b2i) (heq2 : (blks.drop (b2i + 1)).findIdx? P = none) :
    ¬ ∃ b t, Found0 blks.length (goodAt blks L) (newAt blks idx) 0 b t ∧ t + 1 = blks.length := by
  rintro ⟨b, t, hf, ht⟩
  obtain ⟨_, h1, h2⟩ := d2_of_found blks idx L P hP b t hf ht
  rw [heq1] at h1; cases h1
  rw [heq2] at h2; cases h2

theorem nf_stop (P : Blk → Bool) (hP : ∀ B, P B = newIn idx B) (b2i j : Nat)
    (heq1 : blks.findIdx? P = some b2i) (heq2 : (blks.drop (b2i + 1)).findIdx? P = some j)
    (hst : (b2i + 1 + j + 1 == blks.length) = false) :
    ¬ ∃ b t, Found0 blks.length (goodAt blks L) (newAt blks idx) 0 b t ∧ t + 1 = blks.length := by
  rintro ⟨b, t, hf, ht⟩
  obtain ⟨_, h1, h2⟩ := d2_of_found blks idx L P hP b t hf ht
  rw [heq1] at h1; cases h1
  rw [heq2] at h2; cases h2
  have := hf.2.2.2.2.1
  simp only [beq_eq_false_iff_ne, ne_eq] at hst
  omega

theorem found_b (P : Blk → Bool) (hP : ∀ B, P B = newIn idx B) (b2i : Nat)
    (heq1 : blks.findIdx? P = some b2i) (b t : Nat)
    (hf : Found0 blks.length (goodAt blks L) (newAt blks idx) 0 b t) (ht : t + 1 = blks.length) :
    b = b2i := by
  have := (d2_of_found blks idx L P hP b t hf ht).2.1
  rw [heq1] at this; injection this with this; exact this.symm

theorem genesis_false_of_get (hng : blks.any (·.isGenesis) = false) (i : Nat) (B : Blk)
    (h : blks[i]? = some B) : B.isGenesis = false := by
  rw [List.any_eq_false] at hng
  simpa using hng B (List.mem_of_getElem? h)

end Walk

theorem expectedProposedSplit_none (n s : Nat) (t : PTrie) (e : Bool) :
    TrieSplit.expectedProposedSplit none n s t e = .ok none := rfl

theorem beq_none_isNone {α : Type} [BEq α] (o : Option α) : (o == none) = o.isNone := by
  cases o <;> rfl

theorem forIn_const_ok {α : Type} (l : List α) (body : α → PUnit → Except String (ForInStep PUnit))
    (h : ∀ a ∈ l, body a PUnit.unit = .ok (.yield PUnit.unit)) :
    forIn l PUnit.unit body = .ok PUnit.unit := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.forIn_cons, h a List.mem_cons_self]
    exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- **O6, the correspondence.** On a segment without a genesis block, wherever the whole-state
checker without resharding accepts or rejects, the resharding tiers' checker (`ReshardCore`)
returns the same verdict. -/
theorem checkD2CoreWithObs_vr_reshard (d : ExecutionDriver) (hr : d.resharding = false)
    (hcr : d.codeResponseCap = true) (hwu : d.witnessUnbounded = false)
    (hlu : d.layoutUnbounded = false) (hseg : d.segmentUnbounded = false)
    (hik : d.implicitKind = fun _ _ _ => .ok .applyOldChunk)
    (sa' : PTrie → Bytes → RetainMode → Except String Bytes)
    (h : ActionHooks) (cb wb : Bytes) (g : Option Nat)
    (c : Claim) (blks : List Blk) (hc : decodeClaimE cb = .ok c) (hb : c.blocks.mapM decodeBlk = .ok blks)
    (hng : blks.any (·.isGenesis) = false) :
    VR (fun _ _ => True) (checkD2CoreWithObs d h true cb wb g)
      (checkReshardCoreObs { d with resharding := true, splitApply := sa' } h true cb wb g) := by
  unfold checkD2CoreWithObs checkReshardCoreObs
  simp only [hc, hb, hr, hik, hcr, hwu, hlu, hseg, Except.mapError, ok_bind', throw_bind', pure_bind',
    Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true]
  refine VR.bind_same fun cw _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun w _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun H _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ htab => ?_
  cases hep : List.find? (fun x => x.epochId == c.epochId) c.epochs with
  | none => simp only; exact VR.err_err rfl rfl (by decide)
  | some ep =>
  simp only
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.xood (by decide) fun hsl => ?_
  refine VR.bind_same fun L hL => ?_
  refine VR.xood (by decide) fun hbound => ?_
  refine VR.y_ok (forIn_const_ok _ _ fun e he => ?_) ?_
  · have : e.shardLayout = ep.shardLayout := by
      rw [List.all_eq_true] at hsl; simpa using hsl e he
    simp only [this, hL, ok_bind', hbound, check_true_bind]; rfl
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.xood (by decide) fun hsg => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ _ => ?_
  have hlb := layoutBytes_of_table c _ ep (check_ok htab) hsl
  cases hall : blks.all (fun b => b.slots.length == L.numShards)
  · simp only [check_false_bind]
    refine VR.of_x_err rfl fun _ => ?_
    cases hli : L.index H.shardId with
    | none => exact ⟨_, rfl, by decide⟩
    | some idx =>
      simp only
      cases hh : blks.all (fun b => b.slots.all fun x => decide (x.fst.heightIncluded ≤ b.hdr.height))
      · exact ⟨_, rfl, by decide⟩
      · simp only [check_true_bind]
        exact y_walk_err c blks H.shardId idx ep.shardLayout L hlb hL hli hng _ (by decide) _
          (fun ⟨b, t, hf, ht⟩ => by
            have := (d2_of_found blks idx L (newIn idx) (fun _ => rfl) b t hf ht).1
            rw [hall] at this; cases this)
  simp only [check_true_bind]
  cases hli : L.index H.shardId with
  | none => exact VR.err_err rfl rfl (by decide)
  | some idx =>
  simp only
  refine VR.bind_same fun _ _ => ?_
  split
  rotate_left
  next heq =>
    exact VR.of_x_err rfl fun _ => y_walk_err c blks H.shardId idx ep.shardLayout L hlb hL hli hng _
      (by decide) _ (nf_none1 blks idx L _ (fun B => by (try dsimp only); unfold newIn; cases B.slots[idx]? <;> rfl) heq)
  rename_i b2i heq1
  split
  rotate_left
  next hB =>
    exfalso
    obtain ⟨hlt, _⟩ := List.findIdx?_eq_some_iff_getElem.mp heq1
    rw [List.getElem?_eq_getElem hlt] at hB; cases hB
  rename_i B2 hB
  simp only [genesis_false_of_get blks hng b2i B2 hB, Bool.not_false, check_true_bind]
  cases hgce : c.genesisChunkExtra.isNone
  · simp only [check_false_bind]
    refine VR.of_x_err rfl fun _ => ?_
    by_cases hex : ∃ b t, Found0 blks.length (goodAt blks L) (newAt blks idx) 0 b t ∧ t + 1 = blks.length
    · obtain ⟨b, t, hf, ht⟩ := hex
      obtain rfl := found_b blks idx L _ (fun B => by (try dsimp only); unfold newIn; cases B.slots[idx]? <;> rfl) b2i heq1 b t hf ht
      refine ⟨_, ?_, (by decide : isExclusion "invalid: genesis_chunk_extra for a non-genesis main block" = false)⟩
      rw [y_walk_ok c blks H.shardId idx ep.shardLayout L hlb hL hli hng _ _ b t hf ht]
      simp only [expectedWalk, hB, genesis_false_of_get blks hng b B2 hB, Bool.not_false, check_true_bind]
    · exact y_walk_err c blks H.shardId idx ep.shardLayout L hlb hL hli hng _ (by decide) _ hex
  simp only [check_true_bind]
  split
  rotate_left
  next heq2 =>
    exact VR.of_x_err rfl fun _ => y_walk_err c blks H.shardId idx ep.shardLayout L hlb hL hli hng _
      (by decide) _ (nf_none2 blks idx L _ (fun B => by (try dsimp only); unfold newIn; cases B.slots[idx]? <;> rfl) b2i heq1 heq2)
  rename_i j heq2
  cases hst : (b2i + 1 + j + 1 == blks.length)
  · simp only [check_false_bind]
    exact VR.of_x_err rfl fun _ => y_walk_err c blks H.shardId idx ep.shardLayout L hlb hL hli hng _
      (by decide) _ (nf_stop blks idx L _ (fun B => by (try dsimp only); unfold newIn; cases B.slots[idx]? <;> rfl) b2i j heq1 heq2 hst)
  simp only [check_true_bind]
  have hf := found_of_d2 blks idx L _ (fun B => by (try dsimp only); unfold newIn; cases B.slots[idx]? <;> rfl) b2i j hall heq1 heq2
  refine VR.y_rw (y_walk_ok c blks H.shardId idx ep.shardLayout L hlb hL hli hng _ _ b2i (b2i + 1 + j) hf
    (by simpa using hst)) ?_
  simp only [expectedWalk, hB, genesis_false_of_get blks hng b2i B2 hB, Bool.not_false, check_true_bind,
    hL, ok_bind', hli]
  have hN : b2i + 1 + j + 1 = blks.length := by simpa using hst
  refine VR.bind_eq' (by simp [List.filterMap_map, Function.comp_def]) fun _ hfacts => ?_
  have hfacts' : c.applyFacts.length = 1 + b2i := by simpa using check_ok hfacts
  refine VR.bind_eq' (by simp [List.filterMap_map, Function.comp_def]) fun _ _ => ?_
  cases hpb : blks[b2i + 1]? with
  | none => exact VR.err_err rfl rfl (by decide)
  | some prevB2 =>
  cases hsl2 : B2.slots[idx]? with
  | none => exact VR.err_err rfl rfl (by decide)
  | some p =>
  dsimp only
  refine VR.bind_eq' (forIn_forall2 _ _ _ ?hfg _ _ (forall2_sources blks H.shardId _ _ (by omega)) _)
    fun _ _ => ?_
  case hfg =>
    intro a S st hR
    obtain ⟨jj, t'⟩ := a
    obtain ⟨hS, ht'⟩ := hR
    simp only at hS ht'
    subst ht'
    simp only [hS]
    rfl
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ _ => ?_
  refine VR.bind_same fun _ _ => ?_
  cases hsc : Scheduler.Params.calculate Scheduler.Config.pv86 L.numShards with
  | none => exact VR.err_err rfl rfl (by decide)
  | some sched =>
  dsimp only
  simp only [pure_bind']
  have hgate : (c.applyFacts.headD ⟨none, 0, none⟩).splitGate = none := by
    cases hfa : c.applyFacts with
    | nil => rfl
    | cons f fs =>
      rw [hfa, List.all_eq_true] at hsg
      simpa using hsg f List.mem_cons_self
  refine VR.bind_same fun _ _ => ?_
  refine VR.y_ok (by rw [hgate]; exact expectedProposedSplit_none _ _ _ _) ?_
  refine VR.bind_same fun out _ => ?_
  refine VR.bind_same fun _ _ => ?_
  cases g
  rotate_left
  · dsimp only
    refine VR.bind_same fun _ _ => ?_
    refine VR.bind_same fun _ _ => ?_
    refine VR.bind_eq' (by simp) fun _ hcnt => ?_
    have hcnt' : w.implicit.length = b2i := by simpa using check_ok hcnt
    refine VR.bind_eq (fun r => (r, out.congestion, []))
      (forIn_implicit H.shardId _ _ out.congestion ?hnd ?hb _ _ _ _ (by simp; omega) (by simp; omega))
      fun r _ => ?_
    case hnd =>
      intro a r b hx
      split at hx
      · exact bind_check_yield_ne_done _ _ _ _ hx
      · cases hx
    case hb =>
      intro i f fs T root
      dsimp only
      cases hM : blks[i]? with
      | none => rfl
      | some M =>
        have hlo : layoutOf c M.hdr.epochId = .ok L := by
          unfold layoutOf
          rw [hlb _ (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_of_getElem? hM))), ok_bind', hL]
        dsimp only
        rw [hlo, ok_bind', hsc, pure_bind']
        exact map_bind_check _ _ _ _
    dsimp only
    simp only [beq_self_eq_true, ↓reduceIte, beq_none_isNone]
    iterate 11 refine VR.bind_same fun _ _ => ?_
    split
    · rename_i hem
      simp only [hem]
      exact VR.err_err rfl rfl (by decide)
    · rename_i emr len hem
      simp only [hem]
      refine VR.bind_same fun _ _ => ?_
      refine VR.bind_same fun _ _ => ?_
      exact VR.ok_ok trivial
  · dsimp only
    refine VR.bind_same fun _ _ => ?_
    refine VR.bind_eq' (by simp) fun _ hcnt => ?_
    have hcnt' : w.implicit.length = b2i := by simpa using check_ok hcnt
    refine VR.bind_eq (fun r => (r, out.congestion, []))
      (forIn_implicit H.shardId _ _ out.congestion ?hnd ?hb _ _ _ _ (by simp; omega) (by simp; omega))
      fun r _ => ?_
    case hnd =>
      intro a r b hx
      split at hx
      · exact bind_check_yield_ne_done _ _ _ _ hx
      · cases hx
    case hb =>
      intro i f fs T root
      dsimp only
      cases hM : blks[i]? with
      | none => rfl
      | some M =>
        have hlo : layoutOf c M.hdr.epochId = .ok L := by
          unfold layoutOf
          rw [hlb _ (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_of_getElem? hM))), ok_bind', hL]
        dsimp only
        rw [hlo, ok_bind', hsc, pure_bind']
        exact map_bind_check _ _ _ _
    dsimp only
    simp only [beq_self_eq_true, ↓reduceIte, beq_none_isNone]
    iterate 11 refine VR.bind_same fun _ _ => ?_
    split
    · rename_i hem
      simp only [hem]
      exact VR.err_err rfl rfl (by decide)
    · rename_i emr len hem
      simp only [hem]
      refine VR.bind_same fun _ _ => ?_
      refine VR.bind_same fun _ _ => ?_
      exact VR.ok_ok trivial

theorem checkD2CoreWith_vrefines_reshard (d : ExecutionDriver) (hr : d.resharding = false)
    (hcr : d.codeResponseCap = true) (hwu : d.witnessUnbounded = false)
    (hlu : d.layoutUnbounded = false) (hseg : d.segmentUnbounded = false)
    (hik : d.implicitKind = fun _ _ _ => .ok .applyOldChunk)
    (sa' : PTrie → Bytes → RetainMode → Except String Bytes)
    (h : ActionHooks) (cb wb : Bytes) (g : Option Nat) (hng : segmentHasGenesis cb = false) :
    VRefines (checkD2CoreWith d h true cb wb g)
      (checkReshardCore { d with resharding := true, splitApply := sa' } h true cb wb g) := by
  unfold segmentHasGenesis at hng
  cases hc : decodeClaimE cb with
  | error e => rw [hc] at hng; cases hng
  | ok c =>
    rw [hc] at hng
    cases hb : c.blocks.mapM decodeBlk with
    | error e => simp only [hb] at hng; cases hng
    | ok blks =>
      simp only [hb] at hng
      exact VR.toV (VR.map _ _ (checkD2CoreWithObs_vr_reshard d hr hcr hwu hlu hseg hik sa' h cb wb g
        c blks hc hb hng))

/-! ## The genesis-capable shell on a segment without a genesis block -/

/-- `Overlap` without the genesis alternative. -/
def OverlapNG (W : Except String Observable) (x : Except String Unit) (y : Except String Observable) :
    Prop :=
  W = y → x = W.map (fun _ => ())

namespace OverlapNG

theorem bind' {α : Type} {W : Except String Observable} {p₁ p₂ : Except String α}
    {k₁ : α → Except String Unit} {k₂ : α → Except String Observable} (hp : p₁ = p₂)
    (hk : ∀ a, OverlapNG W (k₁ a) (k₂ a)) : OverlapNG W (p₁ >>= k₁) (p₂ >>= k₂) := by
  subst hp
  intro hW
  cases hq : p₁ with
  | error e => subst hW; rw [hq]; rfl
  | ok a => rw [hq] at hW; exact hk a hW

theorem bindE {α : Type} {W : Except String Observable} {p₁ p₂ : Except String α}
    {k₁ : α → Except String Unit} {k₂ : α → Except String Observable} (hp : p₁ = p₂)
    (hk : ∀ a, p₁ = .ok a → OverlapNG W (k₁ a) (k₂ a)) : OverlapNG W (p₁ >>= k₁) (p₂ >>= k₂) := by
  subst hp
  intro hW
  cases hq : p₁ with
  | error e => subst hW; rw [hq]; rfl
  | ok a => rw [hq] at hW; exact hk a hq hW

theorem diverge {W : Except String Observable} (gen : Bool) (hg : gen = false) {GEN : Except String Unit}
    {REST : Unit → Except String Observable} (X : Except String Unit)
    (hX : X = W.map (fun _ => ())) :
    OverlapNG W (if (!gen) = true then X else GEN) (check (!gen) notGenesisError >>= REST) := by
  intro _
  subst hg
  exact hX

theorem error_both {W : Except String Observable} {x : Except String Unit}
    {y : Except String Observable} (e : String) (hx : x = .error e) (hy : y = .error e) :
    OverlapNG W x y := by
  intro hW; rw [hx, hW, hy]; rfl

theorem ite_congr {W : Except String Observable} (c : Prop) [Decidable c]
    {t₁ e₁ : Except String Unit} {t₂ e₂ : Except String Observable}
    (ht : c → OverlapNG W t₁ t₂) (he : ¬c → OverlapNG W e₁ e₂) :
    OverlapNG W (if c then t₁ else e₁) (if c then t₂ else e₂) := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact ht hc
  · simp only [hc, ite_false]; exact he hc

end OverlapNG

theorem genesis_false_of_pure (blks : List Blk) (hng : blks.any (·.isGenesis) = false) {i : Nat}
    {b B : Blk} (hB : blks[i]? = some b) (hp : (pure b : Except String Blk) = .ok B) : B.isGenesis = false := by
  cases hp
  exact genesis_false_of_get blks hng i b hB

theorem throw_ne_ok {α : Type} {e : String} {a : α} (h : (throw e : Except String α) = .ok a) : False := by
  cases h

theorem some_of_match_ok {o : Option Blk} {B : Blk} {m : String}
    (h : (match o with | some b => (pure b : Except String Blk) | none => throw m) = .ok B) : o = some B := by
  cases o with
  | none => cases h
  | some b => cases h; rfl

/-- On a segment without a genesis block the genesis-capable shell is the non-genesis one, error
string included. -/
theorem checkD2CoreGWith_eq_of_segment (d : ExecutionDriver) (hd : d.resharding = false)
    (h : ActionHooks) (a : Bool) (cb wb : Bytes) (g : Option Nat) (hng : segmentHasGenesis cb = false) :
    checkD2CoreGWith d h a cb wb g = checkD2CoreWith d h a cb wb g := by
  unfold segmentHasGenesis at hng
  cases hc : decodeClaimE cb with
  | error e => rw [hc] at hng; cases hng
  | ok c =>
    rw [hc] at hng
    cases hb : c.blocks.mapM decodeBlk with
    | error e => simp only [hb] at hng; cases hng
    | ok blks =>
      simp only [hb] at hng
      have key : ∀ W, W = checkD2CoreWithObs d h a cb wb g →
          OverlapNG W (checkD2CoreGWith d h a cb wb g) (checkD2CoreWithObs d h a cb wb g) := by
        intro W hWfull
        conv => rhs; unfold checkD2CoreWithObs
        conv => lhs; unfold checkD2CoreGWith
        simp only [hc, hb, hd, Except.mapError, ok_bind', Bool.not_false, ↓reduceIte]
        repeat (first
          | (exfalso; exact throw_ne_ok (by assumption))
          | (refine OverlapNG.diverge _
              (genesis_false_of_pure blks hng (by assumption) (by assumption)) _
              (by subst_vars; rfl))
          | ((refine OverlapNG.bind' (by with_reducible rfl) fun (_, _) => ?_); try dsimp only)
          | ((refine OverlapNG.bindE (by with_reducible rfl) fun _ _ => ?_); try dsimp only)
          | (refine OverlapNG.error_both _ rfl rfl)
          | ((refine OverlapNG.bind' (by rfl) fun (_, _) => ?_); try dsimp only)
          | ((refine OverlapNG.bind' (by rfl) fun _ => ?_); try dsimp only)
          | (refine OverlapNG.ite_congr _ (fun _ => ?_) (fun _ => ?_))
          | (split <;> (rename_i hsplit; (try simp only [hsplit]); (try dsimp only))))
      exact key _ rfl rfl


/-! ## O6 at configuration and tier level -/

/-- **O6.** On every whole-state configuration with the genesis main transition and the Gate-B
bounds in force, switching resharding on preserves every decided verdict (`VRefines`): on segments
with a genesis block both run the genesis-capable shell (`checkD2CoreGWith_resharding_mono`); on the
others the resharding tier runs `ReshardCore`, which decides every one-layout, no-split-gate segment
as the plain shell does (`checkD2CoreWith_vrefines_reshard`), and the plain shell excludes every other
segment (`c.same_layout`, `c.no_split_gate`). -/
theorem checkSuccessor_resharding_vmono (cfg : ProtocolCfg) (hr : cfg.resharding = false)
    (hgen : cfg.genesisMainTransition = true) (hsr : cfg.storageResolution = true)
    (hseg : cfg.segmentUnbounded = false) (hwu : cfg.witnessUnbounded = false)
    (hlu : cfg.layoutUnbounded = false) :
    VLift cfg { cfg with resharding := true } := by
  intro c w
  unfold checkSuccessor
  simp only [hr, hsr, hgen, Bool.false_and, Bool.true_and, Bool.true_or, Bool.or_true, ↓reduceIte,
    Bool.false_eq_true]
  split
  · cases hg : segmentHasGenesis c
    · simp only [Bool.not_false, ↓reduceIte]
      rw [checkD2CoreGWith_eq_of_segment _ rfl _ _ _ _ _ hg]
      exact checkD2CoreWith_vrefines_reshard _ rfl rfl hwu hlu hseg rfl _ _ _ _ _ hg
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact (checkD2CoreGWith_resharding_mono _ rfl rfl _ _ _ _ _ _).toV
  · exact (Refines.refl _).toV

/-- `.curveHosts ⊑ .resharding` at verdict level, on every input. -/
theorem relSuccessor_resharding_vmono (c w : Bytes) :
    VRefines (Tier.checker .curveHosts c w) (Tier.checker .resharding c w) :=
  checkSuccessor_resharding_vmono (Tier.cfg .curveHosts) rfl rfl rfl rfl rfl rfl c w

/-- The resharding step of `.globalActions ⊑ .allFeatures` (the `hR` premise of
`relSuccessor_globalActions_allFeatures_of`). -/
theorem resharding_vlift_globalActionsCurve :
    VLift { Tier.cfg .globalActions with curveHosts := true }
      { Tier.cfg .globalActions with curveHosts := true, resharding := true } :=
  checkSuccessor_resharding_vmono _ rfl rfl rfl rfl rfl rfl

/-- The resharding step of `.curveHosts ⊑ .allFeatures` (the `hR` premise of
`relSuccessor_curveHosts_allFeatures_of`). -/
theorem resharding_vlift_curveHosts : VLift (Tier.cfg .curveHosts) (Tier.cfg .resharding) :=
  checkSuccessor_resharding_vmono (Tier.cfg .curveHosts) rfl rfl rfl rfl rfl rfl

/-- `.curveHosts ⊑ .allFeatures` at verdict level, given only the global-action lift (O3). -/
theorem relSuccessor_curveHosts_allFeatures_of_GA
    (hGA : Lift (Tier.cfg .resharding) { Tier.cfg .resharding with globalActions := true }) (c w : Bytes) :
    VRefines (Tier.checker .curveHosts c w) (Tier.checker .allFeatures c w) :=
  relSuccessor_curveHosts_allFeatures_of resharding_vlift_curveHosts hGA c w

/-- `.globalActions ⊑ .allFeatures` at verdict level, given only the curve-host lift (O2). -/
theorem relSuccessor_globalActions_allFeatures_of_C
    (hC : Lift (Tier.cfg .globalActions) { Tier.cfg .globalActions with curveHosts := true }) (c w : Bytes) :
    VRefines (Tier.checker .globalActions c w) (Tier.checker .allFeatures c w) :=
  relSuccessor_globalActions_allFeatures_of hC resharding_vlift_globalActionsCurve c w

#print axioms walk_one_layout
#print axioms checkD2CoreWithObs_vr_reshard
#print axioms checkD2CoreWith_vrefines_reshard
#print axioms checkD2CoreGWith_eq_of_segment
#print axioms checkSuccessor_resharding_vmono
#print axioms relSuccessor_resharding_vmono
#print axioms resharding_vlift_globalActionsCurve
#print axioms resharding_vlift_curveHosts
#print axioms relSuccessor_curveHosts_allFeatures_of_GA
#print axioms relSuccessor_globalActions_allFeatures_of_C

end NearSpecV3.Successor
