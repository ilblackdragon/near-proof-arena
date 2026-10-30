import NearSpecV3.Successor.TierMono

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

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
    transitions := ((List.range b).map (fun i => WalkTransition.old i s)).reverse, stop := t }

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
    simp only [wstD, hne, Bool.false_eq_true, ↓reduceIte]
    rfl

end Walk

end NearSpecV3.Successor
