import ZkFormal.Udr.Np.ShapeLate

/-!
# ZkFormal.Udr.Np.FrameFri — frame lemmas for the late (DEEP/FRI) rounds

* `friF_congr`: the FRI layer word `friF i` depends on the transcript only
  through the header, the oracles, the batched DEEP words and the lookups of
  FRI challenges of key `≤ 2i` (key of `γ_i` is `2i`, of `β_i` is `2i + 1`);
  the same for `evenF`, `oddF`, `foldF`, `rollG`, and `FriChalGood` of a kind
  of key `k` (lookups of key `< k`).
* `globalFail_pushChal`: `GlobalFail` survives a challenge.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-- Position of a FRI challenge kind in the schedule order. -/
def keyOf (k : Bool × Nat) : Nat := if k.1 then 2 * k.2 else 2 * k.2 + 1

section
variable (A : Air) (prm : Params)

/-- Two transcripts agree on everything the FRI words read, except possibly
FRI challenges. -/
structure SameFri (τ τ' : PTn) : Prop where
  hdr : hdrOf τ' = hdrOf τ
  orc : τ'.oracles = τ.oracles
  deep : ∀ m p, deepAtPos A prm τ' m p = deepAtPos A prm τ m p

variable {A prm}

theorem SameFri.n0 {τ τ' : PTn} (h : SameFri A prm τ τ') : n0Of A prm τ' = n0Of A prm τ := by
  simp [n0Of, h.hdr]
theorem SameFri.ell {τ τ' : PTn} (h : SameFri A prm τ τ') : ellOf A prm τ' = ellOf A prm τ := by
  simp [ellOf, h.hdr]
theorem SameFri.commits {τ τ' : PTn} (h : SameFri A prm τ τ') :
    commitsOf A prm τ' = commitsOf A prm τ := by
  simp [commitsOf, h.hdr]
theorem SameFri.permAt {τ τ' : PTn} (h : SameFri A prm τ τ') :
    permAt A prm τ' = permAt A prm τ := by
  funext i j; simp [Np.permAt, h.n0, h.ell]
theorem SameFri.setup {τ τ' : PTn} (h : SameFri A prm τ τ') :
    setupData A prm τ' = setupData A prm τ := by
  simp [setupData, h.n0, h.ell, h.permAt]
theorem SameFri.committed {τ τ' : PTn} (h : SameFri A prm τ τ') :
    committedAt τ' = committedAt τ := by
  funext k a p; simp [committedAt, oracleOf, h.orc]
theorem SameFri.rollG {τ τ' : PTn} (h : SameFri A prm τ τ') :
    rollG A prm τ' = rollG A prm τ := by
  funext i j u; simp [Np.rollG, h.hdr, h.n0, h.permAt, h.deep]

theorem friF_congr {τ τ' : PTn} (h : SameFri A prm τ τ') :
    ∀ i, (∀ k, keyOf k ≤ 2 * i → (friChals A prm τ').lookup k = (friChals A prm τ).lookup k) →
      friF A prm τ' i = friF A prm τ i
  | 0, _ => by
    simp only [friF, h.commits, h.committed, h.permAt, h.deep, h.n0]
  | i + 1, hk => by
    have ih := friF_congr h i fun k hk' => hk k (by omega)
    have hb : betaOf A prm τ' i = betaOf A prm τ i := by
      simp only [betaOf]; rw [hk (false, i) (by simp [keyOf]; omega)]
    have hg : gammaOf A prm τ' (i + 1) = gammaOf A prm τ (i + 1) := by
      simp only [gammaOf]; rw [hk (true, i + 1) (by simp [keyOf])]
    simp only [friF, h.commits, h.committed, h.permAt, h.setup, ih, hb, hg, h.rollG]

theorem evenF_congr {τ τ' : PTn} (h : SameFri A prm τ τ') (i : Nat)
    (hk : ∀ k, keyOf k ≤ 2 * i → (friChals A prm τ').lookup k = (friChals A prm τ).lookup k) :
    evenF A prm τ' i = evenF A prm τ i := by
  funext j u; simp only [evenF, friF_congr h i hk, h.setup]

theorem oddF_congr {τ τ' : PTn} (h : SameFri A prm τ τ') (i : Nat)
    (hk : ∀ k, keyOf k ≤ 2 * i → (friChals A prm τ').lookup k = (friChals A prm τ).lookup k) :
    oddF A prm τ' i = oddF A prm τ i := by
  funext j u; simp only [oddF, friF_congr h i hk, h.setup]

theorem foldF_congr {τ τ' : PTn} (h : SameFri A prm τ τ') (i : Nat)
    (hk : ∀ k, keyOf k ≤ 2 * i + 1 → (friChals A prm τ').lookup k = (friChals A prm τ).lookup k) :
    foldF A prm τ' i = foldF A prm τ i := by
  have hb : betaOf A prm τ' i = betaOf A prm τ i := by
    simp only [betaOf]; rw [hk (false, i) (by simp [keyOf])]
  simp only [foldF, evenF_congr h i (fun k h' => hk k (by omega)),
    oddF_congr h i (fun k h' => hk k (by omega)), hb]

/-- The strong-line condition of a kind depends only on lookups of smaller keys. -/
theorem friChalGood_congr {τ τ' : PTn} (h : SameFri A prm τ τ') (k : Bool × Nat) (hk1 : k.1 → 1 ≤ k.2)
    (hk : ∀ k', keyOf k' < keyOf k → (friChals A prm τ').lookup k' = (friChals A prm τ).lookup k')
    (c : Fp8) : FriChalGood A prm τ' k.1 k.2 c ↔ FriChalGood A prm τ k.1 k.2 c := by
  rcases k with ⟨b, i⟩
  cases b with
  | true =>
    have hi := hk1 rfl
    rw [show keyOf (true, i) = 2 * i from rfl] at hk
    simp only [FriChalGood, ↓reduceIte, h.setup, h.n0, h.rollG,
      foldF_congr h (i - 1) (fun k' h' => hk k' (by omega))]
  | false =>
    rw [show keyOf (false, i) = 2 * i + 1 from rfl] at hk
    simp only [FriChalGood, Bool.false_eq_true, ↓reduceIte, h.setup, h.n0,
      evenF_congr h i (fun k' h' => hk k' (by omega)), oddF_congr h i (fun k' h' => hk k' (by omega))]

end

/-! ## `GlobalFail` under a challenge -/

theorem globalFail_pushChal (A : Air) (prm : Params) (τ : PTn) (c : Fp8) (hE : τ.entries ≠ [])
    (h : GlobalFail A prm τ) : GlobalFail A prm (τ.pushChal c) := by
  have hl : layOf A prm (τ.pushChal c) = layOf A prm τ := by
    simp [layOf, hdrOf, pushChal_header τ c hE]
  unfold GlobalFail at h ⊢
  rw [pushChal_chals, pushChal_elems, hl]
  have hcb : (τ.pushChal c).cb = τ.cb := rfl
  rw [hcb]
  revert h
  rcases τ.chals with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨z, rest⟩⟩⟩⟩ <;>
    rcases τ.elems with _ | ⟨f, _ | ⟨o, r⟩⟩ <;> simp

end ZkFormal.Udr.Np
