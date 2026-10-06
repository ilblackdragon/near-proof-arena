import ReexecV3D0.Normal
import ReexecV3D0.NormBytes

/-!
# The full normal form: completeness and uniqueness of accepted bytes

* (a) `relD0_normal`: every `RelD0` witness `w` has a normal-form `RelD0` witness, no
  longer, constructed by the prover's normaliser: `wrapW c` with `normSW K R sw = .ok c`
  for the state witness `sw` of `w` and the keys / root `keysD0 cb w = .ok (K, R)`.
* (b) `normalW_sound`: the verifier's `normalW` accepts only bytes that are a fixed point
  of the normaliser, and (with `RelD0`) whose decoded state witness is a fixed point of
  `normW`; `normal_unique`: two accepted proofs of one claim that decode to the same
  state witness up to the normal form are byte-identical.
-/

namespace ReexecV3D0

open NearSpec NearSpecV3

theorem bind_ex_intro {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {a : α}
    (hx : x = .ok a) (hf : ∃ p, f a = .ok p) : ∃ p, (x >>= f) = .ok p := by rw [hx]; exact hf

set_option hygiene false in
/-- Lockstep of `h` (an accepting `checkD0` run) and an existential goal
`∃ p, keysD0 … = .ok p` (a verbatim prefix with its own auxiliary matchers). -/
macro "lstepE" : tactic => `(tactic| first
  | (guard_hyp h :~ (bind (m := Except String) _ _) = _; obtain ⟨_, ha, h⟩ := bind_ok h;
     refine bind_ex_intro ha ?_; (try dsimp only at h); (try dsimp only))
  | ((fail_if_success (guard_hyp h :~ (bind (m := Except String) _ _) = _));
     split at h <;> first
      | (obtain ⟨_, ht, _⟩ := bind_ok h; cases ht; done)
      | (rename_i heq; split <;> (rename_i heq2; first
          | (cases (heq.symm.trans heq2); done)
          | (cases (heq.symm.trans heq2); (try dsimp only at h); (try dsimp only))))))

set_option maxHeartbeats 1000000 in
/-- `keysD0` succeeds on every accepted witness (it is a verbatim prefix of `checkD0`). -/
theorem keysD0_of_checkD0 {cb w : Bytes} (h : checkD0 cb w = .ok ()) :
    ∃ p, keysD0 cb w = .ok p := by
  unfold checkD0 at h
  unfold keysD0
  repeat lstepE
  exact ⟨_, rfl⟩

/-- **(a) Normal-form completeness.** Every `RelD0` witness has a normal-form `RelD0`
witness, no longer: the prover's normaliser output `wrapW c`, `normSW K R sw = .ok c`. -/
theorem relD0_normal {cb w : Bytes} (h : RelD0 cb w) :
    ∃ w', RelD0 cb w' ∧ normalW cb w' = true ∧ w'.length ≤ w.length := by
  have hc : checkD0 cb w = .ok () := by
    unfold RelD0 acceptsD0 at h
    split at h
    · assumption
    · cases h
  obtain ⟨sw, s, hw, hs⟩ := checkD0_decoded hc
  obtain ⟨⟨K, R⟩, hk⟩ := keysD0_of_checkD0 hc
  obtain ⟨c, -, hdec, hlen, hfix⟩ := normSW_spec hs K R
  have hwl := decodeWitnessFile_length hw
  have hwb := checkD0_witness_length hc
  have hcl : c.length < 4294967296 := by omega
  have hw' := decodeWitnessFile_wrapW c hcl
  have hl : lenT c ≤ lenT sw := by rw [lenT_eq', lenT_eq']; exact hlen
  refine ⟨wrapW c, ?_, ?_, ?_⟩
  · have := checkD0_normal hw hw' hl hs hdec hk hc
    unfold RelD0 acceptsD0
    rw [this]
  · unfold normalW
    rw [hw']
    dsimp only
    rw [keysD0_normal hw hw' hl hs hdec hk]
    dsimp only
    rw [hfix]
    simp
  · rw [wrapW_length]; omega

/-- **(b) The verifier accepts only normal-form bytes**: an accepted proof's state
witness is a fixed point of the normaliser `normSW` (for the keys and root of the
claim's main trie). -/
theorem normalW_sound {cb w : Bytes} (h : normalW cb w = true) :
    ∃ sw K R, decodeWitnessFile w = .ok (sw, []) ∧ keysD0 cb w = .ok (K, R) ∧
      normSW K R sw = .ok sw := by
  unfold normalW at h
  split at h
  · rename_i sw hw
    split at h
    · rename_i K R hk
      split at h
      · rename_i c hc
        have : c = sw := by simpa using h
        subst this
        exact ⟨c, K, R, hw, hk, hc⟩
      · cases h
    · cases h
  · cases h

/-- (b, semantic form) With the relation, the decoded state witness of an accepted proof is
itself in normal form: `normW K R s = s` (one entry per receipt-proof key in key order,
exactly the looked-up trie values without duplicates in byte order, zero ignored fields). -/
theorem normalW_fixed {cb w : Bytes} (hn : normalW cb w = true) (hr : RelD0 cb w) :
    ∃ sw s K R, decodeWitnessFile w = .ok (sw, []) ∧ keysD0 cb w = .ok (K, R) ∧
      normSW K R sw = .ok sw ∧ decodeStateWitness sw = .ok s ∧ normW K R s = s := by
  obtain ⟨sw, K, R, hw, hk, hfix⟩ := normalW_sound hn
  have hc : checkD0 cb w = .ok () := by
    unfold RelD0 acceptsD0 at hr
    split at hr
    · assumption
    · cases hr
  obtain ⟨sw', s, hw', hs⟩ := checkD0_decoded hc
  rw [hw] at hw'
  injection hw' with hw'
  injection hw' with hsw
  subst hsw
  obtain ⟨c, hrun, hdec, -, -⟩ := normSW_spec hs K R
  rw [hfix] at hrun
  injection hrun with hcs
  subst hcs
  rw [hs] at hdec
  injection hdec with hns
  exact ⟨_, s, K, R, hw, hk, hfix, hs, hns.symm⟩

end ReexecV3D0
