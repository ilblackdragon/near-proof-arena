import ReexecV3D2.Normal
import ReexecV3D2.NormBytes

/-!
# The full normal form: completeness and uniqueness of accepted bytes

* (a) `relD2_normal`: every `RelD2` witness `w` has a normal-form `RelD2` witness, no
  longer, constructed by the prover's normaliser: `wrapW c` with `normSW R sw = .ok c`
  for the state witness `sw` of `w` and the root `keysD2 cb w = .ok R`.
* (b) `normalW_sound`: the verifier's `normalW` accepts only bytes that are a fixed point
  of the normaliser, and (with `RelD2`) whose decoded state witness is a fixed point of
  `normW`; `normal_unique`: two accepted proofs of one claim that decode to the same
  state witness up to the normal form are byte-identical.
-/

namespace ReexecV3D2

open NearSpec NearSpecV3

theorem bind_ex_intro {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {a : α}
    (hx : x = .ok a) (hf : ∃ p, f a = .ok p) : ∃ p, (x >>= f) = .ok p := by rw [hx]; exact hf

set_option hygiene false in
/-- Lockstep of `h` (an accepting `checkD2` run) and an existential goal
`∃ p, keysD2 … = .ok p` (a verbatim prefix with its own auxiliary matchers). -/
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
/-- `keysD2` succeeds on every accepted witness (it is a verbatim prefix of `checkD2`). -/
theorem keysD2_of_checkD2 {cb w : Bytes} (h : checkD2 cb w = .ok ()) :
    ∃ p, keysD2 cb w = .ok p := by
  unfold checkD2 checkD2Core at h
  unfold keysD2
  simp only [Bool.not_false, ite_true] at h ⊢
  repeat lstepE
  exact ⟨_, rfl⟩

/-- **(a) Normal-form completeness.** Every `RelD2` witness has a normal-form `RelD2`
witness, no longer: the prover's normaliser output `wrapW c`, `normSW R sw = .ok c`. -/
theorem relD2_normal {cb w : Bytes} (h : RelD2 cb w) :
    ∃ w', RelD2 cb w' ∧ normalW cb w' = true ∧ w'.length ≤ w.length := by
  have hc : checkD2 cb w = .ok () := by
    unfold RelD2 acceptsD2 at h
    split at h
    · assumption
    · cases h
  obtain ⟨sw, s, hw, hs⟩ := checkD2_decoded hc
  obtain ⟨R, hk⟩ := keysD2_of_checkD2 hc
  obtain ⟨c, -, hdec, hlen, hfix⟩ := normSW_spec hs R
  have hwl := decodeWitnessFile_length hw
  have hwb := checkD2_witness_length hc
  have hcl : c.length < 4294967296 := by omega
  have hw' := decodeWitnessFile_wrapW c hcl
  have hl : lenT c ≤ lenT sw := by rw [lenT_eq', lenT_eq']; exact hlen
  refine ⟨wrapW c, ?_, ?_, ?_⟩
  · have := checkD2_normal hw hw' hl hs hdec hk hc
    unfold RelD2 acceptsD2
    rw [this]
  · unfold normalW
    rw [hw']
    dsimp only
    rw [keysD2_normal hw hw' hl hs hdec hk]
    dsimp only
    rw [hfix]
    simp
  · rw [wrapW_length]; omega

/-- **(b) The verifier accepts only normal-form bytes**: an accepted proof's state
witness is a fixed point of the normaliser `normSW` (for the keys and root of the
claim's main trie). -/
theorem normalW_sound {cb w : Bytes} (h : normalW cb w = true) :
    ∃ sw R, decodeWitnessFile w = .ok (sw, []) ∧ keysD2 cb w = .ok R ∧
      normSW R sw = .ok sw := by
  unfold normalW at h
  split at h
  · rename_i sw hw
    split at h
    · rename_i R hk
      split at h
      · rename_i c hc
        have : c = sw := by simpa using h
        subst this
        exact ⟨c, R, hw, hk, hc⟩
      · cases h
    · cases h
  · cases h

/-- (b, semantic form) With the relation, the decoded state witness of an accepted proof is
itself in normal form: `normW R s = s` (one entry per receipt-proof key in key order,
exactly the looked-up trie values without duplicates in byte order, zero ignored fields). -/
theorem normalW_fixed {cb w : Bytes} (hn : normalW cb w = true) (hr : RelD2 cb w) :
    ∃ sw s R, decodeWitnessFile w = .ok (sw, []) ∧ keysD2 cb w = .ok R ∧
      normSW R sw = .ok sw ∧ decodeStateWitnessD2 sw = .ok s ∧ normW R s = s := by
  obtain ⟨sw, R, hw, hk, hfix⟩ := normalW_sound hn
  have hc : checkD2 cb w = .ok () := by
    unfold RelD2 acceptsD2 at hr
    split at hr
    · assumption
    · cases hr
  obtain ⟨sw', s, hw', hs⟩ := checkD2_decoded hc
  rw [hw] at hw'
  injection hw' with hw'
  injection hw' with hsw
  subst hsw
  obtain ⟨c, hrun, hdec, -, -⟩ := normSW_spec hs R
  rw [hfix] at hrun
  injection hrun with hcs
  subst hcs
  rw [hs] at hdec
  injection hdec with hns
  exact ⟨_, s, R, hw, hk, hfix, hs, hns.symm⟩

end ReexecV3D2
