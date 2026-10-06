import NearSpecV3.ChunkValidationD2

/-!
# Honest proofs are bounded: `RelD2 cb w → w.length ≤ 8 388 641`

The proof of the `reexec-v3-d2` backend is the witness file itself. `checkD2`
(step 1, spec §3.1 + domain condition `w.size`) only accepts a `witness.bin` that
decodes as `bytes "near-arena-witness-v3" ‖ bytes state_witness ‖ Vec<bytes>
contract_code` with no trailing bytes, an empty code list (`w.no_code`) and
`|state_witness| ≤ 8 MiB`, so its length is `4 + 21 + 4 + |state_witness| + 4`.

Everything here is about the trusted parsers of `NearSpecV3.Wire` /
`NearSpecV3.WitnessV3`; no definition is changed.
-/

namespace ReexecV3D2

open NearSpec NearSpecV3

/-! ## `Except` plumbing -/

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem check_ok {b : Bool} {m : String} (h : NearSpecV3.check b m = .ok ()) : b = true := by
  unfold NearSpecV3.check at h; split at h <;> simp_all

/-! ## Byte-count facts of the primitive parsers -/

theorem revAppend_length (x y : List UInt8) : (revAppend x y).length = x.length + y.length := by
  induction x generalizing y with
  | nil => simp [revAppend]
  | cons a as ih => simp [revAppend, ih]; omega

theorem takeAcc_length {n : Nat} {acc bs h t : List UInt8} (e : takeAcc n acc bs = some (h, t)) :
    h.length = n + acc.length ∧ bs.length = n + t.length := by
  induction n generalizing acc bs with
  | zero =>
    simp only [takeAcc, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    simp [revAppend_length]
  | succ n ih =>
    cases bs with
    | nil => simp [takeAcc] at e
    | cons b bs =>
      simp only [takeAcc] at e
      have := ih e
      simp only [List.length_cons] at this ⊢
      omega

theorem takeT_length {n : Nat} {bs h t : List UInt8} (e : takeT n bs = some (h, t)) :
    h.length = n ∧ bs.length = n + t.length := by
  have := takeAcc_length e
  simpa using this

theorem takeN_length {n : Nat} {bs h t : List UInt8} (e : takeN n bs = some (h, t)) :
    bs.length = n + t.length := by
  induction n generalizing bs h with
  | zero => simp only [takeN, Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨-, rfl⟩ := e; simp
  | succ n ih =>
    cases bs with
    | nil => simp [takeN] at e
    | cons b bs =>
      simp only [takeN, Option.map_eq_some_iff] at e
      obtain ⟨⟨h', t'⟩, e', he⟩ := e
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      have := ih e'
      simp only [List.length_cons]; omega

theorem readU32_length {bs t : List UInt8} {n : Nat} (e : readU32 bs = some (n, t)) :
    bs.length = 4 + t.length := by
  simp only [readU32, readLE, Option.map_eq_some_iff] at e
  obtain ⟨⟨h', t'⟩, e', he⟩ := e
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl⟩ := he
  exact takeN_length e'

theorem pBytes_length {w : String} {bs x t : List UInt8} (e : pBytes w bs = .ok (x, t)) :
    bs.length = 4 + x.length + t.length := by
  unfold pBytes lift at e
  split at e
  · rename_i r hr
    simp only [Except.ok.injEq] at e
    subst e
    simp only [readBytesT] at hr
    split at hr
    · cases hr
    · rename_i n rest hu
      have h1 := readU32_length hu
      have h2 := takeT_length hr
      omega
  · cases e

theorem pU32_length {w : String} {bs t : List UInt8} {n : Nat} (e : pU32 w bs = .ok (n, t)) :
    bs.length = 4 + t.length := by
  unfold pU32 lift at e
  split at e
  · rename_i r hr
    simp only [Except.ok.injEq] at e
    subst e
    exact readU32_length hr
  · cases e

theorem pMany_nil {α : Type} {p : P α} {n : Nat} {bs t : List UInt8}
    (e : pMany p n bs = .ok ([], t)) : n = 0 ∧ t = bs := by
  cases n with
  | zero => simp only [pMany, Except.ok.injEq, Prod.mk.injEq] at e; exact ⟨rfl, e.2.symm⟩
  | succ n =>
    exfalso
    simp only [pMany] at e
    obtain ⟨⟨a, bs1⟩, -, e⟩ := bind_ok e
    obtain ⟨⟨as, bs2⟩, -, e⟩ := bind_ok e
    cases e

theorem pVec_nil_length {α : Type} {w : String} {p : P α} {bs t : List UInt8}
    (e : pVec w p bs = .ok ([], t)) : bs.length = 4 + t.length := by
  unfold pVec at e
  obtain ⟨⟨n, bs1⟩, h1, e⟩ := bind_ok e
  have := pU32_length h1
  have := (pMany_nil e).2
  subst this
  omega

theorem dTag_length {want : Bytes} {what : String} {bs t : List UInt8} {u : Unit}
    (e : dTag want what bs = .ok (u, t)) : bs.length = 4 + want.length + t.length := by
  unfold dTag at e
  obtain ⟨⟨got, rest⟩, h1, e⟩ := bind_ok e
  have := pBytes_length h1
  by_cases hg : (got == want) = true
  · simp only [hg, if_true, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨-, rfl⟩ := e
    have : got = want := by simpa using hg
    subst this
    omega
  · simp only [hg, Bool.false_eq_true, if_false] at e
    cases e

theorem lenAcc_eq (b : List UInt8) (n : Nat) : lenAcc b n = b.length + n := by
  induction b generalizing n with
  | nil => simp [lenAcc]
  | cons x xs ih => simp [lenAcc, ih]; omega

theorem lenT_eq (b : List UInt8) : lenT b = b.length := by simp [lenT, lenAcc_eq]

/-! ## The witness file -/

theorem witnessTag_length : witnessTag.length = 21 := by decide

theorem decodeWitnessFile_length {w sw : Bytes}
    (e : decodeWitnessFile w = .ok (sw, [])) : w.length = 33 + sw.length := by
  unfold decodeWitnessFile at e
  obtain ⟨⟨u, bs1⟩, h1, e⟩ := bind_ok e
  obtain ⟨⟨sw', bs2⟩, h2, e⟩ := bind_ok e
  obtain ⟨⟨codes, bs3⟩, h3, e⟩ := bind_ok e
  have l1 := dTag_length h1
  have l2 := pBytes_length h2
  by_cases hemp : bs3.isEmpty = true
  · simp only [hemp, Bool.not_true, Bool.false_eq_true, if_false, pure, Except.pure, bind,
      Except.bind, Except.ok.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have l3 := pVec_nil_length h3
    have : bs3 = [] := by simpa using hemp
    subst this
    rw [witnessTag_length] at l1
    simp at l3
    omega
  · simp only [hemp, Bool.not_false, if_true, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at e
    cases e

/-- **Size bound.** Every witness of `RelD2` is at most 8 388 641 bytes. -/
theorem checkD2_witness_length {cb w : Bytes} (h : checkD2 cb w = .ok ()) :
    w.length ≤ 8388641 := by
  unfold checkD2 checkD2Core at h
  simp only [Bool.not_false, ite_true] at h
  obtain ⟨c, -, h⟩ := bind_ok h
  obtain ⟨⟨sw, codes⟩, hw, h⟩ := bind_ok h
  obtain ⟨u1, h1, h⟩ := bind_ok h
  obtain ⟨u2, h2, -⟩ := bind_ok h
  have hc : codes.isEmpty = true := check_ok (by cases u1; exact h1)
  have hs : decide (lenT sw ≤ 8388608) = true := check_ok (by cases u2; exact h2)
  have : codes = [] := by simpa using hc
  subst this
  have hl := decodeWitnessFile_length hw
  have : lenT sw ≤ 8388608 := by simpa using hs
  rw [lenT_eq] at this
  omega

theorem relD2_witness_length {cb w : Bytes} (h : RelD2 cb w) : w.length ≤ 8388641 := by
  unfold RelD2 acceptsD2 at h
  split at h
  · rename_i hc
    exact checkD2_witness_length hc
  · cases h

end ReexecV3D2
