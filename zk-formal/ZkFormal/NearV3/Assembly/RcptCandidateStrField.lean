import ZkFormal.NearV3.Assembly.RcptCandidateCharClass
-- Source StrField.lean SHA256: 7d73a42d361862acdba5887884b66e8b37e47a73d4d697eab3680ddffcfaf8ae.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.Near.Extract.RcptStrings
import ZkFormal.NearV3.Rcpt.Extract.V.CharClass

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.StrField — account ids of a receipt are valid

A `P`, `V` or `S` field holds a valid account id (`AccountId.valid`): the
characters have the right classes, separators are not leading, trailing or
doubled, and the length is in `2 … 64`.
-/

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near ZkFormal.NearV3.RcptV3 NearSpec
open ZkFormal.Near.RcptProof (char_spec charsOk_of)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

theorem row_char {q X : Nat} (hq : q < tr.height tt) (hX : X = sP ∨ X = sV ∨ X = sS)
    (h1 : tr.cell tt q X = 1) :
    cv tr tt q b < 128 ∧
    (AccountId.isAlnum (UInt8.ofNat (cv tr tt q b)) || AccountId.isSep (UInt8.ofNat (cv tr tt q b))) = true ∧
    (AccountId.isAlnum (UInt8.ofNat (cv tr tt q b)) = true → AccountId.isSep (UInt8.ofNat (cv tr tt q b)) = false) ∧
    sepE.eval tr tt q pub = (if AccountId.isSep (UInt8.ofNat (cv tr tt q b)) = true then 1 else 0) ∧
    hexE.eval tr tt q pub = (if AccountId.isHex (UInt8.ofNat (cv tr tt q b)) = true then 1 else 0) := by
  obtain ⟨cv1, hlo, hhi, -, -⟩ := char_val hL hq hX h1
  obtain ⟨hcl, hse, hhe⟩ := char_class hL hq hX h1
  obtain ⟨a1, a2, a3, a4, a5⟩ := char_spec (hiV tr tt q) (by omega) (loV tr tt q) hlo hcl
  rw [cv1]
  refine ⟨a5, a1, a3, ?_, ?_⟩
  · rw [hse, a2]; by_cases e : hiV tr tt q = 2 ∨ hiV tr tt q = 5 <;> simp [e]
  · rw [hhe, a4]; by_cases e : hiV tr tt q = 3 ∨ (hiV tr tt q = 6 ∧ loV tr tt q ≤ 6) <;> simp [e]

theorem sepN_eval {q : Nat} (hq : q + 1 < tr.height tt) :
    sepN.eval tr tt q pub = sepE.eval tr tt (q + 1) pub := by
  simp [sepN, sepE, nxt hq]

theorem hexN_eval {q : Nat} (hq : q + 1 < tr.height tt) :
    hexN.eval tr tt q pub = hexE.eval tr tt (q + 1) pub := by
  simp [hexN, hexE, nxt hq]

/-- **A string field holds a valid account id.** -/
theorem str_valid {s r0 L X : Nat} (hX : X = sP ∨ X = sV ∨ X = sS) (F : RFld tr tt s r0 L X)
    (hH : r0 + L < tr.height tt) (hlen : 2 ≤ L ∧ L ≤ 64) :
    AccountId.valid (toBytes (colAt tr tt r0 L b)) = true ∧ Bytes8 (colAt tr tt r0 L b) := by
  have RC := fun k (hk : k < L) => row_char hL (q := r0 + k) (by omega) hX (F.fld.st k hk)
  have hSS := fun k (hk : k < L) => SS_eval hL (q := r0 + k) (by omega) hX (F.fld.st k hk)
  have gk : ∀ k (hk : k < L), (toBytes (colAt tr tt r0 L b))[k]'(by simp [toBytes, colAt_len]; omega) =
      UInt8.ofNat (cv tr tt (r0 + k) b) := by
    intro k hk; simp [toBytes, colAt]
  have hl : (toBytes (colAt tr tt r0 L b)).length = L := by simp [toBytes, colAt_len]
  refine ⟨?_, ?_⟩
  · simp only [AccountId.valid, hl, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hlen.1, hlen.2⟩, charsOk_of _ true ?_ ?_ ?_ ?_ ?_ (by intro he; rw [he] at hl; simp at hl; omega)⟩
    · intro c hc
      simp only [toBytes, colAt, List.map_map, List.mem_map, List.mem_range, Function.comp] at hc
      obtain ⟨k, hk, rfl⟩ := hc; exact (RC k hk).2.1
    · intro c hc
      simp only [toBytes, colAt, List.map_map, List.mem_map, List.mem_range, Function.comp] at hc
      obtain ⟨k, hk, rfl⟩ := hc; exact (RC k hk).2.2.1
    · intro i hi ⟨s1, s2⟩
      rw [hl] at hi
      rw [gk i (by omega)] at s1; rw [gk (i + 1) hi] at s2
      have cc := con hL (r := r0 + i) (by omega) (e := .mul (mul3 SS (Dsl.not (c fe)) sepE) sepN) (mem_ch (by simp [cChars]))
      simp only [eval_mul, eval_mul3, eval_not, eval_c] at cc
      rw [hSS i (by omega), F.fld.fe i (by omega), if_neg (by omega), sepN_eval hL (by omega),
        (RC i (by omega)).2.2.2.1, show r0 + i + 1 = r0 + (i + 1) by omega, (RC (i + 1) hi).2.2.2.1] at cc
      simp only [s1, s2, if_true] at cc
      grind
    · intro _ h0
      rw [gk 0 (by omega)]
      have cc := con hL (r := r0 + 0) (by omega) (e := mul3 SS (c fs) sepE) (mem_ch (by simp [cChars]))
      simp only [eval_mul3, eval_c] at cc
      rw [hSS 0 (by omega), F.fld.fs 0 (by omega), if_pos rfl, (RC 0 (by omega)).2.2.2.1] at cc
      by_cases e : AccountId.isSep (UInt8.ofNat (cv tr tt (r0 + 0) b)) = true
      · rw [if_pos e] at cc; grind
      · simpa using e
    · intro h0
      have e2 : (toBytes (colAt tr tt r0 L b))[(toBytes (colAt tr tt r0 L b)).length - 1] =
          UInt8.ofNat (cv tr tt (r0 + (L - 1)) b) := by simp [toBytes, colAt, colAt_len]
      rw [e2]
      have cc := con hL (r := r0 + (L - 1)) (by omega) (e := mul3 SS (c fe) sepE) (mem_ch (by simp [cChars]))
      simp only [eval_mul3, eval_c] at cc
      rw [hSS (L - 1) (by omega), F.fld.fe (L - 1) (by omega), if_pos (by omega), (RC (L - 1) (by omega)).2.2.2.1] at cc
      by_cases e : AccountId.isSep (UInt8.ofNat (cv tr tt (r0 + (L - 1)) b)) = true
      · rw [if_pos e] at cc; grind
      · simpa using e
  · intro y hy
    simp only [colAt, List.mem_map, List.mem_range] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    have := (RC k hk).1; omega

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
