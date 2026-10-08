import ZkFormal.NearV3.Assembly.RcptCandidateLayout
-- Source Chars.lean SHA256: b93273f6d8f3a5a4b2dadde3de2a537608fad6459aa38ef5056ee16691abb51a.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.Bus

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.Chars (v1 `RcptChars`) — account-id characters (row level)

On a row of the `P`, `V`, `S` fields the byte is `16·hi + lo` with
`hi = 2·h2 + 3·h3 + 5·h5 + 6·h6 + 7·h7` (one-hot) and `lo` the four bits `lb`.
-/

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL chain chainC convS convR sumL_congr sumL_lt le256_map_range sumL_add convS_id)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

def hiV (tr : Trace Fp) (tt : Nat) (q : Nat) : Nat :=
  2 * cv tr tt q h2 + 3 * cv tr tt q h3 + 5 * cv tr tt q h5 + 6 * cv tr tt q h6 +
    7 * cv tr tt q h7
def loV (tr : Trace Fp) (tt : Nat) (q : Nat) : Nat := bitsVal (fun j => cv tr tt q (lb j)) 0 4

def charCols : List Nat := [h2, h3, h5, h6, h7, z, hx6] ++ (List.range 4).map lb

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

theorem charBool {q : Nat} (hq : q < tr.height tt) {x : Nat} (hx : x ∈ charCols) :
    tr.cell tt q x = 0 ∨ tr.cell tt q x = 1 := by
  have := con hL hq (e := Dsl.bool (c x)) (mem_ch (by
    unfold cChars; simp only [List.mem_append]
    exact Or.inl (List.mem_map_of_mem (f := fun x => Dsl.bool (c x)) (show x ∈ charCols from hx))))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem SS_eval {q X : Nat} (hq : q < tr.height tt) (hX : X = sP ∨ X = sV ∨ X = sS)
    (h1 : tr.cell tt q X = 1) : SS.eval tr tt q pub = 1 := by
  have hXs : X ∈ states := by rcases hX with rfl | rfl | rfl <;> simp [states]
  have oh := (oneHot hL hq hXs h1).2
  simp only [SS, eval_sum_cons, eval_sum_nil, eval_c]
  rcases hX with rfl | rfl | rfl
  · rw [h1, oh sV (by simp [states]) (by decide), oh sS (by simp [states]) (by decide)]; grind
  · rw [h1, oh sP (by simp [states]) (by decide), oh sS (by simp [states]) (by decide)]; grind
  · rw [h1, oh sP (by simp [states]) (by decide), oh sV (by simp [states]) (by decide)]; grind

/-- **Character value.** -/
theorem char_val {q X : Nat} (hq : q < tr.height tt) (hX : X = sP ∨ X = sV ∨ X = sS)
    (h1 : tr.cell tt q X = 1) :
    cv tr tt q b = 16 * hiV tr tt q + loV tr tt q ∧ loV tr tt q < 16 ∧ hiV tr tt q ≤ 7 ∧
      hiE.eval tr tt q pub = ((hiV tr tt q : Nat) : Fp) ∧ loE.eval tr tt q pub = ((loV tr tt q : Nat) : Fp) := by
  have hSS := SS_eval hL hq hX h1
  have c1 := con hL hq (e := .mul SS (sub (c b) (.add (smul 16 hiE) loE))) (mem_ch (by simp [cChars]))
  have c2 := con hL hq (e := .mul SS (sub (sum [c h2, c h3, c h5, c h6, c h7]) (k 1))) (mem_ch (by simp [cChars]))
  simp only [eval_mul, eval_sub, eval_add, eval_smul, eval_c, eval_k, eval_sum_cons, eval_sum_nil] at c1 c2
  rw [hSS] at c1 c2
  have bl : ∀ j, j < 4 → tr.cell tt q (lb (0 + j)) = 0 ∨ tr.cell tt q (lb (0 + j)) = 1 := fun j hj =>
    charBool hL hq (by unfold charCols; simp only [List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨j, hj, by simp⟩)
  have hlo : loE.eval tr tt q pub = ((loV tr tt q : Nat) : Fp) := eval_bits tr tt q pub lb 0 4 bl
  have hlt : loV tr tt q < 16 := bitsVal_lt _ 0 4 (fun j hj => cv_bool (bl j hj))
  have hhi : hiE.eval tr tt q pub = ((hiV tr tt q : Nat) : Fp) := by
    simp only [hiE, eval_sum_cons, eval_sum_nil, eval_smul, eval_c, hiV]
    rw [cell_eq_cast tr tt q h2, cell_eq_cast tr tt q h3, cell_eq_cast tr tt q h5,
      cell_eq_cast tr tt q h6, cell_eq_cast tr tt q h7]
    grind
  -- one-hot high nibble
  have b2 := cv_bool (charBool hL hq (x := h2) (by simp [charCols]))
  have b3 := cv_bool (charBool hL hq (x := h3) (by simp [charCols]))
  have b5 := cv_bool (charBool hL hq (x := h5) (by simp [charCols]))
  have b6 := cv_bool (charBool hL hq (x := h6) (by simp [charCols]))
  have b7 := cv_bool (charBool hL hq (x := h7) (by simp [charCols]))
  have hsum : cv tr tt q h2 + cv tr tt q h3 + cv tr tt q h5 + cv tr tt q h6 +
      cv tr tt q h7 = 1 := by
    apply ofNat_inj (by unfold P; omega) (by unfold P; omega)
    rw [cell_eq_cast tr tt q h2, cell_eq_cast tr tt q h3, cell_eq_cast tr tt q h5,
      cell_eq_cast tr tt q h6, cell_eq_cast tr tt q h7] at c2
    grind
  have hhi7 : hiV tr tt q ≤ 7 := by unfold hiV; omega
  refine ⟨?_, hlt, hhi7, hhi, hlo⟩
  have e : tr.cell tt q b = (((16 * hiV tr tt q + loV tr tt q : Nat) : Nat) : Fp) := by
    rw [natCast_add, natCast_mul, ← hhi, ← hlo]; grind
  rw [cv, e, toNat_natCast, Nat.mod_eq_of_lt (by unfold P; omega)]

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
