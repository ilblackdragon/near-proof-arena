import ZkFormal.Near.Extract.RcptBus

/-!
# ZkFormal.Near.Extract.RcptChars — account-id characters (row level)

On a row of the `P`, `V`, `S` fields the byte is `16·hi + lo` with
`hi = 2·h2 + 3·h3 + 5·h5 + 6·h6 + 7·h7` (one-hot) and `lo` the four bits `lb`.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

def hiV (tr : Trace Fp) (q : Nat) : Nat :=
  2 * cv tr T_RCPT q h2 + 3 * cv tr T_RCPT q h3 + 5 * cv tr T_RCPT q h5 + 6 * cv tr T_RCPT q h6 +
    7 * cv tr T_RCPT q h7
def loV (tr : Trace Fp) (q : Nat) : Nat := bitsVal (fun j => cv tr T_RCPT q (lb j)) 0 4

def charCols : List Nat := [h2, h3, h5, h6, h7, z, hx6] ++ (List.range 4).map lb

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem charBool {q : Nat} (hq : q < tr.height T_RCPT) {x : Nat} (hx : x ∈ charCols) :
    tr.cell T_RCPT q x = 0 ∨ tr.cell T_RCPT q x = 1 := by
  have := con hL hq (e := Dsl.bool (c x)) (mem_ch (by
    unfold cChars; simp only [List.mem_append]
    exact Or.inl (List.mem_map_of_mem (f := fun x => Dsl.bool (c x)) (show x ∈ charCols from hx))))
  simp only [eval_bool, eval_c] at this
  exact bool_cases this

theorem SS_eval {q X : Nat} (hq : q < tr.height T_RCPT) (hX : X = sP ∨ X = sV ∨ X = sS)
    (h1 : tr.cell T_RCPT q X = 1) : SS.eval tr T_RCPT q pub = 1 := by
  have hXs : X ∈ states := by rcases hX with rfl | rfl | rfl <;> simp [states]
  have oh := (oneHot hL hq hXs h1).2
  simp only [SS, eval_sum_cons, eval_sum_nil, eval_c]
  rcases hX with rfl | rfl | rfl
  · rw [h1, oh sV (by simp [states]) (by decide), oh sS (by simp [states]) (by decide)]; grind
  · rw [h1, oh sP (by simp [states]) (by decide), oh sS (by simp [states]) (by decide)]; grind
  · rw [h1, oh sP (by simp [states]) (by decide), oh sV (by simp [states]) (by decide)]; grind

/-- **Character value.** -/
theorem char_val {q X : Nat} (hq : q < tr.height T_RCPT) (hX : X = sP ∨ X = sV ∨ X = sS)
    (h1 : tr.cell T_RCPT q X = 1) :
    cv tr T_RCPT q b = 16 * hiV tr q + loV tr q ∧ loV tr q < 16 ∧ hiV tr q ≤ 7 ∧
      hiE.eval tr T_RCPT q pub = ((hiV tr q : Nat) : Fp) ∧ loE.eval tr T_RCPT q pub = ((loV tr q : Nat) : Fp) := by
  have hSS := SS_eval hL hq hX h1
  have c1 := con hL hq (e := .mul SS (sub (c b) (.add (smul 16 hiE) loE))) (mem_ch (by simp [cChars]))
  have c2 := con hL hq (e := .mul SS (sub (sum [c h2, c h3, c h5, c h6, c h7]) (k 1))) (mem_ch (by simp [cChars]))
  simp only [eval_mul, eval_sub, eval_add, eval_smul, eval_c, eval_k, eval_sum_cons, eval_sum_nil] at c1 c2
  rw [hSS] at c1 c2
  have bl : ∀ j, j < 4 → tr.cell T_RCPT q (lb (0 + j)) = 0 ∨ tr.cell T_RCPT q (lb (0 + j)) = 1 := fun j hj =>
    charBool hL hq (by unfold charCols; simp only [List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨j, hj, by simp⟩)
  have hlo : loE.eval tr T_RCPT q pub = ((loV tr q : Nat) : Fp) := eval_bits tr T_RCPT q pub lb 0 4 bl
  have hlt : loV tr q < 16 := bitsVal_lt _ 0 4 (fun j hj => cv_bool (bl j hj))
  have hhi : hiE.eval tr T_RCPT q pub = ((hiV tr q : Nat) : Fp) := by
    simp only [hiE, eval_sum_cons, eval_sum_nil, eval_smul, eval_c, hiV]
    rw [cell_eq_cast tr T_RCPT q h2, cell_eq_cast tr T_RCPT q h3, cell_eq_cast tr T_RCPT q h5,
      cell_eq_cast tr T_RCPT q h6, cell_eq_cast tr T_RCPT q h7]
    grind
  -- one-hot high nibble
  have b2 := cv_bool (charBool hL hq (x := h2) (by simp [charCols]))
  have b3 := cv_bool (charBool hL hq (x := h3) (by simp [charCols]))
  have b5 := cv_bool (charBool hL hq (x := h5) (by simp [charCols]))
  have b6 := cv_bool (charBool hL hq (x := h6) (by simp [charCols]))
  have b7 := cv_bool (charBool hL hq (x := h7) (by simp [charCols]))
  have hsum : cv tr T_RCPT q h2 + cv tr T_RCPT q h3 + cv tr T_RCPT q h5 + cv tr T_RCPT q h6 +
      cv tr T_RCPT q h7 = 1 := by
    apply ofNat_inj (by unfold P; omega) (by unfold P; omega)
    rw [cell_eq_cast tr T_RCPT q h2, cell_eq_cast tr T_RCPT q h3, cell_eq_cast tr T_RCPT q h5,
      cell_eq_cast tr T_RCPT q h6, cell_eq_cast tr T_RCPT q h7] at c2
    grind
  have hhi7 : hiV tr q ≤ 7 := by unfold hiV; omega
  refine ⟨?_, hlt, hhi7, hhi, hlo⟩
  have e : tr.cell T_RCPT q b = (((16 * hiV tr q + loV tr q : Nat) : Nat) : Fp) := by
    rw [natCast_add, natCast_mul, ← hhi, ← hlo]; grind
  rw [cv, e, toNat_natCast, Nat.mod_eq_of_lt (by unfold P; omega)]

end ZkFormal.Near.RcptProof
