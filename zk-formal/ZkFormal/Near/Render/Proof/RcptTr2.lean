import ZkFormal.Near.Render.Proof.RcptTr1

/-!
# ZkFormal.Near.Render.Proof.RcptTr2 — reading the extracted receipts off the honest rows

The cells of a field row of the extracted receipt `i` are those of the honest
record (`cell_f`, `cv_f`); a column over a field reads the honest values
(`colAt_f`); the extracted receipt parameters are the honest ones (`rs_eq`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace RcptP

open RcptGen RcptProof

theorem RL_lt_height (c : Claim) (e : Ext) : (RL c e).length < (render c e).height T_RCPT := by
  rw [rcpt_height]; have := le_pow_logOf ((RL c e).length + 1); omega

theorem colAt_eq {tr : Trace Fp} {r0 len x : Nat} {L : List Nat} (hlen : L.length = len)
    (h : ∀ k, k < len → cv tr T_RCPT (r0 + k) x = L.getD k 0) : colAt tr r0 len x = L := by
  apply List.ext_getElem
  · rw [colAt_len, hlen]
  · intro k h1 h2
    rw [colAt_len] at h1
    have := h k h1
    simp only [colAt, List.getElem_map, List.getElem_range]
    rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

theorem tn_lt (b : Bytes) (k : Nat) : (toNats b).getD k 0 < 256 := by
  simp only [toNats, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases b[k]? with
  | none => simp
  | some y => exact y.toNat_lt

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e) (hL : TableLocal Rcpt.table (render c.1 e) T_RCPT (publicOf c))
  {rcs : List RS} (S : Shape (render c.1 e) rcs)
include hg hL S

theorem cell_f {i : Nat} (hi : i < rcs.length) {f o L : Nat}
    (hf : (f, o, L) ∈ plan rcs[i].h rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt) {k : Nat} (hk : k < L) (col : Nat) :
    (render c.1 e).cell T_RCPT (rcs[i].s + o + k) col = Fp.ofNat (Cc c.1 e (.seg i f k) col) := by
  obtain ⟨h, he⟩ := rec_at hg hL S hi hf hk
  have := RL_lt_height c.1 e
  rw [cell_q hg (by omega), dif_pos h, he]; rfl

theorem cv_f {i : Nat} (hi : i < rcs.length) {f o L : Nat}
    (hf : (f, o, L) ∈ plan rcs[i].h rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt) {k : Nat} (hk : k < L) {col : Nat}
    (hv : Cc c.1 e (.seg i f k) col < Render.P) :
    cv (render c.1 e) T_RCPT (rcs[i].s + o + k) col = Cc c.1 e (.seg i f k) col := by
  simp only [cv]; rw [cell_f hg hL S hi hf hk, ofNat_lt_eq hv]

theorem colAt_f {i : Nat} (hi : i < rcs.length) {f o L : Nat}
    (hf : (f, o, L) ∈ plan rcs[i].h rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt) {col : Nat} {Lst : List Nat}
    (hlen : Lst.length = L) (hv : ∀ k, k < L → Cc c.1 e (.seg i f k) col = Lst.getD k 0)
    (hb : ∀ k, k < L → Lst.getD k 0 < Render.P) :
    colAt (render c.1 e) (rcs[i].s + o) L col = Lst :=
  colAt_eq hlen (fun k hk => by rw [cv_f hg hL S hi hf hk (by rw [hv k hk]; exact hb k hk), hv k hk])

theorem pl_mem {i : Nat} (hi : i < rcs.length) : (Rcpt.sPL, 0, 4) ∈ plan rcs[i].h rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt := by
  cases rcs[i].h <;> simp [plan]

/-- The cells of the receipt's first row. -/
theorem cell_s {i : Nat} (hi : i < rcs.length) (col : Nat) :
    (render c.1 e).cell T_RCPT rcs[i].s col = Fp.ofNat (Cc c.1 e (.seg i 5 0) col) := by
  have := cell_f hg hL S hi (pl_mem hg hL S hi) (k := 0) (by decide) col
  simpa [Rcpt.sPL] using this

theorem i_lt {i : Nat} (hi : i < rcs.length) : i < NN e := by
  obtain ⟨h, he⟩ := rec_at hg hL S hi (pl_mem hg hL S hi) (k := 0) (by decide)
  have := RL_ok hg _ (List.getElem_mem h)
  rw [he] at this; exact this.1

/-- **The extracted receipt parameters are the honest ones.** -/
theorem rs_eq {i : Nat} (hi : i < rcs.length) :
    rcs[i].h = (Df c.1 e i).hr ∧ rcs[i].Lp = (Df c.1 e i).pred.length ∧ rcs[i].Lv = (Df c.1 e i).recv.length ∧
      rcs[i].Ls = (Df c.1 e i).signer.length ∧ rcs[i].kt = (Df c.1 e i).kt := by
  have lay := S.lay _ (List.getElem_mem hi)
  have hiN := i_lt hg hL S hi
  have hfin := lay.fin
  have hH := height_ltP hg
  have hb : ∀ x y : Nat, x < Render.P → y < Render.P → Fp.ofNat x = (y : Fp) → x = y :=
    fun x y hx hy h => ofNat_inj hx hy (by rw [h]; rfl)
  have l1 := (pred_ok hg hiN).len; have l2 := (recv_ok hg hiN).len; have l3 := (signer_ok hg hiN).len
  have l4 := d_kt hg hiN
  have P3 := P_3M
  unfold total Vt at hfin
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := lay.hr; rw [cell_s hg hL S hi, S_hr] at this
    cases h1 : rcs[i].h <;> cases h2 : (Df c.1 e i).hr <;> simp only [h1, h2, b2n_true, b2n_false] at this ⊢ <;>
      first | rfl | exact absurd this (by decide)
  · have := lay.cLp; rw [cell_s hg hL S hi, S_Lp] at this
    exact (hb _ _ (by omega) (by split at hfin <;> omega) this).symm
  · have := lay.cLv; rw [cell_s hg hL S hi, S_Lv] at this
    exact (hb _ _ (by omega) (by split at hfin <;> omega) this).symm
  · have := lay.cLs; rw [cell_s hg hL S hi, S_Ls] at this
    exact (hb _ _ (by omega) (by split at hfin <;> omega) this).symm
  · have := lay.ckt; rw [cell_s hg hL S hi, S_kt] at this
    exact (hb _ _ (by omega) (by split at hfin <;> omega) this).symm

end

end RcptP

end ZkFormal.Near.Render
