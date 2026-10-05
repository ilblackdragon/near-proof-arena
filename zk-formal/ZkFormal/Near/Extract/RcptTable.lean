import ZkFormal.Near.Extract.RcptLayout

/-!
# ZkFormal.Near.Extract.RcptTable — rows of the `rcpt` table

Rows `0 … 11`: the claim field; then consecutive receipts (`Layout` each),
starting at row `12`; then inactive rows.  The receipt counter `r` counts the
receipts, and `o`, `o2`, `rcnt` chain from receipt to receipt.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

/-- Shape of one receipt: first row and field sizes. -/
structure RS where
  s : Nat
  h : Bool
  Lp : Nat
  Lv : Nat
  Ls : Nat
  kt : Nat
  deriving Inhabited

def RS.tot (x : RS) : Nat := total x.h x.Lp x.Lv x.Ls x.kt

def segsOf (rcs : List RS) : List (Nat × Nat) := rcs.map fun x => (x.s, x.tot)

theorem total_pos (h : Bool) (Lp Lv Ls kt : Nat) : 176 ≤ total h Lp Lv Ls kt := by
  unfold total; split <;> omega

theorem oEndC : oEnd ∈ rconsts := by simp [rconsts]
theorem o2EndC : o2End ∈ rconsts := by simp [rconsts]
theorem rC : Rcpt.r ∈ rconsts := by simp [rconsts]
theorem oC : o ∈ rconsts := by simp [rconsts]
theorem o2C : o2 ∈ rconsts := by simp [rconsts]
theorem rcntC : rcnt ∈ rconsts := by simp [rconsts]

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

/-- The last row of a receipt. -/
theorem lay_last {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt) :
    tr.cell T_RCPT (s + total h Lp Lv Ls kt - 1) act = 1 ∧
    ∀ x ∈ rconsts, tr.cell T_RCPT (s + total h Lp Lv Ls kt - 1) x = tr.cell T_RCPT s x := by
  have hlast : ∃ X L o, (X, o, L) ∈ plan h Lp Lv Ls kt ∧ o + L = total h Lp Lv Ls kt := by
    cases h
    · exact ⟨sXLH, 32, 144 + 32 * hN false + Vt Lp Lv Ls kt, by simp [plan], by simp [total, hN]; omega⟩
    · exact ⟨sXRZ, 16, 234 + Vt Lp Lv Ls kt, by simp [plan], by simp [total]; omega⟩
  obtain ⟨X, L, o, hm, he⟩ := hlast
  have F : RFld tr s (s + o) L X := lay.flds _ hm
  have hp := F.fld.pos
  have e : s + total h Lp Lv Ls kt - 1 = s + o + (L - 1) := by omega
  rw [e]
  exact ⟨F.fld.act (L - 1) (by omega), fun x hx => F.consts (L - 1) (by omega) x hx⟩

/-- Receipts from row `s` on. -/
theorem rcpts_from : ∀ fuel s t : Nat, tr.height T_RCPT - s ≤ fuel → s < tr.height T_RCPT →
    tr.cell T_RCPT s rf = 1 → tr.cell T_RCPT s Rcpt.r = (t : Fp) →
    ∃ rcs : List RS, rcs ≠ [] ∧ Consec s (segsOf rcs) ∧
      (∀ x ∈ rcs, Layout tr x.s x.h x.Lp x.Lv x.Ls x.kt) ∧
      (∀ i (hi : i < rcs.length), tr.cell T_RCPT rcs[i].s Rcpt.r = ((t + i : Nat) : Fp)) ∧
      (∀ i (hi : i + 1 < rcs.length),
        tr.cell T_RCPT rcs[i + 1].s o = tr.cell T_RCPT rcs[i].s oEnd ∧
        tr.cell T_RCPT rcs[i + 1].s o2 = tr.cell T_RCPT rcs[i].s o2End ∧
        tr.cell T_RCPT rcs[i + 1].s rcnt = tr.cell T_RCPT rcs[i].s rcnt + tr.cell T_RCPT rcs[i].s Rcpt.hr) ∧
      segEnd s (segsOf rcs) < tr.height T_RCPT ∧
      (∀ q, segEnd s (segsOf rcs) ≤ q → q < tr.height T_RCPT → tr.cell T_RCPT q act = 0) := by
  intro fuel
  induction fuel with
  | zero => intro s t h1 h2; omega
  | succ f ih =>
    intro s t hf hs hrf hrt
    obtain ⟨h, Lp, Lv, Ls, kt, lay⟩ := layout_of hL hs hrf
    have hT := total_pos h Lp Lv Ls kt
    have hfin := lay.fin
    obtain ⟨hla, hlc⟩ := lay_last hL lay
    have hrl0 := lay.endRl
    generalize hE : s + total h Lp Lv Ls kt = E at *
    have hE1 : E - 1 + 1 = E := by omega
    rcases isBool hL (r := E) (by omega) (x := act) (by simp [boolCols]) with ha | ha
    · -- no further receipt
      refine ⟨[⟨s, h, Lp, Lv, Ls, kt⟩], by simp, ⟨rfl, trivial⟩, by simpa using lay, fun i hi => ?_,
        fun i hi => by simp at hi, by simp [segsOf, segEnd, RS.tot]; omega, fun q h1 h2 => ?_⟩
      · simp at hi; subst hi; simpa using hrt
      · simp only [segsOf, List.map_cons, List.map_nil, segEnd, RS.tot] at h1
        have : ∀ d, E + d < tr.height T_RCPT → tr.cell T_RCPT (E + d) act = 0 := by
          intro d; induction d with
          | zero => intro _; simpa using ha
          | succ d ihd => intro hd; rw [← Nat.add_assoc]; exact pad hL hd (ihd (by omega))
        rw [hE] at h1
        have := this (q - E) (by omega); rwa [Nat.add_sub_cancel' h1] at this
    · -- the next receipt
      have hrl : tr.cell T_RCPT (E - 1) rl = 1 := hrl0
      have nr := nextRcpt hL (r := E - 1) (by omega) hrl (by rw [hE1]; exact ha)
      rw [hE1] at nr
      obtain ⟨rcs, hne, hc, hlay, hr', hchain, hend, hpad⟩ := ih E (t + 1) (by omega) hfin nr.1
        (by rw [nr.2.1, hlc _ rC, hrt, natCast_add]; rfl)
      refine ⟨⟨s, h, Lp, Lv, Ls, kt⟩ :: rcs, by simp, ⟨rfl, by simpa [segsOf, RS.tot, hE] using hc⟩, ?_,
        fun i hi => ?_, fun i hi => ?_, by simpa [segsOf, segEnd, RS.tot, hE] using hend,
        fun q h1 h2 => hpad q (by simpa [segsOf, segEnd, RS.tot, hE] using h1) h2⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact lay
        · exact hlay x hx
      · cases i with
        | zero => simpa using hrt
        | succ i =>
          have := hr' i (by simpa using hi)
          simp only [List.getElem_cons_succ]; rw [this]; congr 1; omega
      · cases i with
        | zero =>
          have h0 : ∀ hh : 0 < rcs.length, (rcs[0]'hh).s = E := by
            intro hh
            obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
            exact hc.1
          simp only [List.getElem_cons_succ, List.getElem_cons_zero, h0]
          refine ⟨by rw [nr.2.2.1, hlc _ oEndC], by rw [nr.2.2.2.1, hlc _ o2EndC], ?_⟩
          rw [nr.2.2.2.2, hlc _ rcntC, hlc _ hrC]
        | succ i => simpa using hchain i (by simpa using hi)

/-- The claim rows and the first receipt. -/
theorem claim_block : 13 < tr.height T_RCPT ∧ Fld tr 0 12 sCL ∧ tr.cell T_RCPT 12 rf = 1 ∧
    tr.cell T_RCPT 12 Rcpt.r = 0 ∧ tr.cell T_RCPT 12 o = 12 ∧ tr.cell T_RCPT 12 o2 = 4 ∧
    tr.cell T_RCPT 12 rcnt = 0 := by
  have h0 : 0 < tr.height T_RCPT := by have := height_ge hL; omega
  obtain ⟨hc, hfs, hi, -⟩ := row0 hL h0
  obtain ⟨L, hLH, F⟩ := fld_from hL h0 (X := sCL) (by simp [states]) hc hi hfs
  have e := fld_len_k hL (by omega) F (m := 11) (by simp [lastIdx]) (by decide)
  subst e
  have hrl : tr.cell T_RCPT 11 rl = 0 := by
    have := rl_at hL (r := 11) (by omega) (x := sCL) (by simp [states]) (F.st 11 (by omega))
    rw [this, if_neg (by decide), if_neg (by decide)]; grind
  obtain ⟨h1, s1, i1, f1⟩ := fld_next hL (by omega) F hrl (X' := sPL) (g := k 1) (by simp [Rcpt.succ]) rfl
  have he : tr.cell T_RCPT 11 fe = 1 := by rw [F.fe 11 (by omega), if_pos rfl]
  have fr := firstRcpt hL (r := 11) (by omega) he (F.st 11 (by omega))
  have hrf := (bounds hL (r := 12) (by omega)).2.2.1 s1 f1
  have hlay := layout_of hL (s := 12) (by omega) hrf
  obtain ⟨h', Lp, Lv, Ls, kt, lay⟩ := hlay
  have := lay.fin; have := total_pos h' Lp Lv Ls kt
  exact ⟨by omega, F, hrf, fr⟩

/-- **The rows of the table.** -/
theorem table_of : 13 < tr.height T_RCPT ∧ Fld tr 0 12 sCL ∧
    ∃ rcs : List RS, rcs ≠ [] ∧ Consec 12 (segsOf rcs) ∧
      (∀ x ∈ rcs, Layout tr x.s x.h x.Lp x.Lv x.Ls x.kt) ∧
      (∀ i (hi : i < rcs.length), tr.cell T_RCPT rcs[i].s Rcpt.r = ((i : Nat) : Fp)) ∧
      tr.cell T_RCPT 12 o = 12 ∧ tr.cell T_RCPT 12 o2 = 4 ∧ tr.cell T_RCPT 12 rcnt = 0 ∧
      (∀ i (hi : i + 1 < rcs.length),
        tr.cell T_RCPT rcs[i + 1].s o = tr.cell T_RCPT rcs[i].s oEnd ∧
        tr.cell T_RCPT rcs[i + 1].s o2 = tr.cell T_RCPT rcs[i].s o2End ∧
        tr.cell T_RCPT rcs[i + 1].s rcnt = tr.cell T_RCPT rcs[i].s rcnt + tr.cell T_RCPT rcs[i].s Rcpt.hr) ∧
      segEnd 12 (segsOf rcs) < tr.height T_RCPT ∧
      (∀ q, segEnd 12 (segsOf rcs) ≤ q → q < tr.height T_RCPT → tr.cell T_RCPT q act = 0) := by
  obtain ⟨h13, F, hrf, hr0, ho, ho2, hrc⟩ := claim_block hL
  obtain ⟨rcs, hne, hc, hlay, hr, hch, hend, hpad⟩ :=
    rcpts_from hL _ 12 0 (Nat.le_refl _) (by omega) hrf (by rw [hr0]; rfl)
  exact ⟨h13, F, rcs, hne, hc, hlay, fun i hi => by simpa using hr i hi, ho, ho2, hrc, hch, hend, hpad⟩

end ZkFormal.Near.RcptProof
