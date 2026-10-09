import ZkFormal.NearV3.Assembly.RcptCandidateLayout
import ZkFormal.NearV3.Rcpt.Extract.V.Table
-- Source Table.lean SHA256: b31024ea10ea3acb210647c6c5c130283921445d774c27e47324990ddef5b6cf.
-- Reuses original data types and migrates only table-local proofs.
namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- The last row of a receipt. -/
theorem lay_last {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt) :
    tr.cell tt (s + total h Lp Lv Ls kt - 1) act = 1 ∧
    ∀ x ∈ rconsts, tr.cell tt (s + total h Lp Lv Ls kt - 1) x = tr.cell tt s x := by
  have hlast : ∃ X L o, (X, o, L) ∈ plan h Lp Lv Ls kt ∧ o + L = total h Lp Lv Ls kt := by
    cases h
    · exact ⟨sXLH, 32, 144 + 32 * hN false + Vt Lp Lv Ls kt, by simp [plan], by simp [total, hN]; omega⟩
    · exact ⟨sXRZ, 16, 234 + Vt Lp Lv Ls kt, by simp [plan], by simp [total]; omega⟩
  obtain ⟨X, L, o, hm, he⟩ := hlast
  have F : RFld tr tt s (s + o) L X := lay.flds _ hm
  have hp := F.fld.pos
  have e : s + total h Lp Lv Ls kt - 1 = s + o + (L - 1) := by omega
  rw [e]
  exact ⟨F.fld.act (L - 1) (by omega), fun x hx => F.consts (L - 1) (by omega) x hx⟩

/-- A receipt's last row is not a header row. -/
theorem lay_last_ncl {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt) :
    tr.cell tt (s + total h Lp Lv Ls kt - 1) sCL = 0 := by
  have := lay.endRl
  have hq : s + total h Lp Lv Ls kt - 1 < tr.height tt := by have := lay.fin; omega
  rcases states_bool hL hq sCL (by simp [states]) with hc | hc
  · exact hc
  · have oh := (oneHot hL hq (by simp [states]) hc).2
    have hb := (bounds hL hq).1
    rw [oh sXRZ (by simp [states]) (by decide), oh sXLH (by simp [states]) (by decide), this] at hb
    exact absurd (by grind : (1 : Fp) = 0) (fun h => fp_zero_ne_one h.symm)

/-- After a row with `brk = 1`: padding, a receipt, or a header (its first row). -/
theorem after_brk {E : Nat} (hE : E < tr.height tt) (hE0 : 0 < E)
    (hb : tr.cell tt (E - 1) rl + tr.cell tt (E - 1) sCL * tr.cell tt (E - 1) fe = 1)
    (hfe : tr.cell tt (E - 1) fe = 1) :
    tr.cell tt E act = 0 ∨ (tr.cell tt E act = 1 ∧ tr.cell tt E rf = 1) ∨
      (tr.cell tt E act = 1 ∧ tr.cell tt E rf = 0 ∧ tr.cell tt E sCL = 1 ∧ tr.cell tt E fs = 1 ∧
        tr.cell tt E idx = 0) := by
  have hq : E - 1 + 1 < tr.height tt := by omega
  rw [show E - 1 + 1 = E by omega] at hq
  rcases isBool hL (r := E) hE (x := act) (by simp [boolCols]) with ha | ha
  · exact Or.inl ha
  · have hn := brkNext hL (r := E - 1) (by omega) hb (by rw [show E - 1 + 1 = E by omega]; exact ha)
    have hf := afterField hL (r := E - 1) (by omega) hfe (by rw [show E - 1 + 1 = E by omega]; exact ha)
    rw [show E - 1 + 1 = E by omega] at hn hf
    rcases states_bool hL hE sPL (by simp [states]) with hp | hp
    · rw [hp] at hn
      have hc : tr.cell tt E sCL = 1 := by grind
      have hrf : tr.cell tt E rf = 0 := by
        rcases isBool hL (r := E) hE (x := rf) (by simp [boolCols]) with h | h
        · exact h
        · rw [((bounds hL hE).2.1 h).1] at hp; exact absurd hp (fun h => fp_zero_ne_one h.symm)
      exact Or.inr (Or.inr ⟨ha, hrf, hc, hf.2, hf.1⟩)
    · exact Or.inr (Or.inl ⟨ha, (bounds hL hE).2.2.1 hp hf.2⟩)

/-- **Receipts of one list, from row `s`** (`r = t`, `cj = c` at `s`). -/
theorem rcpts_from : ∀ fuel s t c : Nat, tr.height tt - s ≤ fuel → s < tr.height tt →
    tr.cell tt s rf = 1 → tr.cell tt s RcptV3.r = (t : Fp) → tr.cell tt s cj = (c : Fp) →
    ∃ rcs : List RS, rcs ≠ [] ∧ Consec s (segsOf rcs) ∧
      (∀ x ∈ rcs, Layout tr tt x.s x.h x.Lp x.Lv x.Ls x.kt) ∧
      (∀ i (hi : i < rcs.length), tr.cell tt rcs[i].s RcptV3.r = ((t + i : Nat) : Fp) ∧
        tr.cell tt rcs[i].s cj = ((c + i : Nat) : Fp)) ∧
      (∀ i (hi : i + 1 < rcs.length),
        tr.cell tt rcs[i + 1].s o = tr.cell tt rcs[i].s oEnd ∧
        tr.cell tt rcs[i + 1].s o2 = tr.cell tt rcs[i].s o2End) ∧
      BlockEnd tr tt (segEnd s (segsOf rcs)) := by
  intro fuel
  induction fuel with
  | zero => intro s t c h1 h2; omega
  | succ f ih =>
    intro s t c hf hs hrf hrt hcj
    obtain ⟨h, Lp, Lv, Ls, kt, lay⟩ := layout_of hL hs hrf
    have hT := total_pos h Lp Lv Ls kt
    have hfin := lay.fin
    obtain ⟨hla, hlc⟩ := lay_last hL lay
    have hrl0 := lay.endRl
    have hncl := lay_last_ncl hL lay
    generalize hE : s + total h Lp Lv Ls kt = E at *
    have hE1 : E - 1 + 1 = E := by omega
    have hfe : tr.cell tt (E - 1) fe = 1 := by
      have := (bounds hL (r := E - 1) (by omega)).1
      rw [hrl0] at this
      rcases isBool hL (r := E - 1) (by omega) (x := fe) (by simp [boolCols]) with h' | h'
      · rw [h'] at this; exact absurd this (by grind)
      · exact h'
    have hb : tr.cell tt (E - 1) rl + tr.cell tt (E - 1) sCL * tr.cell tt (E - 1) fe = 1 := by
      rw [hrl0, hncl]; grind
    rcases after_brk hL (E := E) hfin (by omega) hb hfe with ha | ⟨ha, hrf'⟩ | ⟨ha, -, hc, hfs, hi⟩
    · -- padding: the list ends
      refine ⟨[⟨s, h, Lp, Lv, Ls, kt⟩], by simp, ⟨rfl, trivial⟩, by simpa using lay, fun i hi => ?_,
        fun i hi => by simp at hi, ?_⟩
      · simp at hi; subst hi; exact ⟨by simpa using hrt, by simpa using hcj⟩
      · simp only [segsOf, List.map_cons, List.map_nil, segEnd, RS.tot]; rw [hE]; exact ⟨hfin, Or.inl ha⟩
    · -- the next receipt of the list
      have st := brkStep hL (r := E - 1) (by omega) hb (by rw [hE1]; exact ha)
      rw [hE1] at st
      obtain ⟨rcs, hne, hcs, hlay, hr', hchain, hend⟩ := ih E (t + 1) (c + 1) (by omega) hfin hrf'
        (by rw [st.1, hlc _ rC, hrt, hrl0, natCast_add]; rfl)
        (by rw [(st.2.1 hrf').1, hlc _ cjC, hcj, natCast_add]; rfl)
      refine ⟨⟨s, h, Lp, Lv, Ls, kt⟩ :: rcs, by simp, ⟨rfl, by simpa [segsOf, RS.tot, hE] using hcs⟩, ?_,
        fun i hi => ?_, fun i hi => ?_, by simpa [segsOf, segEnd, RS.tot, hE] using hend⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact lay
        · exact hlay x hx
      · cases i with
        | zero => exact ⟨by simpa using hrt, by simpa using hcj⟩
        | succ i =>
          obtain ⟨a1, a2⟩ := hr' i (by simpa using hi)
          simp only [List.getElem_cons_succ]
          rw [a1, a2]; exact ⟨by congr 1; omega, by congr 1; omega⟩
      · cases i with
        | zero =>
          have h0 : ∀ hh : 0 < rcs.length, (rcs[0]'hh).s = E := by
            intro hh
            obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
            exact hcs.1
          simp only [List.getElem_cons_succ, List.getElem_cons_zero, h0]
          exact ⟨by rw [(st.2.1 hrf').2, hlc _ oEndC], by rw [st.2.2, hlc _ o2EndC]⟩
        | succ i => simpa using hchain i (by simpa using hi)
    · -- a header: the list ends
      refine ⟨[⟨s, h, Lp, Lv, Ls, kt⟩], by simp, ⟨rfl, trivial⟩, by simpa using lay, fun i hi => ?_,
        fun i hi => by simp at hi, ?_⟩
      · simp at hi; subst hi; exact ⟨by simpa using hrt, by simpa using hcj⟩
      · simp only [segsOf, List.map_cons, List.map_nil, segEnd, RS.tot]; rw [hE]
        exact ⟨hfin, Or.inr ⟨hc, hfs, hi⟩⟩

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
