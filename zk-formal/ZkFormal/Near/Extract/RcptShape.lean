import ZkFormal.Near.Extract.RcptClaim

/-!
# ZkFormal.Near.Extract.RcptShape — the table's receipts and their running offsets

`Shape tr rcs`: the rows of the table (claim rows, the receipts `rcs`,
padding); `offs`: the receipt counter, the `RC`/`RF` offsets and the refund
count of receipt `i` are those of the view `rs = rcs.map (rcptOf tr)`.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

/-- Rows of a legal table. -/
structure Shape (tr : Trace Fp) (rcs : List RS) : Prop where
  h13 : 13 < tr.height T_RCPT
  claim : Fld tr 0 12 sCL
  ne : rcs ≠ []
  consec : Consec 12 (segsOf rcs)
  lay : ∀ x ∈ rcs, Layout tr x.s x.h x.Lp x.Lv x.Ls x.kt
  r : ∀ i (hi : i < rcs.length), tr.cell T_RCPT rcs[i].s Rcpt.r = ((i : Nat) : Fp)
  o0 : tr.cell T_RCPT 12 o = 12
  o20 : tr.cell T_RCPT 12 o2 = 4
  rcnt0 : tr.cell T_RCPT 12 rcnt = 0
  chain : ∀ i (hi : i + 1 < rcs.length),
    tr.cell T_RCPT rcs[i + 1].s o = tr.cell T_RCPT rcs[i].s oEnd ∧
    tr.cell T_RCPT rcs[i + 1].s o2 = tr.cell T_RCPT rcs[i].s o2End ∧
    tr.cell T_RCPT rcs[i + 1].s rcnt = tr.cell T_RCPT rcs[i].s rcnt + tr.cell T_RCPT rcs[i].s Rcpt.hr
  fin : segEnd 12 (segsOf rcs) < tr.height T_RCPT
  pad : ∀ q, segEnd 12 (segsOf rcs) ≤ q → q < tr.height T_RCPT → tr.cell T_RCPT q act = 0

theorem shape_of (hL : TableLocal Rcpt.table tr T_RCPT pub) : ∃ rcs, Shape tr rcs := by
  obtain ⟨h13, F, rcs, hne, hc, hlay, hr, ho, ho2, hrc, hch, hend, hpad⟩ := table_of hL
  exact ⟨rcs, h13, F, hne, hc, hlay, hr, ho, ho2, hrc, hch, hend, hpad⟩

/-- The view of the table. -/
def viewOf (tr : Trace Fp) (rcs : List RS) : RcptVs := rcs.map (rcptOf tr)

theorem enc_len (tr : Trace Fp) (y : RS) : (rcptOf tr y).enc.length = 123 + Vt y.Lp y.Lv y.Ls y.kt := by
  simp [RcptV.enc, RcptV.borshN, rcptOf, colAt_len, u32r, tailN, Vt]; omega

theorem encRefund_len (tr : Trace Fp) (y : RS) :
    (rcptOf tr y).encRefund.length = 129 + 2 * y.Ls + 32 * y.kt := by
  cases hh : y.h <;> simp [RcptV.encRefund, RcptV.borshN, rcptOf, colAt_len, u32r, tailN, systemN, hh] <;> omega

section
variable {rcs : List RS} (S : Shape tr rcs)
include S

theorem s_get (i : Nat) (hi : i < rcs.length) :
    rcs[i].s = segEnd 12 ((segsOf rcs).take i) := by
  have hc := S.consec
  induction i with
  | zero =>
    obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil S.ne
    simp [segsOf] at hc ⊢; simp [segEnd]; exact hc.1
  | succ i ih =>
    have := consec_get _ 12 hc i (by simpa [segsOf] using hi)
    simp only [segsOf, List.getElem_map] at this
    rw [this, ih (by omega)]
    have gen : ∀ (l : List (Nat × Nat)) (s0 k : Nat) (hk : k < l.length), Consec s0 l →
        segEnd s0 (l.take (k + 1)) = segEnd s0 (l.take k) + l[k].2 := by
      intro l; induction l with
      | nil => intro s0 k hk; simp at hk
      | cons p rest ihl =>
        intro s0 k hk hcc
        obtain ⟨rfl, hcc⟩ := hcc
        cases k with
        | zero => simp [segEnd]
        | succ k => simp only [List.take_succ_cons, segEnd]; exact ihl _ k (by simpa using hk) hcc
    rw [gen (segsOf rcs) 12 i (by simp [segsOf]; omega) hc]
    simp [segsOf, RS.tot]

theorem s_succ (i : Nat) (hi : i + 1 < rcs.length) : rcs[i + 1].s = rcs[i].s + rcs[i].tot := by
  have := consec_get _ 12 S.consec i (by simpa [segsOf] using hi)
  simpa [segsOf] using this

theorem s_end (i : Nat) (hi : i < rcs.length) : rcs[i].s + rcs[i].tot ≤ segEnd 12 (segsOf rcs) := by
  have := seg_le_end (segsOf rcs) 12 S.consec (rcs[i].s, rcs[i].tot) (List.mem_map.mpr ⟨rcs[i], List.getElem_mem _, rfl⟩)
  exact this.2

theorem s_last : (rcs[rcs.length - 1]'(by have := S.ne; cases rcs <;> simp_all)).s +
    (rcs[rcs.length - 1]'(by have := S.ne; cases rcs <;> simp_all)).tot = segEnd 12 (segsOf rcs) := by
  have hp : 0 < (segsOf rcs).length := by have := S.ne; cases rcs <;> simp_all [segsOf]
  rw [segEnd_last _ 12 S.consec hp]
  simp [segsOf]

theorem s_ge (i : Nat) (hi : i < rcs.length) : 12 ≤ rcs[i].s := by
  have := seg_le_end (segsOf rcs) 12 S.consec (rcs[i].s, rcs[i].tot) (List.mem_map.mpr ⟨rcs[i], List.getElem_mem _, rfl⟩)
  exact this.1

/-- Is there a receipt after receipt `i`: the row after it is active. -/
theorem act_after (hL : TableLocal Rcpt.table tr T_RCPT pub) (i : Nat) (hi : i < rcs.length) :
    tr.cell T_RCPT (rcs[i].s + rcs[i].tot) act = if i + 1 < rcs.length then 1 else 0 := by
  split
  · rename_i h1
    rw [← s_succ S i h1]
    have lay := S.lay rcs[i + 1] (List.getElem_mem h1)
    have F := (lay.flds (sPL, 0, 4) (by simp [plan])).fld
    simpa using F.act 0 (by show 0 < 4; omega)
  · rename_i h1
    have : i = rcs.length - 1 := by omega
    subst this
    have hl := s_last S
    exact S.pad _ (by rw [hl]; exact Nat.le_refl _) (by rw [hl]; exact S.fin)

end

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem viewOf_get (tr : Trace Fp) (rcs : List RS) (i : Nat) (hi : i < rcs.length) :
    (viewOf tr rcs).getD i default = rcptOf tr rcs[i] := by
  simp [viewOf, List.getD_eq_getElem?_getD, hi]

theorem viewOf_len (tr : Trace Fp) (rcs : List RS) : (viewOf tr rcs).length = rcs.length := by simp [viewOf]

theorem lay_row0 (hL : TableLocal Rcpt.table tr T_RCPT pub) {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat}
    (lay : Layout tr s h Lp Lv Ls kt) :
    tr.cell T_RCPT s act = 1 ∧ tr.cell T_RCPT s sCL = 0 ∧ tr.cell T_RCPT s sPL = 1 ∧ tr.cell T_RCPT s rf = 1 := by
  have F := (lay.flds (sPL, 0, 4) (by simp [plan])).fld
  have h1 : tr.cell T_RCPT s sPL = 1 := by simpa using F.st 0 (by show 0 < 4; omega)
  have hfs : tr.cell T_RCPT s fs = 1 := by simpa using F.fs 0 (by show 0 < 4; omega)
  have hs : s < tr.height T_RCPT := by have := lay.fin; have := total_pos h Lp Lv Ls kt; omega
  have oh := oneHot hL hs (by simp [states]) h1
  exact ⟨oh.1, oh.2 sCL (by simp [states]) (by decide), h1, (bounds hL hs).2.2.1 h1 hfs⟩

theorem offs (hL : TableLocal Rcpt.table tr T_RCPT pub) {rcs : List RS} (S : Shape tr rcs) :
    ∀ i (hi : i < rcs.length), tr.cell T_RCPT rcs[i].s o = (rcOffs (viewOf tr rcs) i : Fp) ∧
      tr.cell T_RCPT rcs[i].s o2 = (rfOffs (viewOf tr rcs) i : Fp) := by
  intro i
  induction i with
  | zero =>
    intro hi
    have h0 : rcs[0].s = 12 := by rw [s_get S 0 hi]; rfl
    rw [h0, S.o0, S.o20]; exact ⟨rfl, rfl⟩
  | succ i ih =>
    intro hi
    obtain ⟨i1, i2⟩ := ih (by omega)
    obtain ⟨c1, c2, -⟩ := S.chain i hi
    have lay := S.lay rcs[i] (List.getElem_mem (by omega))
    obtain ⟨ha, hc, -, -⟩ := lay_row0 hL lay
    have hs : rcs[i].s < tr.height T_RCPT := by have := lay.fin; have := total_pos rcs[i].h rcs[i].Lp rcs[i].Lv rcs[i].Ls rcs[i].kt; omega
    obtain ⟨z1, z2⟩ := sizes hL hs ha hc
    rw [c1, c2, z1, z2, i1, i2, lay.cLp, lay.cLv, lay.cLs, lay.ckt, lay.hr]
    simp only [rcOffs, rfOffs, viewOf_get tr rcs i (by omega), enc_len, encRefund_len, rcptOf_hr, Vt]
    constructor
    · simp only [natCast_add, natCast_mul]; grind
    · cases rcs[i].h <;> simp [natCast_add, natCast_mul] <;> grind

end ZkFormal.Near.RcptProof
