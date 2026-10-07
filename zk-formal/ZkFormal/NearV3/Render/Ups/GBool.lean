import ZkFormal.NearV3.Render.Ups.GWalk

/-!
# ZkFormal.NearV3.Render.Ups.GBool — `cBool` on the honest table

Every boolean cell of the generator is an indicator (`ind`), a bit of a natural number
(`n / 2^i % 2`), or a bit field of the part description (`InstOk.bits`: `qodd`, `nochild`,
`neg`, `podd`); the drain flag `wk − mS − mK − mB` is the indicator of mode `3`.  Each block
of `cBool` (row, segment, part flags; `reg` bits on `TAG`/`HPF`, `MEM`, `W1`/`W2` rows; walk
flags) is checked cell by cell (`*_bits`), gates off elsewhere.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Algebra ZkFormal.Air ZkFormal.Near.Render.EvI
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

namespace UpsGen

/-- A value that is a bit. -/
def B01 (v : Int) : Prop := v = 0 ∨ v = 1

theorem b01_ind (p : Prop) [Decidable p] : B01 (ind p) := ind01 p
theorem b01_0 : B01 0 := .inl rfl
theorem b01_1 : B01 1 := .inr rfl
theorem b01_nat {n : Nat} (h : n ≤ 1) : B01 (n : Int) := by unfold B01; omega
theorem b01_mod (a : Int) : B01 (a % 2) := by unfold B01; omega
theorem b01_natmod (a : Nat) : B01 ((a % 2 : Nat) : Int) := by unfold B01; omega

theorem ev_bool {C D P : Nat → Int} {fst lst trn : Int} {x : Nat} (h : B01 (C x)) :
    ((ev C D fst lst trn P (Dsl.bool (c x)) : Int) : Fp) = 0 := by
  apply cast0; simp only [ev, Dsl.bool, Dsl.c, Dsl.sub, Dsl.k, Bool.false_eq_true, ite_false]
  rcases h with h | h <;> rw [h] <;> rfl

theorem ev_gbool {C D P : Nat → Int} {fst lst trn : Int} {g : Expr} {x : Nat}
    (h : ev C D fst lst trn P g = 0 ∨ B01 (C x)) :
    ((ev C D fst lst trn P (.mul g (Dsl.bool (c x))) : Int) : Fp) = 0 := by
  apply cast0; simp only [ev, Dsl.bool, Dsl.c, Dsl.sub, Dsl.k, Bool.false_eq_true, ite_false]
  rcases h with h | h | h <;> rw [h] <;> simp

/-! ## Cells that are bits -/

/-- Unfold the derived flags of a node row to indicators. -/
macro "bsimp" : tactic => `(tactic| simp only [fwV, lastwV, wfrV, tgtV, wyV, wnV, cpV, rdcV, extraV, rdV, aftV, gDV,
  winFrV, kin, cin, xcpV, useAV, bNV, bLV, cOV, cSV, eLV, eSV, vcpV, spY1V, spY2V, upV, nokeyV, spRecv, presV, xbit,
  List.map, List.sum_cons, List.sum_nil, XcpB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq])

/-- Close `B01 v` for an indicator expression. -/
macro "bclose" : tactic => `(tactic| first
  | exact b01_0 | exact b01_1 | exact b01_ind _ | exact b01_natmod _ | exact b01_mod _
  | (unfold B01; simp only [ind]; (repeat' split) <;> omega))

theorem seg_bits (I : UpsInst) : ∀ x ∈ UpsV3.segBools, B01 (segCell I x) := by
  intro x hx
  simp only [segBools, UpsV3.cases, List.map, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.mem_cons, List.mem_append, List.not_mem_nil, or_false, xb, cLP, cBR, cBV, cBI, cLSa, cLSb, cLSc, cESl0,
    cESl1, cESn0, cESn1, dd0, dd1, dd2, ts1, ts2, ts3, ti0, ti1, ti2, pres] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [segCell] <;> (try simp) <;> (try bsimp) <;> bclose

theorem lt8 {x : Nat} (h : x < 8) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by omega
theorem lt14 {x : Nat} (h : x < 14) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨
    x = 9 ∨ x = 10 ∨ x = 11 ∨ x = 12 ∨ x = 13 := by omega

set_option hygiene false in
macro "rowbools_cases" : tactic => `(tactic| (simp only [rowBools, UpsV3.states, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false, act, wk, vb, qb, sf, wt1, wt2, wt3, pf, pl, rd, cp, aft, sTAG, sHPL,
    sHPF, sKEY, sVLEN, sVH, sBM, sCH, sMEM, fs, fe, fw, lastw, wfr, tgt, wy, wn, gD, gMs, gMr, mS, mK, mB, rdc] at hx <;>
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl))

theorem walk_rowbits (I : UpsInst) (t : Nat) : ∀ x ∈ UpsV3.rowBools, B01 (WC I t x) := by
  intro x hx; rowbools_cases <;> cellsimp <;> (try bsimp) <;> bclose

theorem val_rowbits (I : UpsInst) (p : Nat) : ∀ x ∈ UpsV3.rowBools, B01 (VC I p x) := by
  intro x hx; rowbools_cases <;> cellsimp <;> (try bsimp) <;> bclose

theorem node_rowbits (I : UpsInst) (Q : UpsPartI) (k p st ix fl wi u : Nat) :
    ∀ x ∈ UpsV3.rowBools, B01 (QC I Q k p st ix fl wi u x) := by
  intro x hx; rowbools_cases <;> cellsimp <;> (try bsimp) <;> bclose

theorem val_partbits (I : UpsInst) (p : Nat) : ∀ x ∈ UpsV3.partBools, B01 (VC I p x) := by
  intro x hx
  simp only [partBools, UpsV3.kinds, List.map, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.mem_cons, List.mem_append, List.not_mem_nil, or_false, jo, kRDB, kRDE, kRLP, kRBR, kRBV, kRBI, kMVL, kMVE,
    kNLF, kWEX, kSPB, kPT, sd0, sd1, sd2, qtl, qte, qtb1, qtb2, qodd, nokey, UpsV3.nochild, rootP, eL, eS, useA,
    UpsV3.bN, bL, cO, cS, UpsV3.neg, podd, vcp, xcp, spY1, spY2, UpsV3.up] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> cellsimp <;> (try bsimp) <;> bclose

theorem node_partbits (I : UpsInst) (Q : UpsPartI) (k p st ix fl wi u : Nat)
    (hb : Q.qodd ≤ 1 ∧ Q.nochild ≤ 1 ∧ Q.neg ≤ 1 ∧ Q.podd ≤ 1) :
    ∀ x ∈ UpsV3.partBools, B01 (QC I Q k p st ix fl wi u x) := by
  intro x hx
  obtain ⟨h1, h2, h3, h4⟩ := hb
  simp only [partBools, UpsV3.kinds, List.map, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
    List.mem_cons, List.mem_append, List.not_mem_nil, or_false, jo, kRDB, kRDE, kRLP, kRBR, kRBV, kRBI, kMVL, kMVE,
    kNLF, kWEX, kSPB, kPT, sd0, sd1, sd2, qtl, qte, qtb1, qtb2, qodd, nokey, UpsV3.nochild, rootP, eL, eS, useA,
    UpsV3.bN, bL, cO, cS, UpsV3.neg, podd, vcp, xcp, spY1, spY2, UpsV3.up] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> cellsimp <;> (try bsimp) <;> first | bclose | exact b01_nat (by assumption)

/-- `reg` bits on `TAG` / `HPF` rows (nibble bits of the read byte). -/
theorem node_nibbits (I : UpsInst) (Q : UpsPartI) (k p st ix fl wi u : Nat) (hs : st = 0 ∨ st = 1 ∨ st = 2) :
    ∀ i, i < 8 → B01 (QC I Q k p st ix fl wi u (129 + i)) := by
  intro i hi
  rcases hs with rfl | rfl | rfl <;>
    rcases lt8 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cellsimp <;> simp [winFrV,WinFrB,ind] <;> exact b01_mod _

/-- `reg` bits on `MEM` rows (byte bits, carries). -/
theorem node_membits (I : UpsInst) (Q : UpsPartI) (k p ix fl wi u : Nat) :
    ∀ i, i < 14 → B01 (QC I Q k p 8 ix fl wi u (129 + i)) := by
  intro i hi
  have hw : winFrV I Q 8 wi = 0 := rfl
  rcases lt14 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cellsimp <;>
    simp only [hw, show (0 : Int) ≠ 1 by decide, ite_false, ite_true, memReg, Nat.reduceSub, Nat.reduceLT,
      Nat.reduceAdd, Nat.reduceEqDiff, or_false, false_or] <;> exact b01_mod _

/-- `W1` / `W2` bitmap bits. -/
theorem walk_bmbits (I : UpsInst) (t : Nat) (ht : t = 1 ∨ t = 2) :
    ∀ i, i < 16 → B01 (WC I t (129 + i)) := by
  intro i hi
  have hs : isSeg (129 + i) = false := by simp only [isSeg]; simp; omega
  simp only [WC, hs, Bool.false_eq_true, ite_false]
  unfold wCell
  split <;> (try omega)
  rw [if_pos (by omega)]; simp only [wReg, Nat.add_sub_cancel_left]
  rcases ht with rfl | rfl <;> simp only [Nat.reduceEqDiff, ite_false] <;> split <;> first | exact b01_natmod _ | exact b01_0

theorem rowBools_lt : ∀ x ∈ UpsV3.rowBools, x < 187 := by decide
theorem segBools_seg : ∀ x ∈ UpsV3.segBools, x < 187 ∧ isSeg x = true := by decide
theorem partBools_lt : ∀ x ∈ UpsV3.partBools, x < 187 := by decide

theorem gate0 {C D P : Nat → Int} {fst lst trn : Int} {g : Expr} (h : ev C D fst lst trn P g = 0) :
    ev C D fst lst trn P g = 0 ∨ B01 0 := .inl h

/-- The blocks of `cBool`. -/
theorem cBool_cases {ex : Expr} (h : ex ∈ UpsV3.cBool) :
    (∃ x ∈ UpsV3.rowBools, ex = Dsl.bool (c x)) ∨
    (∃ x ∈ UpsV3.segBools, ex = .mul (c sf) (Dsl.bool (c x))) ∨
    (∃ x ∈ UpsV3.partBools, ex = .mul (c pf) (Dsl.bool (c x))) ∨
    ex = Dsl.bool mDE ∨
    (∃ i, i < 8 ∧ ex = .mul (sumc [sTAG,sHPL,sHPF]) (Dsl.bool (c (reg i)))) ∨
    (∃ i, i < 14 ∧ ex = .mul (c sMEM) (Dsl.bool (c (reg i)))) ∨
    (∃ i, i < 16 ∧ ex = .mul (.add (c wt1) (c wt2)) (Dsl.bool (c (wb i)))) ∨
    ex ∈ [.mul (c wk) (Dsl.bool (c enter)), .mul (c wk) (Dsl.bool (c hv)),
      .mul (c wk) (Dsl.bool (c lv0)), .mul (c wk) (Dsl.bool (c lv1)), .mul (c wk) (Dsl.bool (c lv2))] := by
  simp only [UpsV3.cBool, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at h
  rcases h with ((((((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) | h) | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) |
    ⟨i, hi, rfl⟩) | h
  · exact .inl ⟨x, hx, rfl⟩
  · exact .inr (.inl ⟨x, hx, rfl⟩)
  · exact .inr (.inr (.inl ⟨x, hx, rfl⟩))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨i, hi, rfl⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨i, hi, rfl⟩)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨i, hi, rfl⟩))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr h))))))

section
variable {C D P : Nat → Int} {fst lst trn : Int}

theorem cBool_w {I : UpsInst} (iok : InstOk I) {t : Nat} (ht : t < 4) (hC : ∀ x, x < 187 → C x = WC I t x) :
    ∀ ex ∈ UpsV3.cBool, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  rcases cBool_cases hex with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ |
    ⟨i, hi, rfl⟩ | h
  · exact ev_bool (by rw [hC x (rowBools_lt x hx)]; exact walk_rowbits I t x hx)
  · obtain ⟨hl, hs⟩ := segBools_seg x hx
    exact ev_gbool (.inr (by rw [hC x hl]; simp only [WC, hs, ite_true]; exact seg_bits I x hx))
  · exact ev_gbool (.inl (by simp only [ev, Dsl.c, Bool.false_eq_true, ite_false, pf]; rw [hC 8 (by decide)]; rfl))
  · apply cast0
    have hm := iok.walk.mode t ht
    ups_ev [hC]; cellsimp
    rcases (show (step I t).mode = 0 ∨ (step I t).mode = 1 ∨ (step I t).mode = 2 ∨ (step I t).mode = 3 by omega)
      with h | h | h | h <;> simp [h, ind]
  · exact ev_gbool (.inl (by
      simp only [ev, sumc, Dsl.sum, Dsl.c, List.map, List.foldl, Bool.false_eq_true, ite_false, sTAG, sHPL, sHPF]
      rw [hC 106 (by decide), hC 107 (by decide), hC 108 (by decide)]; rfl))
  · exact ev_gbool (.inl (by
      simp only [ev, Dsl.c, Bool.false_eq_true, ite_false, sMEM]; rw [hC 114 (by decide)]; rfl))
  · by_cases h12 : t = 1 ∨ t = 2
    · exact ev_gbool (.inr (by simp only [wb, reg]; rw [hC _ (by omega)]; exact walk_bmbits I t h12 i hi))
    · exact ev_gbool (.inl (by
        simp only [ev, Dsl.c, Bool.false_eq_true, ite_false, wt1, wt2]
        rw [hC 5 (by decide), hC 6 (by decide)]; simp [WC, isSeg, wCell, ind]; omega))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    have hv : (step I t).mode = 2 → (step I t).hv ≤ 1 := fun h2 => (iok.walk.absB t ht h2).2.1
    have he : ent I t ≤ 1 := by unfold ent; split <;> omega
    rcases h with rfl | rfl | rfl | rfl | rfl <;> refine ev_gbool (.inr ?_) <;>
      simp only [enter, UpsV3.hv, lv0, lv1, lv2] <;> rw [hC _ (by decide)] <;> cellsimp
    · exact b01_nat he
    · by_cases h2 : (step I t).mode = 2
      · simp only [h2, ite_true]; exact b01_nat (hv h2)
      · simp only [h2, ite_false]; exact b01_0
    all_goals exact b01_ind _

theorem cBool_v {I : UpsInst} {p : Nat} (hC : ∀ x, x < 187 → C x = VC I p x) :
    ∀ ex ∈ UpsV3.cBool, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  rcases cBool_cases hex with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ |
    ⟨i, hi, rfl⟩ | h
  · exact ev_bool (by rw [hC x (rowBools_lt x hx)]; exact val_rowbits I p x hx)
  · obtain ⟨hl, hs⟩ := segBools_seg x hx
    exact ev_gbool (.inr (by rw [hC x hl]; simp only [VC, hs, ite_true]; exact seg_bits I x hx))
  · exact ev_gbool (.inr (by rw [hC x (partBools_lt x hx)]; exact val_partbits I p x hx))
  · apply cast0; ups_ev [hC]; cellsimp
  all_goals first
    | (simp only [List.mem_cons, List.not_mem_nil, or_false] at h
       rcases h with rfl | rfl | rfl | rfl | rfl <;> exact ev_gbool (.inl (by
         simp only [ev, Dsl.c, Bool.false_eq_true, ite_false, wk]; rw [hC 1 (by decide)]; rfl)))
    | exact ev_gbool (.inl (by
        simp only [ev, sumc, Dsl.sum, Dsl.c, List.map, List.foldl, Bool.false_eq_true, ite_false, sTAG, sHPL, sHPF, sMEM, wt1, wt2]
        (repeat rw [hC _ (by decide)]); rfl))

theorem cBool_q {I : UpsInst} {Q : UpsPartI} {k p st ix fl wi u : Nat}
    (hb : Q.qodd ≤ 1 ∧ Q.nochild ≤ 1 ∧ Q.neg ≤ 1 ∧ Q.podd ≤ 1) (hC : ∀ x, x < 187 → C x = QC I Q k p st ix fl wi u x) :
    ∀ ex ∈ UpsV3.cBool, ((ev C D fst lst trn P ex : Int) : Fp) = 0 := by
  intro ex hex
  rcases cBool_cases hex with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ |
    ⟨i, hi, rfl⟩ | h
  · exact ev_bool (by rw [hC x (rowBools_lt x hx)]; exact node_rowbits I Q k p st ix fl wi u x hx)
  · obtain ⟨hl, hs⟩ := segBools_seg x hx
    exact ev_gbool (.inr (by rw [hC x hl]; simp only [QC, hs, ite_true]; exact seg_bits I x hx))
  · exact ev_gbool (.inr (by rw [hC x (partBools_lt x hx)]; exact node_partbits I Q k p st ix fl wi u hb x hx))
  · apply cast0; ups_ev [hC]; cellsimp
  · by_cases hs : st = 0 ∨ st = 1 ∨ st = 2
    · exact ev_gbool (.inr (by simp only [reg]; rw [hC _ (by omega)]; exact node_nibbits I Q k p st ix fl wi u hs i hi))
    · exact ev_gbool (.inl (by
        simp only [ev, sumc, Dsl.sum, Dsl.c, List.map, List.foldl, Bool.false_eq_true, ite_false, sTAG, sHPL, sHPF]
        rw [hC 106 (by decide), hC 107 (by decide), hC 108 (by decide)]; cellsimp; simp [ind]; omega))
  · by_cases hs : st = 8
    · subst hs
      exact ev_gbool (.inr (by simp only [reg]; rw [hC _ (by omega)]; exact node_membits I Q k p ix fl wi u i hi))
    · exact ev_gbool (.inl (by
        simp only [ev, Dsl.c, Bool.false_eq_true, ite_false, sMEM]
        rw [hC 114 (by decide)]; cellsimp; simp [ind]; omega))
  · exact ev_gbool (.inl (by
      simp only [ev, Dsl.c, Bool.false_eq_true, ite_false, wt1, wt2]
      rw [hC 5 (by decide), hC 6 (by decide)]; rfl))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> exact ev_gbool (.inl (by
      simp only [ev, Dsl.c, Bool.false_eq_true, ite_false, wk]; rw [hC 1 (by decide)]; rfl))

end

/-- **`cBool`.** -/
theorem cBool_ok {insts : List UpsInst} (ok : UpsOk insts) {H : Nat} (hH : R insts + 1 ≤ H) :
    GroupOk insts H UpsV3.cBool := by
  apply groupOk_by ok hH (fun e he => by simp [UpsV3.constraints, he])
  · intro i hi t ht q _ _ C D P hC _
    exact cBool_w (ok.inst _ (inst_mem hi)) ht hC
  · intro i hi p hp q _ _ C D P hC _
    exact cBool_v hC
  · intro i hi k p hk hp q _ _ C D P hC _
    exact cBool_q ((ok.inst _ (inst_mem hi)).bits k hk) hC

end UpsGen

end ZkFormal.NearV3.Render
