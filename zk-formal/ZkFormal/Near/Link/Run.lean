import ZkFormal.Near.Link.RunAcc

/-!
# ZkFormal.Near.Link.Run — `run_ok : RunStmt`

The amount of a slot before receipt `r` is the value of its last write
(`amt_inv`); with `arith_ok` this gives `RcptOk` for every receipt, and the
running token sums are the `RcptWf` ones.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

/-- Value written to slot `a.k` at time `t`. -/
def wval (rs : RcptVs) (a : AcctV) (t : Nat) : Nat :=
  if t = 0 then leN' (a.pre.take 16) else leN' (rs.getD (t - 1) default).aft

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem acc0_eq {a : AcctV} (ha : a ∈ as) : (linkExt vs as rs).acc0 a.k = accOf a := by
  have hnd := (vslot h).1
  obtain ⟨-, -, -, -, hpre, -⟩ := acct_digests h ha
  have hl := h.acct.len a ha
  have hd := decode_pre hl.1 hpre (h.acct.notMax a ha (fun i _ => getD_lt_of_bytes8 hpre i))
  simp only [Ext.acc0, linkExt, acctOf_eq hnd ha, Option.map_some, Option.getD_some, hd]

omit h in
theorem rc_eq {r : Nat} (hr : r < rs.length) : (linkExt vs as rs).rc r = rs[r].toReceipt := by
  simp [Ext.rc, linkExt, List.getD_eq_getElem?_getD, hr]

theorem bef_val {r : Nat} (hr : r < rs.length) {a : AcctV} (ha : a ∈ as) (hk : a.k = rs[r].kslot) :
    leN' rs[r].bef = wval rs a (lastW (ksl rs) a.k r) := by
  have hnd := (vslot h).1
  obtain ⟨_, _, _, w⟩ := rcpt_wf_at h hr
  obtain ⟨-, -, -, -, -, l6, -⟩ := w.lens
  have hl := h.acct.len a ha
  rw [hk]
  rcases lastW_cases (ksl rs) rs[r].kslot r with e | ⟨r0, -, -, e⟩
  · rw [e]; simp only [wval, if_true]
    congr 1
    apply ext16 l6 (by simp [hl.1])
    intro i hi
    obtain ⟨b, hb, hbk, he⟩ := (mem_read h hr hi).1 e
    have : b = a := by
      have := (acctOf_eq hnd hb).symm.trans ((hbk.trans hk.symm) ▸ acctOf_eq hnd ha)
      simpa using this
    subst this
    simp only [rdMsg, awMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he
    rw [he.2.2.2.1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos hi]
  · rw [e]; simp only [wval, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    obtain ⟨hr0, -, -, -⟩ := (mem_read h hr (i := 0) (by decide)).2 r0 e
    obtain ⟨_, _, _, w0⟩ := rcpt_wf_at h hr0
    obtain ⟨-, -, -, -, -, -, -, -, l9, -⟩ := w0.lens
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr0, Option.getD_some]
    congr 1
    apply ext16 l6 l9
    intro i hi
    obtain ⟨_, -, -, he2⟩ := (mem_read h hr hi).2 r0 e
    simp only [rdMsg, wrMsg, List.cons.injEq] at he2
    exact he2.2.2.2.1

/-- The token sums of `RcptWf`. -/
theorem toks_spec : ∃ toks : List Nat, toks.length = rs.length + 1 ∧ toks.head? = some 0 ∧
    (∀ r (hr : r < rs.length), rs[r].Wf r (leN' (pubBytes (publicOf c) PV_BGP 16)) (toks.getD r 0)
      (toks.getD (r + 1) 0)) ∧ toks.getD rs.length 0 = c.1.tokensBurntTotal := by
  obtain ⟨toks, h1, h2, h3, h4⟩ := rcptWf_at h.rcpt
  obtain ⟨-, -, -, -, -, -, -, bt⟩ := wf_bounds c
  refine ⟨toks, h1, h2, h3, ?_⟩
  rw [h4 (fun _ _ => pubNat_lt c _), leN'_pub_field (pub_tok (hdr_of c h.rcpt)) bt]

theorem amt_inv {a : AcctV} (ha : a ∈ as) :
    ∀ r, r ≤ rs.length → (linkExt vs as rs).amtAt a.k r = wval rs a (lastW (ksl rs) a.k r)
  | 0, _ => by
    simp only [Ext.amtAt, acc0_eq h ha, lastW, wval, if_true, accOf]
  | r + 1, hr => by
    have ih := amt_inv ha r (by omega)
    simp only [Ext.amtAt, lastW]
    rw [ih]
    have hs : (linkExt vs as rs).slot r = ksl rs r := rfl
    rw [hs]
    split
    · next hk =>
      have hr' : r < rs.length := by omega
      obtain ⟨toks, -, -, hw, -⟩ := toks_spec h
      have ar := arith_ok h hr' (hw r hr')
      rw [rc_eq hr', ← bef_val h hr' ha (by rw [← hk, ksl_eq hr'])]
      simp only [wval, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr', Option.getD_some]
      rw [ar.1]; rfl
    · simp

theorem tok_inv {toks : List Nat} (h0 : toks.head? = some 0)
    (hw : ∀ r (hr : r < rs.length), rs[r].Wf r (leN' (pubBytes (publicOf c) PV_BGP 16)) (toks.getD r 0)
      (toks.getD (r + 1) 0)) :
    ∀ r, r ≤ rs.length → (linkExt vs as rs).tokAt c.1 r = toks.getD r 0
  | 0, _ => by
    cases toks with
    | nil => simp at h0
    | cons t l => simp at h0; subst h0; rfl
  | r + 1, hr => by
    have hr' : r < rs.length := by omega
    have ar := arith_ok h hr' (hw r hr')
    simp only [Ext.tokAt]
    rw [tok_inv h0 hw r (by omega), ar.2.2.2.2.2.2.2.2.1, ar.2.2.2.2.2.1, rc_eq hr']
    rfl

theorem lk_eq {r : Nat} (hr : r < rs.length) {a : AcctV} (ha : a ∈ as) (hk : a.k = rs[r].kslot) :
    leN' rs[r].lk = (accOf a).locked := by
  obtain ⟨_, _, _, w⟩ := rcpt_wf_at h hr
  obtain ⟨-, -, -, -, -, -, l7, -⟩ := w.lens
  have hl := h.acct.len a ha
  simp only [accOf]; congr 1
  apply ext16 l7 (by simp [hl.1])
  intro i hi
  rw [(lanes h r hr a ha hk i hi).1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take, if_pos hi, List.getElem?_drop]

theorem st_eq {r : Nat} (hr : r < rs.length) {a : AcctV} (ha : a ∈ as) (hk : a.k = rs[r].kslot) :
    leN' rs[r].st = (accOf a).storageUsage := by
  obtain ⟨_, _, _, w⟩ := rcpt_wf_at h hr
  obtain ⟨-, -, -, -, -, -, -, l8, -⟩ := w.lens
  have hl := h.acct.len a ha
  have : rs[r].st = a.pre.drop 64 ++ List.replicate 8 0 := by
    apply ext16 l8 (by simp [hl.1])
    intro i hi
    rw [(lanes h r hr a ha hk i hi).2.1]
    have hd : (a.pre.drop 64).length = 8 := by simp [hl.1]
    split
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        List.getElem?_drop]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), List.getElem?_replicate,
        if_pos (by rw [hd]; omega)]; rfl
  simp only [accOf]; rw [this, leN'_append_zeros]

omit h in
theorem leN'_16 {l : List Nat} (hl : l.length = 16) : leN' l < Params.two128 := by
  have := leN'_lt hl; have e : (256:Nat) ^ 16 = Params.two128 := by decide
  omega

end Hyp

theorem run_ok : RunStmt := by
  intro c vs ws rs as mv ids shaS shaR h
  obtain ⟨toks, -, h0, hw, htok⟩ := toks_spec h
  have hlen : (linkExt vs as rs).rs.length = rs.length := by simp [linkExt]
  refine ⟨fun r hr => ?_, ?_⟩
  · rw [hlen] at hr
    obtain ⟨_, _, _, w⟩ := rcpt_wf_at h hr
    obtain ⟨-, -, -, -, -, -, -, -, -, l10, l11, -⟩ := w.lens
    have ar := arith_ok h hr (hw r hr)
    obtain ⟨a, ha, hk⟩ := slot_acct h r hr
    have hs : (linkExt vs as rs).slot r = a.k := by
      show ksl rs r = a.k; rw [ksl_eq hr, hk]
    have hamt : (linkExt vs as rs).amtAt a.k r = leN' rs[r].bef := by
      rw [amt_inv h ha r (by omega), bef_val h hr ha hk]
    have hrc := rc_eq (vs := vs) (as := as) hr
    have hacc := acc0_eq h ha
    have hlk := lk_eq h hr ha hk
    have hst := st_eq h hr ha hk
    have htk := tok_inv h h0 hw r (by omega)
    obtain ⟨a1, a2, a3, a4, -, a6, a7, a8, a9, a10⟩ := ar
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [hs, hamt, hrc, hacc, burntOf, surplusOf, burnPrice, RcptV.toReceipt, htk, ← hlk,
        ← hst]
    · omega
    · omega
    · rw [← a1]; exact a4
    · rw [← a6]; exact leN'_16 l10
    · by_cases hhr : rs[r].hr = true
      · rw [← a8 hhr]; exact leN'_16 l11
      · have : ¬ (Params.G * (leN' rs[r].gp - min (leN' rs[r].gp) c.1.blockGasPrice) ≠ 0) :=
          fun hc => hhr (a7.mpr hc)
        have : Params.G * (leN' rs[r].gp - min (leN' rs[r].gp) c.1.blockGasPrice) = 0 := by omega
        rw [this]; decide
    · rw [← a6, ← a9]; exact a10
  · rw [hlen, tok_inv h h0 hw _ (Nat.le_refl _), htok]


end Link

end ZkFormal.Near
