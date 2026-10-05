import ZkFormal.Near.Link.Digests

/-!
# ZkFormal.Near.Link.RunChain — slot values along the memory chain, `arith` for every receipt

* `slot_acct` — every receipt's slot has an `acct` entry;
* `lanes` — `lk`, `st` are the slot's pre-state locked/storage lanes, `bef` bytes;
* `arith_ok` — the arithmetic facts of every receipt (all `Bytes8` hypotheses discharged).
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem bytes8_of_getD {l : List Nat} {n : Nat} (hl : l.length = n) (h : ∀ i, i < n → l.getD i 0 < 256) :
    Bytes8 l := by
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hy
  have := h i (by omega)
  rwa [getD_eq_getElem _ _ hi] at this

theorem getD_lt_of_bytes8 {l : List Nat} (h : Bytes8 l) (i : Nat) : l.getD i 0 < 256 := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp
  | some y => exact h y (List.mem_of_getElem? hi)

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem slot_acct : ∀ r (hr : r < rs.length), ∃ a ∈ as, a.k = rs[r].kslot := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro hr
    rcases lastW_cases (ksl rs) rs[r].kslot r with e | ⟨r0, -, -, e⟩
    · obtain ⟨a, ha, hk, -⟩ := (mem_read h hr (i := 0) (by decide)).1 e
      exact ⟨a, ha, hk⟩
    · obtain ⟨hr0, hlt, hk, -⟩ := (mem_read h hr (i := 0) (by decide)).2 r0 e
      obtain ⟨a, ha, hk'⟩ := ih r0 hlt hr0
      exact ⟨a, ha, hk' ▸ hk ▸ rfl⟩

/-- Lanes of a receipt's read: locked and storage are the slot's pre-state lanes. -/
theorem lanes : ∀ r (hr : r < rs.length), ∀ a ∈ as, a.k = rs[r].kslot → ∀ i, i < 16 →
    rs[r].lk.getD i 0 = a.pre.getD (16 + i) 0 ∧
    rs[r].st.getD i 0 = (if i < 8 then a.pre.getD (64 + i) 0 else 0) ∧
    rs[r].bef.getD i 0 < 256 := by
  have hnd := (vslot h).1
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro hr a ha hk i hi
    rcases lastW_cases (ksl rs) rs[r].kslot r with e | ⟨r0, -, -, e⟩
    · obtain ⟨b, hb, hbk, he⟩ := (mem_read h hr hi).1 e
      have : b = a := by
        have := (acctOf_eq hnd hb).symm.trans ((hbk.trans hk.symm) ▸ acctOf_eq hnd ha)
        simpa using this
      subst this
      obtain ⟨-, -, -, -, hpre, -⟩ := acct_digests h hb
      simp only [rdMsg, awMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he
      refine ⟨he.2.2.2.2.1, he.2.2.2.2.2.1, ?_⟩
      rw [he.2.2.2.1]; exact getD_lt_of_bytes8 hpre _
    · obtain ⟨hr0, hlt, hk0, he⟩ := (mem_read h hr hi).2 r0 e
      obtain ⟨_, _, _, w0⟩ := rcpt_wf_at h hr0
      obtain ⟨i1, i2, -⟩ := ih r0 hlt hr0 a ha (hk.trans hk0.symm) i hi
      simp only [rdMsg, wrMsg, List.cons.injEq] at he
      refine ⟨he.2.2.2.2.1.trans i1, he.2.2.2.2.2.1.trans i2, ?_⟩
      rw [he.2.2.2.1]; exact getD_lt_of_bytes8 w0.aft8 _

theorem bgp_lt : leN' (pubBytes (publicOf c) PV_BGP 16) = c.1.blockGasPrice ∧
    c.1.blockGasPrice < Params.two128 := by
  have hh := hdr_of c h.rcpt
  obtain ⟨-, -, b, -⟩ := wf_bounds c
  refine ⟨leN'_pub_field (pub_bgp hh) b, ?_⟩
  have : (256:Nat) ^ 16 = Params.two128 := by decide
  omega

/-- The arithmetic facts of receipt `r`, with the block gas price and running tokens. -/
theorem arith_ok {r : Nat} (hr : r < rs.length) {tok tok' : Nat}
    (w : rs[r].Wf r (leN' (pubBytes (publicOf c) PV_BGP 16)) tok tok') :
    let x := rs[r]; let bgp := c.1.blockGasPrice
    leN' x.aft = leN' x.bef + leN' x.dep ∧ leN' x.aft < Params.u128Max ∧
    leN' x.aft + leN' x.lk < Params.two128 ∧
    (Params.storageAmountPerByte * leN' x.st ≤ leN' x.aft + leN' x.lk ∨
      leN' x.st ≤ Params.zeroBalanceStorageLimit) ∧
    (x.ge = decide (bgp ≤ leN' x.gp)) ∧
    leN' x.burnt = Params.G * min (leN' x.gp) bgp ∧
    (x.hr = true ↔ Params.G * (leN' x.gp - min (leN' x.gp) bgp) ≠ 0) ∧
    (x.hr = true → leN' x.ramt = Params.G * (leN' x.gp - min (leN' x.gp) bgp)) ∧
    tok' = tok + leN' x.burnt ∧ tok' < Params.two128 := by
  obtain ⟨hbgp, hbgpl⟩ := bgp_lt h
  rw [hbgp] at w
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13⟩ := w.lens
  obtain ⟨hrcb, -⟩ := rc_digest h
  have hencb : Bytes8 rs[r].enc := bytes8_of_sub hrcb (fun y hy => by
    simp only [rcMsg, List.mem_append, List.mem_flatMap]; right
    exact ⟨_, List.getElem_mem hr, hy⟩)
  have hgp : Bytes8 rs[r].gp := bytes8_of_sub hencb (fun y hy => by simp [RcptV.enc, hy])
  have hdep : Bytes8 rs[r].dep := bytes8_of_sub hencb (fun y hy => by simp [RcptV.enc, hy])
  obtain ⟨a, ha, hk⟩ := slot_acct h r hr
  have hl := lanes h r hr a ha hk
  obtain ⟨-, -, -, -, hpre, -⟩ := acct_digests h ha
  have hbef : Bytes8 rs[r].bef := bytes8_of_getD l6 (fun i hi => (hl i hi).2.2)
  have hlk : Bytes8 rs[r].lk := bytes8_of_getD l7 (fun i hi => by
    rw [(hl i hi).1]; exact getD_lt_of_bytes8 hpre _)
  have hst : Bytes8 rs[r].st := bytes8_of_getD l8 (fun i hi => by
    rw [(hl i hi).2.1]; split
    · exact getD_lt_of_bytes8 hpre _
    · decide)
  obtain ⟨hpeo, -⟩ := peo_digest h hr
  have hburnt : Bytes8 rs[r].burnt := bytes8_of_sub hpeo (fun y hy => by simp [RcptV.peo, hy])
  have hramt : rs[r].hr = true → Bytes8 rs[r].ramt := by
    intro hhr
    obtain ⟨hrf, -⟩ := rf_digest h
    refine bytes8_of_sub hrf (fun y hy => ?_)
    rw [rfMsg_eq]; simp only [List.mem_append, List.mem_flatMap]; right
    exact ⟨_, List.getElem_mem hr, (by simp [rfPart, hhr, RcptV.encRefund, hy])⟩
  exact w.arith hgp hdep hbef hlk hst hburnt hramt hbgpl

end Hyp

end Link

end ZkFormal.Near
