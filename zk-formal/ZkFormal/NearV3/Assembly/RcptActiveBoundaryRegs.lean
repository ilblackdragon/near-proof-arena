import ZkFormal.NearV3.Assembly.RcptPhysicalGasBoundary

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem cRegs_assemble (tr : Trace Fp) (t pos : Nat) (pub : List Fp)
    (hc : ∀e∈currentRegs,e.eval tr t pos pub=0)
    (hs : ∀e∈shiftConstraints,e.eval tr t pos pub=0)
    (hi : ∀e∈initialTokenConstraints,e.eval tr t pos pub=0)
    (hg : ∀e∈gasTokenConstraints,e.eval tr t pos pub=0)
    (ht : ∀e∈carryTokenConstraints,e.eval tr t pos pub=0) :
    ∀e∈cRegs,e.eval tr t pos pub=0 := by
  intro e he
  rcases (cRegs_membership e).mp he with he|he
  · have hm : e∈currentRegs ∨ e∈shiftConstraints ∨ e∈gasTokenConstraints ∨ e∈carryTokenConstraints := by
      simpa only [ordinaryRegs,currentRegs,List.mem_append,or_assoc] using he
    rcases hm with he|he|he|he
    · exact hc e he
    · exact hs e he
    · exact hg e he
    · exact ht e he
  · exact hi e he

/-- All 200 cRegs at every active-to-active endpoint, including final GP shift,
receipt transitions and empty source-list headers. -/
theorem planned_active_boundary_cRegs (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (a b : PlannedRow) (ha : (plannedRows lists)[pos]?=some a) (hb : (plannedRows lists)[pos+1]?=some b)
    (hend : (eraseRow a).index+1=(eraseRow a).length) (hh : pos+1<2^log)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀e∈cRegs,e.eval
      (plannedTrace lists log constants
        (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
        (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback)) 0 pos pub=0 := by
  have hnb := neighbors_of_get _ a b pos ha hb
  rcases planned_neighbors_indexed lists hw a b hnb with ⟨p,_,hn⟩|⟨p,q,hpq,hpa,hqb,_⟩
  · obtain ⟨row,_,hlen,hi,hrow,_⟩ := p.neighbors a b hn
    rw [hrow,p.erase_wrap] at hend
    omega
  · obtain ⟨row,hstate,hlen,hi,hrow⟩ := p.last a hpa
    have ha' : (plannedRows lists)[pos]?=some (p.wrap row) := by simpa [hrow] using ha
    let tr := plannedTrace lists log constants
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
      (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback)
    have hcell (col : Nat) : tr.cell 0 pos col=
        nativePlannedCell own ctx lists constants pub digests fallback headerFallback (p.wrap row) col :=
      plannedTrace_cell _ _ _ _ _ _ _ ha' col
    have hctrl (col : Nat) (hc : controlColumn col=true) : tr.cell 0 pos col=controlCell row col :=
      (hcell col).trans (nativePlannedCell_control _ _ _ _ _ _ _ _ p row col hc)
    have hfe : tr.cell 0 pos fe=1 := by
      rw [hctrl fe (by decide)]
      change (if row.index+1=row.length then (1:Fp) else 0)=1
      have he : row.index+1=row.length := by omega
      simp [he]
    have hact : tr.cell 0 pos act=1 := by rw [hctrl act (by decide)];rfl
    have hcurrent := planned_currentRegs own ctx lists log pos constants pub digests fallback headerFallback
      p row hstate hlen ha' hown
    apply cRegs_assemble tr 0 pos pub hcurrent (zero_shift_at_endpoint tr 0 pos pub hfe)
      (planned_stream_initial_tokens own ctx _ lists log pos constants _ headerFallback pub)
    all_goals
      by_cases hgp : row.state=sGP
    · cases p with
      | header lp => change row.state=sCL at hstate; have : sCL=sGP := hstate.symm.trans hgp; cases this
      | receipt rp state =>
        change row.state=state at hstate
        have hs : state=sGP := hstate.symm.trans hgp
        rw [hs] at hpq hpa
        exact planned_GP_boundary_gas own ctx lists log pos constants pub digests fallback headerFallback
          rp q hpq a b hpa hqb ha hb hh
    · apply zero_gas_off_GP tr 0 pos pub
      rw [hctrl sGP (by decide),control_state row (by decide)]
      simp [Ne.symm hgp]
    · have hg : tr.cell 0 pos sGP=1 := by
        rw [hctrl sGP (by decide),control_state row (by decide)]
        simp [hgp]
      apply zero_carry_GP tr 0 pos pub hact hg
      rw [hcell]
      cases p with
      | header lp => change row.state=sCL at hstate; have : sCL=sGP := hstate.symm.trans hgp; cases this
      | receipt rp state =>
        change bitCell (receiptEnd rp row && rp.lastInList && rp.lastList)=0
        simp [receiptEnd,hgp,sGP,sXRZ,sXLH,bitCell]
    · have hs : (eraseRow a).state≠sGP := by simpa only [hrow,p.erase_wrap] using hgp
      exact planned_boundary_token_carry own ctx lists hw log pos constants pub digests fallback headerFallback
        a b ha hb hend hs hh

end ZkFormal.NearV3.Assembly.RcptSkeleton
