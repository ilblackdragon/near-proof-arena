import ZkFormal.NearV3.Assembly.RcptFinalSegment

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem FinalSegment.not_GP (p : SegmentPlan) (hp : FinalSegment p) : p.state≠sGP := by
  cases p with
  | header lp => change sCL≠sGP;decide
  | receipt rp s =>
    change s≠sGP
    rw [hp.2.2]
    cases h : rp.input.refund <;> simp [finalState,h,sXRZ,sXLH,sGP]

theorem final_segment_lastR (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : SegmentPlan) (hp : FinalSegment p) (row : Coord)
    (hs : row.state=p.state) (hl : row.length=p.length) (hi : row.index+1=p.length) :
    nativePlannedCell own ctx lists constants pub digests fallback headerFallback (p.wrap row) lastR=1 := by
  cases p with
  | header lp =>
    have hidx : row.index+1=12 := hi
    change bitCell (row.index+1==12 && lp.inputs.isEmpty && lp.lastList)=1
    simp [hidx,hp.1,hp.2,bitCell]
  | receipt rp s =>
    have hend : row.index+1=row.length := by omega
    change bitCell (receiptEnd rp row && rp.lastInList && rp.lastList)=1
    have hstate : row.state=finalState rp.input := hs.trans hp.2.2
    cases hr : rp.input.refund <;>
      simp [receiptEnd,hend,hstate,finalState,hr,hp.1,hp.2.1,sXRZ,sXLH,bitCell]

/-- Complete cRegs at the last active row, even with immediate cyclic wrap.
Actual plan flags discharge lastR; it is not an input annotation premise. -/
theorem planned_final_cRegs (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (a : PlannedRow) (ha : (plannedRows lists)[pos]?=some a)
    (hn : (plannedRows lists)[pos+1]?=none)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀e∈cRegs,e.eval
      (plannedTrace lists log constants
        (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
        (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback)) 0 pos pub=0 := by
  have hidx := (List.getElem?_eq_some_iff.mp ha).1
  have hnidx := List.getElem?_eq_none_iff.mp hn
  have hlast : (plannedRows lists).getLast?=some a := by
    rw [List.getLast?_eq_getElem?,show (plannedRows lists).length-1=pos by omega]
    exact ha
  obtain ⟨p,hfinal,hpa⟩ := planned_last_final_segment lists hw a hlast
  obtain ⟨row,hs,hl,hi,hrow⟩ := p.last a hpa
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
  have hgp : tr.cell 0 pos sGP=0 := by
    rw [hctrl sGP (by decide),control_state row (by decide)]
    have hne : sGP≠row.state := by rw [hs];exact Ne.symm (FinalSegment.not_GP p hfinal)
    simp [hne]
  have hlastR : tr.cell 0 pos lastR=1 :=
    (hcell lastR).trans (final_segment_lastR own ctx lists constants pub digests fallback headerFallback p hfinal row hs hl hi)
  exact cRegs_assemble tr 0 pos pub
    (planned_currentRegs own ctx lists log pos constants pub digests fallback headerFallback p row hs hl ha' hown)
    (zero_shift_at_endpoint tr 0 pos pub hfe)
    (planned_stream_initial_tokens own ctx _ lists log pos constants _ headerFallback pub)
    (zero_gas_off_GP tr 0 pos pub hgp)
    (zero_carry_last tr 0 pos pub hact hgp hlastR)

end ZkFormal.NearV3.Assembly.RcptSkeleton
