import ZkFormal.NearV3.Assembly.RcptEmitLocal

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Header refund flags are zero. Receipt refund flags remain their native plan
input; this choice also supplies the header Boolean column for cStates. -/
def emissionHeaderFallback (fallback : ListPlan→Coord→Nat→Fp)
    (p : ListPlan) (row : Coord) (col : Nat) : Fp :=
  if col=hr then 0 else fallback p row col

def plannedState (lists : List (List Input)) (pos : Nat) : Nat :=
  match (plannedRows lists)[pos]? with | none=>0 | some a=>(eraseRow a).state

def emittedReceiptBase (own : Nat) (ctx : ApplyCtx) (lists : List (List Input)) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) : Trace Fp :=
  nativeReceiptTrace own ctx lists log constants pub digests fallback (emissionHeaderFallback headerFallback)

def emittedReceiptTrace (own : Nat) (ctx : ApplyCtx) (lists : List (List Input)) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) : Trace Fp :=
  emissionPatch (emittedReceiptBase own ctx lists log constants pub digests fallback headerFallback)
    pub (fun _ pos=>plannedState lists pos)

theorem plannedSegments_states (lists : List (List Input)) : ∀p∈plannedSegments lists,p.state∈states := by
  intro p hp
  obtain ⟨lp,_,hp⟩ := List.mem_flatMap.mp hp
  simp only [listSegments,List.mem_cons] at hp
  rcases hp with rfl|hp
  · change sCL∈states;decide
  · obtain ⟨rp,_,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hp
    exact fields_states rp.input.refund s hs

theorem planned_row_state (lists : List (List Input)) (a : PlannedRow)
    (ha : a∈plannedRows lists) : (eraseRow a).state∈states := by
  rw [←plannedSegments_rows] at ha
  obtain ⟨p,hp,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨row,hr,he⟩ := List.mem_map.mp ha
  obtain ⟨hs,_,_⟩ := segment_member hr
  rw [←he,p.erase_wrap,hs]
  exact plannedSegments_states lists p hp

/-- Concrete one-hot states, active flag, and Boolean refund flag on the exact
base trace used by the emission extension. -/
theorem emittedReceiptBase_controls (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) :
    let base := emittedReceiptBase own ctx lists log constants pub digests fallback headerFallback
    (∀s∈states,base.cell 0 pos s=if s=plannedState lists pos then 1 else 0) ∧
    base.cell 0 pos act=(if plannedState lists pos=0 then 0 else 1) ∧
    (base.cell 0 pos hr=0 ∨ base.cell 0 pos hr=1) := by
  dsimp only
  unfold emittedReceiptBase nativeReceiptTrace
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    have hz := plannedTrace_padding lists log pos constants
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
      (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt))
        (emissionHeaderFallback headerFallback)) (List.getElem?_eq_none_iff.mp ha)
    have hs : plannedState lists pos=0 := by simp [plannedState,ha]
    refine ⟨?_,?_,Or.inl (hz hr)⟩
    · intro s hsm
      rw [hs]
      have hlim := states_limits hsm
      have he : s≠0 := by omega
      simpa [he] using hz s
    · simpa only [hs,ite_true] using hz act
  | some a =>
    have hm := planned_row_state lists a (List.mem_of_getElem? ha)
    have hlim := states_limits hm
    have hnon : (eraseRow a).state≠0 := by omega
    have hs : plannedState lists pos=(eraseRow a).state := by simp [plannedState,ha]
    have hc := plannedTrace_cell lists log pos constants
      (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
      (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt))
        (emissionHeaderFallback headerFallback)) a ha
    refine ⟨?_,?_,?_⟩
    · intro s hsm
      rw [hs]
      change (plannedTrace lists log constants _ _).cell 0 pos s=_
      rw [hc s]
      have hl := states_limits hsm
      cases a with
      | header lp row => exact (header_control_cell _ lp row (by simp [controlColumn];omega)).trans (control_state row hsm)
      | receipt rp row => exact (receipt_control_cell _ _ rp row (by simp [controlColumn];omega)).trans (control_state row hsm)
    · rw [hs]
      simp only [if_neg hnon]
      change (plannedTrace lists log constants _ _).cell 0 pos act=1
      rw [hc act]
      cases a <;> rfl
    · change (plannedTrace lists log constants _ _).cell 0 pos hr=0 ∨
        (plannedTrace lists log constants _ _).cell 0 pos hr=1
      rw [hc hr]
      cases a with
      | header lp row => exact Or.inl rfl
      | receipt rp row =>
        change (if rp.input.refund then (1:Fp) else 0)=0 ∨ (if rp.input.refund then (1:Fp) else 0)=1
        cases rp.input.refund <;> first | exact Or.inl rfl | exact Or.inr rfl

/-- Both register and emission groups on one concrete trace: 200+189 equations.
No Boolean/state/cell correspondence premises are delegated to the prover. -/
theorem emittedReceiptTrace_regs_emit (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length≤2^log)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^log→∀e∈cRegs++cEmit,
      e.eval (emittedReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro pos hp e he
  rcases List.mem_append.mp he with he|he
  · exact emissionPatch_cRegs _ pub _ 0 pos
      (nativeReceiptTrace_cRegs own ctx lists hw log constants pub digests fallback
        (emissionHeaderFallback headerFallback) hcap hown pos hp) e he
  · obtain ⟨hs,ha,hr⟩ := emittedReceiptBase_controls own ctx lists log pos constants pub digests fallback headerFallback
    exact emissionPatch_cEmit _ pub _ 0 pos hs ha hr e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
