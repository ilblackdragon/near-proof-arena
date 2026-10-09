import ZkFormal.NearV3.Assembly.RcptStateSuccessors

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def successorConstraints : List Expr := succ.map (fun (s,t,g)=>.mul (mul3 (c fe) (c s) g) (Dsl.not (n t)))

theorem successor_states : ∀x∈succ,x.1∈states ∧ x.2.1∈states := by decide

theorem booleanReceiptTrace_refund (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : SegmentPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (p.wrap row)) :
    (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos hr=
      if p.refund then 1 else 0 := by
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_other _ _ _ _ _ hr (by decide)]
  unfold emittedReceiptBase nativeReceiptTrace
  rw [plannedTrace_cell lists log pos _ _ _ _ ha hr]
  cases p <;> rfl

theorem booleanReceiptTrace_successorGuard (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : SegmentPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (p.wrap row)) (s t : Nat) (g : Expr) (hg : (s,t,g)∈succ) :
    g.eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=
      g.eval (refundTrace p.refund) 0 0 [] := by
  have hh := booleanReceiptTrace_refund own ctx lists log pos constants pub digests fallback headerFallback p row ha
  rcases successor_uses_refund hg with rfl|rfl|rfl
  · rfl
  · exact hh
  · simp only [eval_not,eval_c,hh];rfl

theorem booleanReceiptTrace_successors (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length<2^log) :
    ∀e∈successorConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro e he
  obtain ⟨⟨s,t,g⟩,hg,rfl⟩ := List.mem_map.mp he
  have hstates : s∈states ∧ t∈states := successor_states (s,t,g) hg
  have hsc : controlColumn s=true := by have hl := states_limits hstates.1;simp [controlColumn];omega
  have htc : controlColumn t=true := by have hl := states_limits hstates.2;simp [controlColumn];omega
  have hc := booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback
  simp only [eval_mul,eval_mul3,eval_c,eval_not,eval_n]
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    rw [hc fe (by decide),ha]
    grind only
  | some a =>
    by_cases hend : (eraseRow a).index+1=(eraseRow a).length
    · cases hb : (plannedRows lists)[pos+1]? with
      | none =>
        have hlast : (plannedRows lists).getLast?=some a := by
          have hh := (List.getElem?_eq_some_iff.mp ha).1
          have hn := List.getElem?_eq_none_iff.mp hb
          rw [List.getLast?_eq_getElem?,show (plannedRows lists).length-1=pos by omega]
          exact ha
        obtain ⟨p,hp,hplast⟩ := planned_last_final_segment lists hw a hlast
        obtain ⟨row,hs,hl,hi,hea⟩ := p.last a hplast
        have hoff : SuccessorsOff p := by
          cases p with
          | header lp => exact header_successorsOff lp
          | receipt rp state =>
            obtain ⟨_,_,hs⟩ := hp
            rw [hs];exact terminal_successorsOff rp
        subst a
        rw [hc s hsc]
        simp only [ha,p.erase_wrap]
        rw [control_state row hstates.1]
        by_cases heq : s=row.state
        · rw [if_pos heq,booleanReceiptTrace_successorGuard own ctx lists log pos constants pub digests fallback headerFallback p row ha s t g hg,
            hoff s t g hg (heq.trans hs)]
          grind only
        · rw [if_neg heq];grind only
      | some b =>
        have hpos : pos+1<2^log := by have hh := (List.getElem?_eq_some_iff.mp hb).1;omega
        have ht : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).height 0=2^log := rfl
        rcases planned_neighbors_indexed lists hw a b (neighbors_of_get _ a b pos ha hb) with
          ⟨p,_,hp⟩|⟨p,q,hpq,hp,hq,_⟩
        · obtain ⟨row,_,hl,hi,hea,_⟩ := p.neighbors a b hp
          rw [hea,p.erase_wrap] at hend;omega
        · obtain ⟨row,hs,hl,hi,hea⟩ := p.last a hp
          have heb := q.head b hq
          subst a b
          rw [hc s hsc]
          simp only [ha,p.erase_wrap]
          rw [control_state row hstates.1]
          by_cases heq : s=row.state
          · rw [if_pos heq,booleanReceiptTrace_successorGuard own ctx lists log pos constants pub digests fallback headerFallback p row ha s t g hg]
            rcases plannedSegments_successor lists p q hpq s t g hg (heq.trans hs) with hz|heq
            · rw [hz];grind only
            · have hn := booleanReceiptTrace_control own ctx lists log (pos+1) constants pub digests fallback headerFallback t htc
              rw [ht,Nat.mod_eq_of_lt hpos,hn]
              simp only [hb,q.erase_wrap]
              rw [control_state _ hstates.2]
              simp only [heq,ite_true]
              grind only
          · rw [if_neg heq];grind only
    · rw [hc fe (by decide),ha]
      simp only [controlCell,fe,idx,act,fs,↓reduceIte,if_neg hend]
      grind only

theorem successorConstraints_count : successorConstraints.length=22 := by decide

theorem successorConstraints_in_states : ∀e∈successorConstraints,e∈cStates := by
  intro e he
  simp only [cStates,List.mem_append]
  simp_all [successorConstraints]

theorem booleanReceiptTrace_structural_checkpoint (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length<2^log)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀pos,pos<2^log→∀e∈cRegs++cEmit++booleanConstraints++continuationConstraints++lastIndexConstraints++boundaryResetConstraints++successorConstraints,
      e.eval (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro pos hp e he
  rcases List.mem_append.mp he with he|he
  · rcases List.mem_append.mp he with he|he
    · exact booleanReceiptTrace_regs_emit_bool_continuation_lastIndex own ctx lists hw log constants pub digests fallback headerFallback (Nat.le_of_lt hcap) hown pos hp e he
    · exact booleanReceiptTrace_boundaryReset own ctx lists hw log pos constants pub digests fallback headerFallback hcap e he
  · exact booleanReceiptTrace_successors own ctx lists hw log pos constants pub digests fallback headerFallback hcap e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
