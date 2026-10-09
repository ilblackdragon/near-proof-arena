import ZkFormal.NearV3.Assembly.RcptStateReceiptContinuity

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

def receiptCarryConstraints : List Expr :=
  rconsts.map (fun col=>mul3 rowE (Dsl.not (c rl)) (sub (n col) (c col)))

theorem receiptCarryConstraints_footprint : receiptCarryConstraints.all noEmissionExpr=true := by decide

theorem receiptCarry_header (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (p : ListPlan) (row : Coord) (aux : ListPlan→Coord→Nat→Fp)
    (hs : row.state=sCL) (hc : ∀col,tr.cell 0 pos col=headerCell aux p row col) :
    ∀e∈receiptCarryConstraints,e.eval tr 0 pos pub=0 := by
  have hrow : rowE.eval tr 0 pos pub=0 := by
    simp only [rowE,eval_sub,eval_c,hc]
    rw [header_control_cell _ _ _ (by decide : controlColumn act=true),
      header_control_cell _ _ _ (by decide : controlColumn sCL=true),control_state row (by decide : sCL∈states)]
    simp only [hs,ite_true]
    change (1:Fp)-1=0;grind only
  intro e he
  obtain ⟨col,_,rfl⟩ := List.mem_map.mp he
  simp only [eval_mul3,hrow];grind only

theorem receiptCarry_terminal (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (p : ReceiptPlan) (row : Coord) (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp)
    (hs : row.state=finalState p.input) (hend : row.index+1=row.length)
    (hc : ∀col,tr.cell 0 pos col=receiptCell constants aux p row col) :
    ∀e∈receiptCarryConstraints,e.eval tr 0 pos pub=0 := by
  have hrl : tr.cell 0 pos rl=1 := by
    rw [hc rl]
    change bitCell (receiptEnd p row)=1
    rw [terminal_receiptEnd p row hs hend];rfl
  intro e he
  obtain ⟨col,_,rfl⟩ := List.mem_map.mp he
  simp only [eval_mul3,eval_not,eval_c,hrl];grind only

theorem receiptCarry_same (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (p : ReceiptPlan) (row next : Coord) (constants : ReceiptPlan→Nat→Fp) (aux : ReceiptPlan→Coord→Nat→Fp)
    (hc : ∀col,tr.cell 0 pos col=receiptCell constants aux p row col)
    (hn : ∀col,tr.cell 0 ((pos+1)%tr.height 0) col=receiptCell constants aux p next col) :
    ∀e∈receiptCarryConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  obtain ⟨col,hcol,rfl⟩ := List.mem_map.mp he
  simp only [eval_mul3,eval_sub,eval_n,eval_c,hc,hn]
  rw [receipt_constants_carry constants aux p row next hcol]
  grind only

theorem plannedTrace_receiptCarry (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (receiptAux : ReceiptPlan→Coord→Nat→Fp)
    (headerAux : ListPlan→Coord→Nat→Fp) (pub : List Fp)
    (hcap : (plannedRows lists).length<2^log) :
    ∀e∈receiptCarryConstraints,e.eval (plannedTrace lists log constants receiptAux headerAux) 0 pos pub=0 := by
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    intro e he
    obtain ⟨col,_,rfl⟩ := List.mem_map.mp he
    have hc := plannedTrace_padding lists log pos constants receiptAux headerAux (List.getElem?_eq_none_iff.mp ha)
    simp only [eval_mul3,rowE,eval_sub,eval_c,hc]
    grind only
  | some a =>
    have hc := plannedTrace_cell lists log pos constants receiptAux headerAux a ha
    have hpos : pos+1<2^log := by have hh := (List.getElem?_eq_some_iff.mp ha).1;omega
    have ht : (plannedTrace lists log constants receiptAux headerAux).height 0=2^log := rfl
    cases hb : (plannedRows lists)[pos+1]? with
    | none =>
      have hlast : (plannedRows lists).getLast?=some a := by
        have hh := (List.getElem?_eq_some_iff.mp ha).1
        have hn := List.getElem?_eq_none_iff.mp hb
        rw [List.getLast?_eq_getElem?,show (plannedRows lists).length-1=pos by omega]
        exact ha
      obtain ⟨p,hp,hplast⟩ := planned_last_final_segment lists hw a hlast
      obtain ⟨row,hs,hl,hi,hea⟩ := p.last a hplast
      subst a
      cases p with
      | header lp => exact receiptCarry_header _ pos pub lp row headerAux hs hc
      | receipt rp s =>
        obtain ⟨_,_,hfinal⟩ := hp
        exact receiptCarry_terminal _ pos pub rp row constants receiptAux (hs.trans hfinal) (by omega) hc
    | some b =>
      have hn := plannedTrace_cell lists log (pos+1) constants receiptAux headerAux b hb
      have hn' : ∀col,(plannedTrace lists log constants receiptAux headerAux).cell 0
          ((pos+1)%(plannedTrace lists log constants receiptAux headerAux).height 0) col=plannedCell constants receiptAux headerAux b col := by
        simpa only [ht,Nat.mod_eq_of_lt hpos] using hn
      rcases planned_neighbors_indexed lists hw a b (neighbors_of_get _ a b pos ha hb) with
        ⟨p,_,hp⟩|⟨p,q,hpq,hp,hq,_⟩
      · obtain ⟨row,hs,_,_,hea,heb⟩ := p.neighbors a b hp
        subst a b
        cases p with
        | header lp => exact receiptCarry_header _ pos pub lp row headerAux hs hc
        | receipt rp s => exact receiptCarry_same _ pos pub rp row (advance row) constants receiptAux hc hn'
      · obtain ⟨row,hs,hl,hi,hea⟩ := p.last a hp
        have heb := q.head b hq
        subst a b
        have hcont := plannedSegments_continues lists p q hpq
        cases p with
        | header lp => exact receiptCarry_header _ pos pub lp row headerAux hs hc
        | receipt rp s =>
          rcases hcont with hfinal|⟨t,rfl⟩
          · exact receiptCarry_terminal _ pos pub rp row constants receiptAux (hs.trans hfinal) (by omega) hc
          · exact receiptCarry_same _ pos pub rp row ⟨t,0,fieldLen rp.input t⟩ constants receiptAux hc hn'

theorem receiptCarryConstraints_count : receiptCarryConstraints.length=21 := by decide

theorem receiptCarryConstraints_in_states : ∀e∈receiptCarryConstraints,e∈cStates := by
  intro e he
  simp only [cStates,List.mem_append]
  simp_all [receiptCarryConstraints]

theorem booleanReceiptTrace_receiptCarry (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (log pos : Nat)
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (hcap : (plannedRows lists).length<2^log) :
    ∀e∈receiptCarryConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pos pub=0 := by
  intro e he
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_eval _ _ _ _ _ _ (List.all_eq_true.mp receiptCarryConstraints_footprint e he)]
  exact plannedTrace_receiptCarry lists hw log pos _ _ _ pub hcap e he

end ZkFormal.NearV3.Assembly.RcptSkeleton
