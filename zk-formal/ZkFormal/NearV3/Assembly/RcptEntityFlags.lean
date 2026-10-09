import ZkFormal.NearV3.Assembly.RcptEntityCells

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem booleanReceiptTrace_planned_cell (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (a : PlannedRow)
    (ha : (plannedRows lists)[pos]?=some a) (col : Nat) (hcol : emissionColumn col=false) :
    (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos col=
      plannedCell (booleanConstants constants)
        (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux fallback))
        (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt))
          (emissionHeaderFallback (booleanHeaderAux headerFallback))) a col := by
  unfold booleanReceiptTrace emittedReceiptTrace
  rw [emissionPatch_other _ _ _ _ _ col hcol]
  exact plannedTrace_cell lists log pos _ _ _ _ ha col

structure EntityStartFlags (tr : Trace Fp) (pos : Nat) (p : EntityPlan) : Prop where
  active : tr.cell 0 pos act=1
  firstReceipt : tr.cell 0 pos rf=bitCell (!p.isHeader)
  predecessor : tr.cell 0 pos sPL=bitCell (!p.isHeader)
  header : tr.cell 0 pos sCL=bitCell p.isHeader

structure EntityEndFlags (tr : Trace Fp) (pos : Nat) (pub : List Fp) (p : EntityPlan) : Prop where
  active : tr.cell 0 pos act=1
  header : tr.cell 0 pos sCL=bitCell p.isHeader
  lastReceipt : tr.cell 0 pos rl=bitCell (!p.isHeader)
  boundary : brkE.eval tr 0 pos pub=1
  listEnd : tr.cell 0 pos le=bitCell p.lastInList
  activeEnd : tr.cell 0 pos lastR=bitCell (p.lastInList && p.lastList)

structure EntityInsideFlags (tr : Trace Fp) (pos : Nat) (pub : List Fp) (p : EntityPlan) : Prop where
  active : tr.cell 0 pos act=1
  header : tr.cell 0 pos sCL=bitCell p.isHeader
  lastReceipt : tr.cell 0 pos rl=0
  boundary : brkE.eval tr 0 pos pub=0
  listEnd : tr.cell 0 pos le=0
  activeEnd : tr.cell 0 pos lastR=0

def EntityWf : EntityPlan→Prop
  | .header _=>True
  | .receipt p=>p.input.receipt.wf=true

theorem entityPlans_wf (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (p : EntityPlan) (hp : p∈entityPlans lists) : EntityWf p := by
  cases p with
  | header => trivial
  | receipt rp => exact entityPlans_receipt_wf lists hw rp hp

theorem booleanReceiptTrace_entityStart (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : EntityPlan)
    (ha : (plannedRows lists)[pos]?=some p.firstRow) :
    EntityStartFlags (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) pos p := by
  have hc := booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests fallback headerFallback p.firstRow ha
  cases p with
  | header lp => exact ⟨hc act (by decide),hc rf (by decide),hc sPL (by decide),hc sCL (by decide)⟩
  | receipt rp => exact ⟨hc act (by decide),hc rf (by decide),hc sPL (by decide),hc sCL (by decide)⟩

theorem booleanReceiptTrace_entityEnd (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : EntityPlan) (a : PlannedRow)
    (ha : (plannedRows lists)[pos]?=some a) (hw : EntityWf p) (hend : p.rows.getLast?=some a) :
    EntityEndFlags (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) pos pub p := by
  cases p with
  | header lp =>
    have he := EntityPlan.header_last lp a hend
    subst a
    have hc := booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests fallback headerFallback _ ha
    refine ⟨hc act (by decide),hc sCL (by decide),hc rl (by decide),?_,?_,?_⟩
    · simp only [brkE,lhEnd,eval_add,eval_mul,eval_c,hc rl (by decide),hc sCL (by decide),hc fe (by decide)]
      change (0:Fp)+1*1=1;grind only
    · rw [hc le (by decide)]
      rfl
    · rw [hc lastR (by decide)]
      rfl
  | receipt rp =>
    obtain ⟨row,hs,he,hea⟩ := EntityPlan.receipt_last rp hw a hend
    subst a
    have hc := booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests fallback headerFallback _ ha
    have hr : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos rl=1 := by
      rw [hc rl (by decide)]
      change bitCell (receiptEnd rp row)=1
      rw [terminal_receiptEnd rp row hs he];rfl
    have hh := booleanReceiptTrace_receipt_not_header own ctx lists log pos constants pub digests fallback headerFallback rp row ha
    refine ⟨hc act (by decide),hh,hr,?_,?_,?_⟩
    · simp only [brkE,lhEnd,eval_add,eval_mul,eval_c,hr,hh];grind only
    · rw [hc le (by decide)]
      change bitCell (receiptEnd rp row && rp.lastInList)=bitCell rp.lastInList
      rw [terminal_receiptEnd rp row hs he,Bool.true_and]
    · rw [hc lastR (by decide)]
      change bitCell (receiptEnd rp row && rp.lastInList && rp.lastList)=bitCell (rp.lastInList && rp.lastList)
      rw [terminal_receiptEnd rp row hs he,Bool.true_and]

theorem booleanReceiptTrace_entityInside (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : EntityPlan) (a : PlannedRow)
    (ha : (plannedRows lists)[pos]?=some a) (hi : EntityInside p a) :
    EntityInsideFlags (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) pos pub p := by
  cases p with
  | header lp =>
    obtain ⟨row,rfl,hi⟩ := hi
    have hc := booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests fallback headerFallback _ ha
    have hshape : row.state=sCL ∧ row.length=12 := by
      have hm := List.mem_of_getElem? ha
      rw [←plannedSegments_rows] at hm
      obtain ⟨seg,_,hm⟩ := List.mem_flatMap.mp hm
      obtain ⟨r,hr,he⟩ := List.mem_map.mp hm
      obtain ⟨hs,_,hl⟩ := segment_member hr
      cases seg with
      | receipt => cases he
      | header p => cases he;exact ⟨hs,hl⟩
    have hh : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos sCL=1 := by
      rw [booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback sCL (by decide)]
      simp only [ha,eraseRow]
      rw [control_state row (by decide : sCL∈states)]
      simp only [hshape.1,ite_true]
    have hf : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos fe=0 := by
      rw [booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback fe (by decide)]
      simp [ha,eraseRow,controlCell,fe,idx,act,fs,hshape.2,show row.index+1≠12 by omega]
    refine ⟨hc act (by decide),hh,hc rl (by decide),?_,?_,?_⟩
    · simp only [brkE,lhEnd,eval_add,eval_mul,eval_c,hc rl (by decide),hh,hf]
      change (0:Fp)+1*0=0;grind only
    · rw [hc le (by decide)]
      change bitCell (row.index+1==12 && lp.inputs.isEmpty)=0
      simp [bitCell,show row.index≠11 by omega]
    · rw [hc lastR (by decide)]
      change bitCell (row.index+1==12 && lp.inputs.isEmpty && lp.lastList)=0
      simp [bitCell,show row.index≠11 by omega]
  | receipt rp =>
    obtain ⟨row,rfl,hi⟩ := hi
    have hc := booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests fallback headerFallback _ ha
    have hh := booleanReceiptTrace_receipt_not_header own ctx lists log pos constants pub digests fallback headerFallback rp row ha
    have hr : (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos rl=0 := by
      rw [hc rl (by decide)];change bitCell (receiptEnd rp row)=0;rw [hi];rfl
    refine ⟨hc act (by decide),hh,hr,?_,?_,?_⟩
    · simp only [brkE,lhEnd,eval_add,eval_mul,eval_c,hr,hh];grind only
    · rw [hc le (by decide)];change bitCell (receiptEnd rp row && rp.lastInList)=0;rw [hi];rfl
    · rw [hc lastR (by decide)];change bitCell (receiptEnd rp row && rp.lastInList && rp.lastList)=0;rw [hi];rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
