import ZkFormal.NearV3.Assembly.RcptEntityInterior

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

structure EntityCells (tr : Trace Fp) (pos : Nat) (p : EntityPlan) : Prop where
  listIndex : tr.cell 0 pos j=Fp.ofNat p.listIndex
  listCount : tr.cell 0 pos nj=Fp.ofNat p.listCount
  receiptIndex : tr.cell 0 pos r=Fp.ofNat p.receiptIndex
  withinList : tr.cell 0 pos cj=Fp.ofNat p.withinList
  rcEnd : tr.cell 0 pos oEnd=Fp.ofNat p.rcEnd
  bodyStart : tr.cell 0 pos o2=Fp.ofNat p.bodyStart
  bodyEnd : tr.cell 0 pos o2End=Fp.ofNat p.bodyEnd
  rcStart : p.isHeader=false→tr.cell 0 pos o=Fp.ofNat p.rcStart

theorem EntityPlan.row_member (p : EntityPlan) (a : PlannedRow) (ha : a∈p.rows) :
    match p with
    | .header lp=>∃row,a=.header lp row
    | .receipt rp=>∃row,a=.receipt rp row := by
  cases p with
  | header lp =>
    obtain ⟨row,_,he⟩ := List.mem_map.mp ha
    exact ⟨row,he.symm⟩
  | receipt rp =>
    obtain ⟨row,_,he⟩ := List.mem_map.mp ha
    exact ⟨row,he.symm⟩

theorem booleanReceiptTrace_entityCells (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : EntityPlan) (a : PlannedRow)
    (ha : (plannedRows lists)[pos]?=some a) (hpa : a∈p.rows) :
    EntityCells (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) pos p := by
  have hshape := p.row_member a hpa
  have hc (col : Nat) (hcol : emissionColumn col=false) :
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos col=
      plannedCell (booleanConstants constants)
        (tokenReceiptAux pub digests (receiptPlanToken ctx lists) (booleanReceiptAux fallback))
        (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt))
          (emissionHeaderFallback (booleanHeaderAux headerFallback))) a col := by
    unfold booleanReceiptTrace emittedReceiptTrace
    rw [emissionPatch_other _ _ _ _ _ col hcol]
    exact plannedTrace_cell lists log pos _ _ _ _ ha col
  cases p with
  | header lp =>
    obtain ⟨row,rfl⟩ := hshape
    exact ⟨hc j (by decide),hc nj (by decide),hc r (by decide),hc cj (by decide),hc oEnd (by decide),
      hc o2 (by decide),hc o2End (by decide),fun h=>by cases h⟩
  | receipt rp =>
    obtain ⟨row,rfl⟩ := hshape
    exact ⟨hc j (by decide),hc nj (by decide),hc r (by decide),hc cj (by decide),hc oEnd (by decide),
      hc o2 (by decide),hc o2End (by decide),fun _=>hc o (by decide)⟩

def listBoundaryConstraints : List Expr :=
  [mul3 brkE (n act) (Dsl.not (.add (n sPL) (n sCL))),
   sub (c le) (.mul brkE (Dsl.not (n rf))),
   sub (c lastR) (.mul (c le) (Dsl.not (n act))),
   mul3 (c le) (n act) (sub (n j) (.add (c j) (k 1))),
   .mul (n act) (.mul brkE (sub (n r) (.add (c r) (c rl)))),
   .mul (n rf) (.mul brkE (sub (n cj) (.add (c cj) (k 1)))),
   .mul (c le) (sub (c cj) (c nj)),
   .mul (n rf) (.mul brkE (sub (n o) (c oEnd))),
   .mul (n act) (.mul (.add (c sCL) (c rl)) (sub (n o2) (c o2End)))] ++
  lconsts.map (fun x=>mul3 (c act) (Dsl.not (c le)) (sub (n x) (c x)))

set_option maxRecDepth 4096 in
theorem listBoundaryConstraints_count : listBoundaryConstraints.length=11 := by decide

theorem listBoundaryConstraints_in_states : ∀e∈listBoundaryConstraints,e∈cStates := by
  intro e he
  simp only [listBoundaryConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cStates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
