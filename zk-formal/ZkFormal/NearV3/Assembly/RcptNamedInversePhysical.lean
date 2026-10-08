import ZkFormal.NearV3.Assembly.RcptNamedFrame

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

def namedInverseConstraints : List Expr :=
  [mul3 (c sV) (c fe) (sub (.mul (c p1) (c i1)) (k 1)),
   mul3 (c sV) (c fe) (sub (.mul (c p2) (c i2)) (k 1)),
   mul3 (c sV) (c fe) (sub (.mul (c p3) (c i3)) (k 1))]

theorem namedInverse_in_chars : ∀e∈namedInverseConstraints,e∈cChars := by
  intro e he
  simp only [namedInverseConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cChars,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

theorem namedInverse_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : tr.cell 0 pos sV=0) : ∀e∈namedInverseConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [namedInverseConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl <;> simp only [eval_mul3,eval_c,hz] <;> grind only

set_option maxRecDepth 4096 in
theorem booleanReceiptTrace_namedInverse (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true)
    (hn : ∀xs∈lists,∀x∈xs,AccountId.isNamed x.receipt.receiverId=true)
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) :
    ∀e∈namedInverseConstraints,e.eval
      (booleanReceiptTrace own ctx lists log constants pub digests (namedAux fallback) headerFallback) 0 pos pub=0 := by
  let tr := booleanReceiptTrace own ctx lists log constants pub digests (namedAux fallback) headerFallback
  change ∀e∈namedInverseConstraints,e.eval tr 0 pos pub=0
  have hc := booleanReceiptTrace_control own ctx lists log pos constants pub digests (namedAux fallback) headerFallback
  cases ha : (plannedRows lists)[pos]? with
  | none =>
    exact namedInverse_zero tr pos pub
      (booleanReceiptTrace_padding own ctx lists log pos constants pub digests (namedAux fallback) headerFallback ha sV)
  | some a =>
    have hstate := hc sV (by decide)
    rw [ha] at hstate
    dsimp only at hstate
    by_cases hs : (eraseRow a).state=sV
    · cases a with
      | header p row =>
        have hm := List.mem_of_getElem? ha
        rw [←plannedSegments_rows] at hm
        obtain ⟨seg,_,hm⟩ := List.mem_flatMap.mp hm
        obtain ⟨c,hc,he⟩ := List.mem_map.mp hm
        have hh := (segment_member hc).1
        cases seg <;> cases he
        change row.state=sCL at hh
        simp only [eraseRow] at hs
        rw [hh] at hs
        contradiction
      | receipt p row =>
        change row.state=sV at hs
        have hmem := planned_receipt_input_mem lists p row (List.mem_of_getElem? ha)
        obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp hmem
        have hv : AccountId.valid p.input.receipt.receiverId=true := by
          have hh := hw xs hxs p.input hx
          simp only [Receipt.wf,Bool.and_eq_true] at hh
          grind only
        have hi := character_named_inverses p.input.receipt hv (hn xs hxs p.input hx)
        have hcells : ∀col,col∈[p1,p2,p3,i1,i2,i3]→tr.cell 0 pos col=namedAux fallback p row col := by
          intro col hh
          have hall : col∈[acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3] := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hh ⊢
            grind only
          have hem : emissionColumn col=false := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
            rcases hh with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
          exact (booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
            (namedAux fallback) headerFallback _ ha col hem).trans
              (namedAux_transport ctx lists constants pub digests fallback p row col hall)
        intro e he
        simp only [namedInverseConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
        rcases he with rfl|rfl|rfl
        all_goals
          simp only [eval_mul3,eval_sub,eval_mul,eval_c,eval_k]
          first
          | rw [hcells p1 (by decide),hcells i1 (by decide)]
          | rw [hcells p2 (by decide),hcells i2 (by decide)]
          | rw [hcells p3 (by decide),hcells i3 (by decide)]
          simp only [namedAux,hs,acc,vc0,vc1,h01,p1,p2,p3,i1,i2,i3,Nat.reduceEqDiff,↓reduceIte]
          grind only

    · apply namedInverse_zero
      exact hstate.trans (by rw [control_state _ (by decide),if_neg (Ne.symm hs)])

end ZkFormal.NearV3.Assembly.RcptSkeleton
