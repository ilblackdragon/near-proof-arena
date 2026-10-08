import ZkFormal.NearV3.Assembly.RcptNativeSeparators

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render.RcptP

theorem booleanReceiptTrace_separator (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (ha : (plannedRows lists)[pos]?=some (.receipt p row))
    (hw : p.input.receipt.wf=true) (hs : row.state∈[sP,sV,sS])
    (hi : row.index<fieldLen p.input row.state) :
    sepE.eval (booleanReceiptTrace own ctx lists log constants pub digests (characterAux fallback)
      (characterHeaderAux headerFallback)) 0 pos pub=bitCell (sepB (characterByte p row)) := by
  have hchar := character_receipt_cells ctx lists constants pub digests fallback p row hs
  have h2 := hchar 111 (by decide)
  have h5 := hchar 113 (by decide)
  have hc (col : Nat) (hcol : emissionColumn col=false) := booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
    (characterAux fallback) (characterHeaderAux headerFallback) _ ha col hcol
  simp only [sepE,eval_add,eval_c]
  rw [hc _ (by decide),hc _ (by decide)]
  change receiptCell _ _ p row 111+receiptCell _ _ p row 113=_
  rw [h2,h5]
  have hn := sep_char (characterByte p row) (characterByte_lt p row) (characterByte_valid p row hw hs hi)
  have hf := congrArg (fun n : Nat=>(n:Fp)) hn
  change ((ZkFormal.Near.Render.RcptGen.charCell (characterByte p row) 111:Nat):Fp)+
    ((ZkFormal.Near.Render.RcptGen.charCell (characterByte p row) 113:Nat):Fp)=_
  have hb : ((ZkFormal.Near.Render.RcptGen.b2n (sepB (characterByte p row))):Fp)=bitCell (sepB (characterByte p row)) := by
    cases sepB (characterByte p row) <;> rfl
  rw [←hb]
  grind only

def separatorConstraints : List Expr :=
  [.mul (mul3 SS (Dsl.not (c fe)) sepE) sepN,mul3 SS (c fs) sepE,mul3 SS (c fe) sepE]

theorem separatorConstraints_in_chars : ∀e∈separatorConstraints,e∈cChars := by
  intro e he
  simp only [separatorConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cChars,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

theorem separator_current_zero (tr : Trace Fp) (pos : Nat) (pub : List Fp)
    (hz : SS.eval tr 0 pos pub=0 ∨ sepE.eval tr 0 pos pub=0) :
    ∀e∈separatorConstraints,e.eval tr 0 pos pub=0 := by
  intro e he
  simp only [separatorConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl <;> simp only [eval_mul,eval_mul3]
  all_goals rcases hz with hz|hz <;> rw [hz] <;> grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
