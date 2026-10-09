import ZkFormal.NearV3.Assembly.RcptNamedEnd

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render.RcptP ZkFormal.Near.Render.RcptGen

theorem booleanReceiptTrace_hex (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (ha : (plannedRows lists)[pos]?=some (.receipt p row))
    (hw : p.input.receipt.wf=true) (hs : row.state∈[sP,sV,sS])
    (hi : row.index<fieldLen p.input row.state) :
    hexE.eval (booleanReceiptTrace own ctx lists log constants pub digests (characterAux fallback)
      (characterHeaderAux headerFallback)) 0 pos pub=bitCell (isHexC (characterByte p row)) := by
  have hchar := character_receipt_cells ctx lists constants pub digests fallback p row hs
  have hh3 := hchar 112 (by decide)
  have hhx6 := hchar 123 (by decide)
  have hc (col : Nat) (hcol : emissionColumn col=false) := booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
    (characterAux fallback) (characterHeaderAux headerFallback) _ ha col hcol
  simp only [hexE,eval_add,eval_c]
  rw [hc _ (by decide),hc _ (by decide)]
  change receiptCell _ _ p row 112+receiptCell _ _ p row 123=_
  rw [hh3,hhx6]
  have hn := hex_char (characterByte p row) (characterByte_lt p row) (characterByte_valid p row hw hs hi)
  have hf := congrArg (fun n : Nat=>(n:Fp)) hn
  change ((ZkFormal.Near.Render.RcptGen.charCell (characterByte p row) 112:Nat):Fp)+
    ((ZkFormal.Near.Render.RcptGen.charCell (characterByte p row) 123:Nat):Fp)=_
  have hb : ((ZkFormal.Near.Render.RcptGen.b2n (isHexC (characterByte p row))):Fp)=bitCell (isHexC (characterByte p row)) := by
    cases isHexC (characterByte p row) <;> rfl
  rw [←hb]
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
