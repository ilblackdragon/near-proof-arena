import ZkFormal.NearV3.Assembly.RcptSystemTrafficRows

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem booleanReceiptTrace_systemTraffic (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length≤2^log) (sd : Bool) :
    let tr := booleanReceiptTrace own ctx lists log constants pub digests (systemAux fallback) (systemHeaderAux headerFallback)
    (List.range (tr.height 0)).flatMap (fun pos=>rowTraffic RcptV3.interactions tr 0 pos pub B_SREC sd)=
      ((plannedRows lists).flatMap (systemPlannedMessages sd)).map Msg.toFp := by
  let tr := booleanReceiptTrace own ctx lists log constants pub digests (systemAux fallback) (systemHeaderAux headerFallback)
  change (List.range (2^log)).flatMap (fun pos=>rowTraffic RcptV3.interactions tr 0 pos pub B_SREC sd)=_
  have hh (pos : Nat) : rowTraffic RcptV3.interactions tr 0 pos pub B_SREC sd=
      (match (plannedRows lists)[pos]? with | some a=>(systemPlannedMessages sd a).map Msg.toFp | none=>[]) := by
    cases ha : (plannedRows lists)[pos]? with
    | none => exact system_padding_traffic own ctx lists log pos constants pub digests fallback headerFallback ha sd
    | some a =>
      cases a with
      | header p row => exact system_header_row_traffic own ctx lists log pos constants pub digests fallback headerFallback p row ha sd
      | receipt p row => exact system_receipt_row_traffic own ctx lists log pos constants pub digests fallback headerFallback p row ha sd
  rw [show (fun pos=>rowTraffic RcptV3.interactions tr 0 pos pub B_SREC sd)=
      (fun pos=>match (plannedRows lists)[pos]? with | some a=>(systemPlannedMessages sd a).map Msg.toFp | none=>[]) from funext hh]
  have hp := range_get_flatMap (2^log) (plannedRows lists) (fun a=>(systemPlannedMessages sd a).map Msg.toFp) hcap
  rw [List.map_flatMap]
  apply Eq.trans ?_ hp
  apply congrArg (fun f : Nat→List (List Fp)=>(List.range (2^log)).flatMap f)
  funext i
  cases (plannedRows lists)[i]? <;> rfl


theorem booleanReceiptTrace_systemBalance (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (hcap : (plannedRows lists).length≤2^log) :
    let tr := booleanReceiptTrace own ctx lists log constants pub digests (systemAux fallback) (systemHeaderAux headerFallback)
    (List.range (tr.height 0)).flatMap (fun pos=>rowTraffic RcptV3.interactions tr 0 pos pub B_SREC true)=
      (List.range (tr.height 0)).flatMap (fun pos=>rowTraffic RcptV3.interactions tr 0 pos pub B_SREC false) := by
  dsimp only
  rw [booleanReceiptTrace_systemTraffic own ctx lists log constants pub digests fallback headerFallback hcap true,
    booleanReceiptTrace_systemTraffic own ctx lists log constants pub digests fallback headerFallback hcap false,
    system_planned_balance]

end ZkFormal.NearV3.Assembly.RcptSkeleton
