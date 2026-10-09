import ZkFormal.NearV3.Assembly.RcptSystemTrafficPlan

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem receipt_receiver_byte (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (p : ReceiptPlan) (row : Coord) (hs : row.state=sV) :
    receiptCell constants (streamAux pub digests fallback) p row b=
      Fp.ofNat ((p.input.receipt.receiverId.getD row.index 0).toNat) := by
  rw [receipt_stream_byte,hs,if_neg (show sV∉regStates by decide)]
  simp only [nativeFieldByte,hs,sV,sP,Nat.reduceEqDiff,↓reduceIte]

theorem system_receipt_row_traffic (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (.receipt p row)) (sd : Bool) :
    rowTraffic RcptV3.interactions
      (booleanReceiptTrace own ctx lists log constants pub digests (systemAux fallback) (systemHeaderAux headerFallback))
      0 pos pub B_SREC sd=(systemRowMessages p row sd).map Msg.toFp := by
  let tr := booleanReceiptTrace own ctx lists log constants pub digests (systemAux fallback) (systemHeaderAux headerFallback)
  change rowTraffic RcptV3.interactions tr 0 pos pub B_SREC sd=_
  have hc := booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
    (systemAux fallback) (systemHeaderAux headerFallback) _ ha
  have hr : tr.cell 0 pos RcptV3.r=Fp.ofNat p.receiptIndex := hc RcptV3.r (by decide)
  have hi : tr.cell 0 pos idx=Fp.ofNat row.index := hc idx (by decide)
  have hfields := systemAux_transport ctx lists constants pub digests fallback p row
  rw [RcptV3Proof.rowT_srec]
  cases sd with
  | true =>
    have hg : tr.cell 0 pos gV=bitCell (row.state==sV && systemLookup p.input.receipt row.index) :=
      (hc gV (by decide)).trans (hfields gV (by decide))
    simp only [ite_true,hg,system_gt_bit,systemRowMessages]
    by_cases hh : (row.state==sV && systemLookup p.input.receipt row.index)=true
    · have hs : row.state=sV := by simpa only [beq_iff_eq] using (Bool.and_eq_true_iff.mp hh).1
      have hb : tr.cell 0 pos b=Fp.ofNat ((p.input.receipt.receiverId.getD row.index 0).toNat) :=
        (hc b (by decide)).trans (receipt_receiver_byte (booleanConstants constants) pub digests
          (tokenAux (receiptPlanToken ctx lists) (booleanReceiptAux (systemAux fallback))) p row hs)
      simp only [hh,ite_true,hr,hi,hb,List.map_cons,List.map_nil,Msg.toFp]
    · simp only [hh,Bool.false_eq_true,ite_false,List.map_nil]
  | false =>
    have hg : tr.cell 0 pos gS=bitCell (row.state==sS && systemLookup p.input.receipt row.index) :=
      (hc gS (by decide)).trans (hfields gS (by decide))
    have hb : tr.cell 0 pos sx=Fp.ofNat ((p.input.receipt.receiverId.getD row.index 0).toNat) :=
      (hc sx (by decide)).trans (hfields sx (by decide))
    simp only [Bool.false_eq_true,ite_false,hg,system_gt_bit,systemRowMessages]
    by_cases hh : (row.state==sS && systemLookup p.input.receipt row.index)=true
    · simp only [hh,ite_true,hr,hi,hb,List.map_cons,List.map_nil,Msg.toFp]
    · simp only [hh,Bool.false_eq_true,ite_false,List.map_nil]

theorem system_header_row_traffic (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ListPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (.header p row)) (sd : Bool) :
    rowTraffic RcptV3.interactions
      (booleanReceiptTrace own ctx lists log constants pub digests (systemAux fallback) (systemHeaderAux headerFallback))
      0 pos pub B_SREC sd=[] := by
  rw [RcptV3Proof.rowT_srec]
  apply RcptV3Proof.gt_zero
  have hc := booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests
    (systemAux fallback) (systemHeaderAux headerFallback) _ ha
  cases sd with
  | true =>
    have hh := hc gV (by decide)
    apply hh.trans
    change boolInput gV 0=0
    exact boolInput_preserves _ _ (Or.inl rfl)
  | false =>
    have hh := hc gS (by decide)
    apply hh.trans
    change boolInput gS 0=0
    exact boolInput_preserves _ _ (Or.inl rfl)

theorem system_padding_traffic (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (ha : (plannedRows lists)[pos]?=none) (sd : Bool) :
    rowTraffic RcptV3.interactions
      (booleanReceiptTrace own ctx lists log constants pub digests (systemAux fallback) (systemHeaderAux headerFallback))
      0 pos pub B_SREC sd=[] := by
  rw [RcptV3Proof.rowT_srec]
  apply RcptV3Proof.gt_zero
  exact booleanReceiptTrace_padding own ctx lists log pos constants pub digests
    (systemAux fallback) (systemHeaderAux headerFallback) ha _

end ZkFormal.NearV3.Assembly.RcptSkeleton
