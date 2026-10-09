import ZkFormal.NearV3.Assembly.RcptSegmentTokenBytes

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3

/-- The shared concrete row assignment already used by physical cRegs proofs. -/
def nativePlannedCell (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp) :
    PlannedRow→Nat→Fp :=
  plannedCell constants (tokenReceiptAux pub digests (receiptPlanToken ctx lists) fallback)
    (headerStreamAux own (headerBurn ctx (lists.flatten.map Input.receipt)) headerFallback)

theorem segment_first_token_cell (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : SegmentPlan) (hp : p∈plannedSegments lists) (j : Nat) (hj : j<16) :
    nativePlannedCell own ctx lists constants pub digests fallback headerFallback
      (p.wrap ⟨p.state,0,p.length⟩) (tok j)=
      Fp.ofNat (((u128 (prefixBurn ctx (lists.flatten.map Input.receipt) 0 p.startIndex)).getD j 0).toNat) := by
  cases p with
  | header lp =>
    change headerCell _ lp _ (tok j)=_
    rw [header_stream_token _ _ _ _ _ _ hj]
    simp only [headerBurn,prefixBurn,SegmentPlan.startIndex,Nat.zero_add]
  | receipt rp s =>
    change receiptCell _ _ rp _ (tok j)=_
    rw [receipt_token_cell _ _ _ _ _ _ _ _ hj]
    exact congrArg (fun b=>Fp.ofNat b.toNat) (receipt_segment_first_token ctx lists rp s j hj hp)

theorem segment_end_token_cell (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p : SegmentPlan) (hp : p∈plannedSegments lists) (i j : Nat) (hj : j<16) (hs : p.state≠sGP) :
    nativePlannedCell own ctx lists constants pub digests fallback headerFallback
      (p.wrap ⟨p.state,i,p.length⟩) (tok j)=
      Fp.ofNat (((u128 (prefixBurn ctx (lists.flatten.map Input.receipt) 0 p.endIndex)).getD j 0).toNat) := by
  cases p with
  | header lp =>
    change headerCell _ lp _ (tok j)=_
    rw [header_stream_token _ _ _ _ _ _ hj]
    simp only [headerBurn,prefixBurn,SegmentPlan.endIndex,Nat.zero_add]
  | receipt rp s =>
    change receiptCell _ _ rp _ (tok j)=_
    rw [receipt_token_cell _ _ _ _ _ _ _ _ hj]
    exact congrArg (fun b=>Fp.ofNat b.toNat) (receipt_segment_end_token ctx lists rp s i _ j hs hp)

theorem SegmentPlan.head (p : SegmentPlan) (a : PlannedRow)
    (h : p.rows.head?=some a) : a=p.wrap ⟨p.state,0,p.length⟩ := by
  simp only [SegmentPlan.rows,List.head?_map] at h
  obtain ⟨row,hr,ha⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hs,hl,hi⟩ := segment_head p.state p.length row hr
  have he : row=⟨p.state,0,p.length⟩ := by cases row; simp_all
  simpa only [he] using ha.symm

/-- Every non-GP physical segment boundary has identical token bytes, including
receipt-to-header and empty-list-header transitions. -/
theorem segment_boundary_token_cells (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (constants : ReceiptPlan→Nat→Fp) (pub : List Fp) (digests : ReceiptPlan→Nat→List Fp)
    (fallback : ReceiptPlan→Coord→Nat→Fp) (headerFallback : ListPlan→Coord→Nat→Fp)
    (p q : SegmentPlan) (hpq : Neighbors (plannedSegments lists) p q)
    (a b : PlannedRow) (ha : p.rows.getLast?=some a) (hb : q.rows.head?=some b)
    (hs : p.state≠sGP) (j : Nat) (hj : j<16) :
    nativePlannedCell own ctx lists constants pub digests fallback headerFallback b (tok j)=
    nativePlannedCell own ctx lists constants pub digests fallback headerFallback a (tok j) := by
  obtain ⟨hp,hq⟩ := List.of_mem_zip hpq
  have hq' : q∈plannedSegments lists := List.mem_of_mem_drop hq
  obtain ⟨row,hstate,hlen,_,hrow⟩ := p.last a ha
  have he : row=⟨p.state,row.index,p.length⟩ := by cases row; simp_all
  rw [q.head b hb,hrow,he]
  rw [segment_first_token_cell _ _ _ _ _ _ _ _ q hq' j hj,
    segment_end_token_cell _ _ _ _ _ _ _ _ p hp _ j hj hs,
    plannedSegments_neighbor_indices lists p q hpq]

end ZkFormal.NearV3.Assembly.RcptSkeleton
