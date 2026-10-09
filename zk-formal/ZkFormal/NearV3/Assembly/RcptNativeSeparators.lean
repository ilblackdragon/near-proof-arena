import ZkFormal.NearV3.Assembly.RcptCharacterLengthComposition

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render.RcptP

theorem characterByte_separator (p : ReceiptPlan) (row : Coord)
    (hw : p.input.receipt.wf=true) (hs : row.state∈[sP,sV,sS])
    (hi : row.index<fieldLen p.input row.state)
    (hsep : sepB (characterByte p row)=true) :
    row.index≠0 ∧ row.index+1<fieldLen p.input row.state ∧
      sepB (characterByte p (advance row))=false := by
  have hv := characterBytes_valid p.input hw row.state hs
  simp only [AccountId.valid,Bool.and_eq_true,decide_eq_true_eq] at hv
  have he (i : Nat) : ((ZkFormal.Near.Render.toNats (characterBytes p.input row.state)).getD i 0)=
      ((characterBytes p.input row.state).getD i 0).toNat := by
    simp only [ZkFormal.Near.Render.toNats,List.getD_eq_getElem?_getD,List.getElem?_map]
    cases (characterBytes p.input row.state)[i]? <;> rfl
  have hh := chars_spec (characterBytes p.input row.state) true hv.2 row.index
    (by rw [characterBytes_length p.input row.state hs];exact hi)
  have hse : sepB ((ZkFormal.Near.Render.toNats (characterBytes p.input row.state)).getD row.index 0)=true := by
    simpa only [he,characterByte] using hsep
  obtain ⟨hfirst,hlast,hnext⟩ := hh.2 hse
  refine ⟨?_,?_,?_⟩
  · intro hz;have hh:=hfirst hz;cases hh
  · simpa only [characterBytes_length p.input row.state hs] using hlast
  · simpa only [he,characterByte,advance] using hnext

theorem planned_receipt_next (lists : List (List Input)) (pos : Nat) (p : ReceiptPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (.receipt p row)) (hi : row.index+1<row.length) :
    (plannedRows lists)[pos+1]?=some (.receipt p (advance row)) := by
  cases hb : (plannedRows lists)[pos+1]? with
  | none =>
    obtain ⟨seg,_,r,_,hl,he,hea⟩ := planned_before_padding lists pos _ ha hb
    have hh := congrArg eraseRow hea
    rw [seg.erase_wrap] at hh
    change row=r at hh
    subst r
    omega
  | some b =>
    rcases planned_index_neighbor_shape lists pos _ b ha hb with
      ⟨seg,_,r,_,_,_,hea,heb⟩|⟨seg,r,_,hl,he,hea⟩
    · cases seg with
      | header => cases hea
      | receipt rp s =>
        change PlannedRow.receipt p row=PlannedRow.receipt rp r at hea
        cases hea
        simpa only [heb,SegmentPlan.wrap] using hb
    · have hh := congrArg eraseRow hea
      rw [seg.erase_wrap] at hh
      change row=r at hh
      subst r
      omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
