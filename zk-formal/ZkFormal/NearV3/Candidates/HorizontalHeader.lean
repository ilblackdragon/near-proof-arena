import ZkFormal.NearV3.Candidates.HorizontalPack
import ZkFormal.NearV3.Candidates.HorizontalCertified

namespace ZkFormal.NearV3.Candidates.HorizontalHeader
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ZkFormal.Near.Render
open HorizontalAccounts

def actualHeader (tr : Trace Fp) : List Nat := (List.range air.tables.length).map tr.log

set_option maxRecDepth 32768 in
theorem maxlog_cap : air.tables.all (fun T=>decide (T.maxLog≤22))=true := by decide +kernel

/-- Admission holds for the witness's actual clocks, not only the maximum
header used to certify the worst-case proof size. -/
theorem actual_header {tr : Trace Fp} {pub : List Fp} (h : Holds air pub tr) :
    ZkFormal.Stark.headerOk air (ZkFormal.V2.G.pg 2) (actualHeader tr)=true := by
  have hbl : 2^(ZkFormal.V2.G.pg 2).logBlowup=16 := rfl
  have hgr : (ZkFormal.V2.G.pg 2).auxGroup=2 := rfl
  simp only [ZkFormal.Stark.headerOk,actualHeader,List.length_map,List.length_range,
    beq_self_eq_true,Bool.true_and,hbl,hgr,HorizontalCertified.air_wf,
    HorizontalCertified.grouped_degree,Bool.and_true]
  rw [List.zip_map_right,zip_range_getD MerkleEmpty.table]
  simp only [List.map_map,List.all_map]
  apply List.all_eq_true.mpr
  intro i hi
  have hil := List.mem_range.mp hi
  have hb := h.logBound i hil
  have hm := of_decide_eq_true (List.all_eq_true.mp maxlog_cap air.tables[i] (List.getElem_mem hil))
  have hg : air.tables.getD i MerkleEmpty.table=air.tables[i] := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hil]; rfl
  simp only [Function.comp_apply,Prod.map,hg,Bool.and_eq_true,decide_eq_true_eq]
  have hc1 : 22+(ZkFormal.V2.G.pg 2).logBlowup≤(ZkFormal.V2.G.pg 2).maxLogLde := by decide
  have hc2 : 22+(ZkFormal.V2.G.pg 2).logBlowup≤(ZkFormal.V2.G.pg 2).posBits := by decide
  exact ⟨⟨⟨hb.1,hb.2⟩,by omega⟩,by omega⟩

end ZkFormal.NearV3.Candidates.HorizontalHeader
