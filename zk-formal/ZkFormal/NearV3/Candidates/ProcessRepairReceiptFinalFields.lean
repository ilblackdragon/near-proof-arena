import ZkFormal.NearV3.Candidates.ProcessRepairReceiptFinal
import ZkFormal.NearV3.Candidates.ProcessRepairReceiptNativeKey
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptFinalFields
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2

theorem member (ls:RcptV3Vs) {j:Nat} (hj:j<ls.length) {k:Nat} (hk:k<ls[j].rs.length):
    [baseR ls j+k,0,FK_VAL,(ls[j].rs[k]).kslot]∈rcptRecvs3 ls B_FINAL:=by
  simp only [rcptRecvs3,List.mem_flatMap]
  refine ⟨j,List.mem_range.mpr hj,?_⟩
  refine ⟨(baseR ls j+k,lOffs ls[j].rs k,ls[j].rs[k]),?_,?_⟩
  · simp only [located,List.mem_map]
    refine ⟨k,List.mem_range.mpr (by simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj] using hk),?_⟩
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,List.getElem?_eq_getElem hk]
  · simp [rRecvs,show B_FINAL≠B_DIGEST by decide]

theorem fields {ws:List WalkR} (hW:WalkWf3 ws) {w:WalkR} (hw:w∈ws)
    {r k:Nat} (hr:r<P) (hk:k<P)
    (he:Msg.toFp [w.w,w.tau,w.fk,w.k]=Msg.toFp [r,0,FK_VAL,k]):
    w.w=r ∧ w.tau=0 ∧ w.fk=FK_VAL ∧ w.k=k:=by
  have hc:=hW.canon w hw
  have hlen:=hW.len w hw
  have hlast:=hc.2.2 w.last (Walk3.row_mem (by omega))
  have hfk:w.fk<P:=by unfold WalkR.fk;split <;>decide
  have hval:w.k<P:=by
    unfold WalkR.k
    split
    · exact Link.getD_lt hlast.2.2.2 _
    · unfold P;omega
  simp only [Msg.toFp,List.map_cons,List.map_nil,List.cons.injEq] at he
  exact ⟨Link.ofNat_inj hc.1 hr he.1,Link.ofNat_inj hc.2.1 (by decide) he.2.1,
    Link.ofNat_inj hfk (by decide) he.2.2.1,Link.ofNat_inj hval hk he.2.2.2.1⟩
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptFinalFields
