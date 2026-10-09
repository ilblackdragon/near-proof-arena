import ZkFormal.NearV3.Candidates.ProcessRepairReceiptKeyOwner
import ZkFormal.Near.Link.Walks
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptWalkKey
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2

theorem lookup (r:Nat) (ss:List Nat) (hs:ss.length<P) {j:Nat} (hj:j<P)
    {id sym last:Fp} (hm:[id,Fp.ofNat j,sym,last]∈(RcptE.keyMsgs r ss).map Msg.toFp):
    j<ss.length ∧ sym=Fp.ofNat (ss.getD j 0) ∧ last=(if j+1=ss.length then 1 else 0):=by
  simp only [RcptE.keyMsgs,List.map_map,List.mem_map] at hm
  obtain ⟨k,hk,he⟩:=hm
  have hk:=List.mem_range.mp hk
  simp only [Function.comp_apply,Msg.toFp,List.map_cons,List.map_nil,List.cons.injEq] at he
  have hkj:k=j:=Link.ofNat_inj (by omega) hj he.2.1
  subst k
  refine ⟨hk,he.2.2.1.symm,?_⟩
  split <;> simpa only [*,ite_true,ite_false,show Fp.ofNat 1=(1:Fp) from rfl,show Fp.ofNat 0=(0:Fp) from rfl] using he.2.2.2.1.symm

theorem symbols {ws:List WalkR} (hW:WalkWf3 ws) {w:WalkR} (hw:w∈ws)
    (ss:List Nat) (hs:ss.length<P) (hcanon:∀x∈ss,x<P)
    (hm:∀j,1≤j→j<w.steps.length→
      (Msg.toFp [w.w,j-1,(w.step j).sym,if j+1=w.steps.length then 1 else 0])∈
      (RcptE.keyMsgs w.w ss).map Msg.toFp):
    w.steps.length=ss.length+1 ∧ w.key3=ss.take (ss.length-1):=by
  have hlen:=hW.len w hw
  have htotal:=Link3.wrows_lt hW
  have hsize:w.steps.length≤(ws.flatMap (·.steps)).length:=by
    rw [List.length_flatMap]
    exact Link.le_sum_of_mem (fun w:WalkR=>w.steps.length) hw
  have hmember:=hm (w.steps.length-1) (by omega) (by omega)
  have hterm:w.steps.length-1+1=w.steps.length:=by omega
  simp only [hterm,ite_true,Msg.toFp,List.map_cons,List.map_nil] at hmember
  have hlast:=lookup w.w ss hs (j:=w.steps.length-1-1) (by omega) hmember
  have hn:w.steps.length-1-1+1=ss.length:=by
    by_cases hn:w.steps.length-1-1+1=ss.length
    · exact hn
    · simp only [hn,ite_false] at hlast
      have h01:Fp.ofNat 1≠(0:Fp):=by decide
      exact (h01 hlast.2.2).elim
  have hlength:w.steps.length=ss.length+1:=by omega
  refine ⟨hlength,?_⟩
  apply List.ext_getElem
  · simp only [WalkR.key3,List.length_map,List.length_range,List.length_take];omega
  intro j hj hj'
  have hjn:j<ss.length-1:=by simp only [List.length_take] at hj';omega
  have hmem:=hm (j+1) (by omega) (by omega)
  have hnot:¬j+1+1=w.steps.length:=by omega
  simp only [hnot,ite_false,Nat.add_sub_cancel,Msg.toFp,List.map_cons,List.map_nil] at hmem
  have hmsg:=lookup w.w ss hs (j:=j) (by omega) hmem
  have hsymP:(w.step (j+1)).sym<P:=((hW.canon w hw).2.2 _ (Walk3.row_mem (by omega))).1
  have hssP:ss.getD j 0<P:=by
    simpa [List.getD_eq_getElem?_getD,show j<ss.length by omega] using hcanon _ (List.getElem_mem (by omega))
  have heq:=Link.ofNat_inj hsymP hssP hmsg.2.1
  simp only [WalkR.key3,List.getElem_map,List.getElem_range,List.getElem_take]
  simpa [List.getD_eq_getElem?_getD,show j<ss.length by omega] using heq
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptWalkKey
