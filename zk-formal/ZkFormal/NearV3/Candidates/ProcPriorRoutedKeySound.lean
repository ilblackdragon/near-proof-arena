import ZkFormal.NearV3.Candidates.ProcPriorRoutedReceiptKeys
import ZkFormal.NearV3.Candidates.ProcPriorRoutedKeyCounts
import ZkFormal.NearV3.Candidates.ProcPriorRoutedKeySymbols
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedKeySound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem query_symbols {AP:AirP} {pub msg:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:pubCount AP pub B_KEYNIB true msg=0)
    (hc:0<tableBusCount WalkV3.interactions tr 2 pub B_KEYNIB false msg) :
    msg[2]!.toNat<16 ∨ msg[2]!.toNat=SYM_END := by
  rcases ProcPriorRoutedKeyCounts.query_source hH htables hpub hc with hr|hq
  · exact ProcPriorRoutedReceiptKeys.physical_symbols hH htables hr
  · rw [tableBusCount_eq,List.count_pos_iff,List.mem_flatMap] at hq
    obtain ⟨r,hr,hm⟩:=hq
    exact ProcPriorRoutedKeySymbols.row_symbols hH htables (List.mem_range.mp hr) hm

theorem recv_canon {ws:List WalkR} (hW:WalkWf3 ws) {m:Msg}
    (hm:m∈walkRecvs3 ws B_KEYNIB) : m.getD 2 0<P := by
  simp only [walkRecvs3,show B_KEYNIB≠B_EDGE by decide,show B_KEYNIB≠B_BMAP by decide,
    ite_false,ite_true,List.mem_flatMap,List.mem_map,List.mem_range] at hm
  obtain ⟨w,hw,t,ht,rfl⟩:=hm
  have hi:t+1<w.steps.length:=by omega
  have hm:w.step (t+1)∈w.steps:=by rw [Walk3.step_eq w hi];exact List.getElem_mem hi
  exact (hW.canon w hw).2.2 _ hm |>.1

theorem keynib_ok {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀msg,pubCount AP pub B_KEYNIB true msg=0)
    {ws:List WalkR} (hW:WalkWf3 ws)
    (hT:TableTraffic WalkV3.interactions tr 2 pub (walkTraffic3 ws)) :
    Link3.KeynibOk ws (walkRecvs3 ws B_KEYNIB) := by
  refine ⟨fun m hm=>List.mem_map.mpr ⟨m,hm,rfl⟩,?_⟩
  intro m hm
  have hc:0<tableBusCount WalkV3.interactions tr 2 pub B_KEYNIB false (Msg.toFp m):=by
    rw [(hT _ _).2,List.count_pos_iff]
    exact List.mem_map.mpr ⟨m,hm,rfl⟩
  have hb:=query_symbols hH htables (hpub _) hc
  have hP:=recv_canon hW hm
  have he:(Msg.toFp m)[2]! =Fp.ofNat (m.getD 2 0):=by
    cases m with
    | nil=>rfl
    | cons a m=>
      cases m with
      | nil=>rfl
      | cons b m=>cases m <;>rfl
  rw [he,Fp.toNat_ofNat,Nat.mod_eq_of_lt hP] at hb
  exact ⟨hP,hb⟩
end ZkFormal.NearV3.Candidates.ProcPriorRoutedKeySound
