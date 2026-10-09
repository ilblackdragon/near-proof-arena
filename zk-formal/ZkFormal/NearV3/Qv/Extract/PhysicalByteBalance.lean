import ZkFormal.NearV3.Qv.Extract.ByteAggregate
import ZkFormal.NearV3.Qv.Extract.SupplierStreams

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Complete value-stream ownership from the physical four-table VBYTES
balance and checked traffic views. No record-specific balance or ownership
premise is needed; whole-AIR assembly must supply this channel equation. -/
theorem physical_balanced_record_complete {tr : Trace Fp} {tq ta tk tv : Nat} {pub : List Fp}
    (hL : TableLocal Candidates.CombinedTable.table tr tq pub)
    (q : WalkChain tr tq) (v : ParserChain tr tq (segEnd 0 q.segs))
    (as : List AcctV) (aks : List AkeyE) (vals : List ValE) (hv : ValWf vals)
    (ha : TableTraffic AcctV3.interactions tr ta pub (acctV3Traffic as))
    (hk : TableTraffic AkeyV3.interactions tr tk pub (akeyTraffic aks))
    (ht : TableTraffic ValV3.interactions tr tv pub (valTraffic vals))
    (hbalance : ∀ m,
      tableBusCount Candidates.CombinedTable.interactions tr tq pub B_VBYTES true m +
      tableBusCount AcctV3.interactions tr ta pub B_VBYTES true m +
      tableBusCount AkeyV3.interactions tr tk pub B_VBYTES true m =
      tableBusCount ValV3.interactions tr tv pub B_VBYTES false m)
    (p : Nat × Nat) (hp : p∈v.segs) (hn : cv tr tq p.1 Candidates.ValueTable.len≠0) :
    (physicalRecordBytes tr tq p.1 p.2 pub).Perm
      (((valRecvs vals B_VBYTES).map Msg.toFp).filter
        (fun m => decide ((byteKey m).1=tr.cell tq p.1 Candidates.ValueTable.vid))) := by
  have hglobal : ((v.segs.flatMap (fun p => physicalRecordBytes tr tq p.1 p.2 pub) ++
      (acctV3Sends as B_VBYTES).map Msg.toFp) ++
      (akeySends aks B_VBYTES).map Msg.toFp).Perm ((valRecvs vals B_VBYTES).map Msg.toFp) := by
    apply List.perm_iff_count.mpr
    intro m
    have he := hbalance m
    rw [(ha B_VBYTES m).1,(hk B_VBYTES m).1,(ht B_VBYTES m).2] at he
    simp only [acctV3Traffic,akeyTraffic,valTraffic] at he
    rw [tableBusCount_eq,byte_all_physical hL q v] at he
    simpa only [List.count_append] using he
  have hmove := (List.perm_cons_erase hp).flatMap_right
    (fun z => physicalRecordBytes tr tq z.1 z.2 pub)
  have hselected := (hmove.append_right ((acctV3Sends as B_VBYTES).map Msg.toFp)).append_right
    ((akeySends aks B_VBYTES).map Msg.toFp)
  have hfinal := hselected.symm.trans hglobal
  apply selected_record_complete hL q v p hp hn (v.segs.erase p)
    (fun z hz => List.mem_of_mem_erase hz) as aks vals hv
  simpa only [List.flatMap_cons,List.append_assoc] using hfinal

end ZkFormal.NearV3.Qv.Extract
