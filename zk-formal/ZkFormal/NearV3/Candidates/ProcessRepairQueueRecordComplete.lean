import ZkFormal.NearV3.Qv.Extract.PhysicalNativeRecord
namespace ZkFormal.NearV3.Candidates.ProcessRepairQueueRecordComplete
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Qv.Extract

/-- Additional real supplier families are retained in conservation. Their
position-zero ownership property is explicit until obtained from their AIR. -/
theorem selected {tr:Trace Fp} {tt:Nat} {pub:List Fp}
    (hL:TableLocal Qv.Candidates.CombinedTable.table tr tt pub)
    (q:WalkChain tr tt) (v:ParserChain tr tt (segEnd 0 q.segs))
    (p:Nat×Nat) (hp:p∈v.segs) (hn:cv tr tt p.1 Qv.Candidates.ValueTable.len≠0)
    (rest:List (Nat×Nat)) (hr:∀z∈rest,z∈v.segs)
    (as:List AcctV) (aks:List AkeyE) (vals:List ValE) (hv:ValWf vals)
    (extra:List (List Fp)) (hextra:StartClosed extra)
    (hbalance:(physicalRecordBytes tr tt p.1 p.2 pub ++
      (rest.flatMap (fun z=>physicalRecordBytes tr tt z.1 z.2 pub) ++
        (acctV3Sends as B_VBYTES).map Msg.toFp ++ (akeySends aks B_VBYTES).map Msg.toFp) ++ extra).Perm
      ((valRecvs vals B_VBYTES).map Msg.toFp)) :
    (physicalRecordBytes tr tt p.1 p.2 pub).Perm
      (((valRecvs vals B_VBYTES).map Msg.toFp).filter
        (fun m=>decide ((byteKey m).1=tr.cell tt p.1 Qv.Candidates.ValueTable.vid))) := by
  have hb:=seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
  have hfit:p.1+p.2≤tr.height tt:=Nat.le_trans hb.2 v.fits
  have hw:∀r,p.1≤r→r<p.1+p.2→tr.cell tt r Qv.Candidates.CombinedTable.walk=0:=by
    intro r hr hn
    exact zero_of_false hL (by omega) (x:=Qv.Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix r (by omega) (by omega))
  apply physical_record_complete hL hfit hw (v.valid p hp) hv hn _
    (by simpa only [List.append_assoc] using hbalance)
  have hc:=startClosed_append (other_suppliers_closed hL q v rest hr as aks) hextra
  simpa only [List.append_assoc,StartClosed] using hc
end ZkFormal.NearV3.Candidates.ProcessRepairQueueRecordComplete
