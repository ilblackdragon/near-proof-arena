import ZkFormal.NearV3.Qv.Extract.ParserStream
import ZkFormal.NearV3.Rcpt.Extract.AcctProof
import ZkFormal.NearV3.Rcpt.Extract.AkeyProof

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Every nonempty supplier starts its value stream at position zero. -/
def StartClosed (ms : List (List Fp)) : Prop :=
  ∀ m∈ms, ∃ z∈ms, byteKey z=((byteKey m).1,0)

theorem startClosed_perm {xs ys : List (List Fp)} (h : xs.Perm ys)
    (hx : StartClosed xs) : StartClosed ys := by
  intro m hm
  obtain ⟨z,hz,he⟩ := hx m (h.mem_iff.mpr hm)
  exact ⟨z,h.mem_iff.mp hz,he⟩

theorem startClosed_append {xs ys : List (List Fp)}
    (hx : StartClosed xs) (hy : StartClosed ys) : StartClosed (xs++ys) := by
  intro m hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨z,hz,he⟩ := hx m hm
    exact ⟨z,List.mem_append.mpr (Or.inl hz),he⟩
  · obtain ⟨z,hz,he⟩ := hy m hm
    exact ⟨z,List.mem_append.mpr (Or.inr hz),he⟩

theorem account_streams_closed (as : List AcctV) :
    StartClosed ((acctV3Sends as B_VBYTES).map Msg.toFp) := by
  intro m hm
  change m∈(acctV3Sends as B_VBYTES).map Msg.toFp at hm
  obtain ⟨msg,hmsg,rfl⟩ := List.mem_map.mp hm
  simp only [acctV3Sends,ite_true] at hmsg
  obtain ⟨a,ha,hm⟩ := List.mem_flatMap.mp hmsg
  rw [emitAt_zero] at hm
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
  have hn : 0<a.pre.length := by have := List.mem_range.mp hi; omega
  refine ⟨Msg.toFp [a.k,0,a.pre.getD 0 0],?_,?_⟩
  · apply List.mem_map.mpr
    refine ⟨_,?_,rfl⟩
    simp only [acctV3Sends,ite_true]
    apply List.mem_flatMap.mpr
    refine ⟨a,ha,?_⟩
    rw [emitAt_zero]
    exact List.mem_map.mpr ⟨0,List.mem_range.mpr hn,rfl⟩
  · rfl

theorem access_key_streams_closed (es : List AkeyE) :
    StartClosed ((akeySends es B_VBYTES).map Msg.toFp) := by
  intro m hm
  change m∈(akeySends es B_VBYTES).map Msg.toFp at hm
  obtain ⟨msg,hmsg,rfl⟩ := List.mem_map.mp hm
  simp only [akeySends,ite_true] at hmsg
  obtain ⟨e,he,hm⟩ := List.mem_flatMap.mp hmsg
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hm
  refine ⟨Msg.toFp [e.vid,0,e.bytes.getD 0 0],?_,?_⟩
  · apply List.mem_map.mpr
    refine ⟨_,?_,rfl⟩
    simp only [akeySends,ite_true]
    exact List.mem_flatMap.mpr ⟨e,he,List.mem_map.mpr ⟨0,by simp,rfl⟩⟩
  · rfl

/-- All other extracted parser records and the account/access-key tables meet
the ownership condition, independent of their physical message ordering. -/
theorem other_suppliers_closed {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
    (q : WalkChain tr tt) (v : ParserChain tr tt (segEnd 0 q.segs))
    (l : List (Nat × Nat)) (hl : ∀ p∈l,p∈v.segs)
    (as : List AcctV) (es : List AkeyE) :
    StartClosed (l.flatMap (fun p => physicalRecordBytes tr tt p.1 p.2 pub) ++
      (acctV3Sends as B_VBYTES).map Msg.toFp ++ (akeySends es B_VBYTES).map Msg.toFp) := by
  exact startClosed_append (startClosed_append
    (physical_records_closed hL q v l hl) (account_streams_closed as))
    (access_key_streams_closed es)

/-- The parser ownership conclusion with all three concrete supplier families.
Only the assembled exact bus balance remains explicit. -/
theorem selected_record_complete {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
    (q : WalkChain tr tt) (v : ParserChain tr tt (segEnd 0 q.segs))
    (p : Nat × Nat) (hp : p∈v.segs) (hn : cv tr tt p.1 Candidates.ValueTable.len≠0)
    (rest : List (Nat × Nat)) (hr : ∀ z∈rest,z∈v.segs)
    (as : List AcctV) (aks : List AkeyE) (vals : List ValE) (hv : ValWf vals)
    (hbalance : (physicalRecordBytes tr tt p.1 p.2 pub ++
      (rest.flatMap (fun z => physicalRecordBytes tr tt z.1 z.2 pub) ++
        (acctV3Sends as B_VBYTES).map Msg.toFp ++ (akeySends aks B_VBYTES).map Msg.toFp)).Perm
      ((valRecvs vals B_VBYTES).map Msg.toFp)) :
    (physicalRecordBytes tr tt p.1 p.2 pub).Perm
      (((valRecvs vals B_VBYTES).map Msg.toFp).filter
        (fun m => decide ((byteKey m).1=tr.cell tt p.1 Candidates.ValueTable.vid))) := by
  have hb := seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
  have hfit : p.1+p.2≤tr.height tt := Nat.le_trans hb.2 v.fits
  have hw : ∀ r, p.1≤r → r<p.1+p.2 → tr.cell tt r Candidates.CombinedTable.walk=0 := by
    intro r hr hn
    exact zero_of_false hL (by omega) (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix r (by omega) (by omega))
  exact physical_record_complete hL hfit hw (v.valid p hp) hv hn _ hbalance
    (other_suppliers_closed hL q v rest hr as aks)

end ZkFormal.NearV3.Qv.Extract
