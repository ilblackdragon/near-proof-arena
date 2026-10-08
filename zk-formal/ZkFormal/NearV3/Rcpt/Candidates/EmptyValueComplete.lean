import ZkFormal.NearV3.Rcpt.Candidates.EmptyValueTraffic
import ZkFormal.NearV3.Candidates.TrieCountTraffic
import ZkFormal.NearV3.Candidates.ProcPriorValueLength
namespace ZkFormal.NearV3.Rcpt.Candidates.EmptyValue
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render

theorem counted_cells (es : List ValE) (pub : List Fp) (t r x : Nat) (hx:x<15) :
    (Candidates.TrieCountHeight.value es pub).cell t r x=
      Fp.ofNat (ValGen.cell es ((Candidates.TrieCountHeight.value es pub).height t) r x) := by
  have hne:x≠SizeCount.valCount:=by change x≠15;omega
  simp only [Candidates.TrieCountHeight.value,Candidates.CountLift.trace,if_neg hne]
  rfl

theorem physical_digest (es : List ValE) (h : ValOk es) (pub msg : List Fp) (t : Nat) :
    tableBusCount table.interactions (Candidates.TrieCountHeight.value es pub) t pub B_DIGEST true msg=
      ((emptyMessages es).map Msg.toFp).count msg := by
  rw [show table.interactions=SizeCount.valTable.interactions++[emptyInteraction] from rfl,
    append_counts,Candidates.TrieCountTraffic.value_non_size _ _ _ _ _ _ (by decide),
    ((Candidates.TrieHeight.value_complete es h t pub).2.1 B_DIGEST msg).1]
  have hz:(valTraffic es).sends B_DIGEST=[]:=by
    simp [valTraffic,valSends,B_DIGEST,B_BYTES,B_ENT,B_SIZE]
  rw [hz]
  simp only [List.map_nil,List.count_nil,Nat.zero_add]
  apply generated_count es h.wf _ t pub msg
  · have hh:=h.wf.rows;change ValGen.R es≤2^22;exact Nat.le_trans (Nat.le_add_right _ 1) hh
  · intro r x hr hx;exact counted_cells es pub t r x hx

/-- Full VPRE contribution for the actual log22 value trace and the existing
nonempty SHA job inventory. No extra SHA rows or altered payload cap. -/
theorem physical_inventory (es : List ValE) (h : ValOk es) (pub msg : List Fp) (t : Nat) :
    (((nativeValueShaJobs es).map ZkFormal.Near.Render.digestMsg).map Msg.toFp).count msg+
      tableBusCount table.interactions (Candidates.TrieCountHeight.value es pub) t pub B_DIGEST true msg=
      ((valueDigests es).map Msg.toFp).count msg := by
  rw [physical_digest es h]
  have hp:=(complete_digest_inventory es).map Msg.toFp
  have hh:=hp.count_eq msg
  simpa only [List.map_append,List.count_append] using hh

/-- Compatibility with the actual authenticated-length component. -/
theorem length_local (bus : Nat) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (h:TableLocal (Candidates.ProcPriorValueLength.table bus) tr t pub) :
    TableLocal {(Candidates.ProcPriorValueLength.table bus) with
      interactions:=(Candidates.ProcPriorValueLength.table bus).interactions++[emptyInteraction]} tr t pub := by
  have hbase:=Candidates.ProcPriorValueLength.to_base bus tr t pub h
  have hext:=(local_iff tr t pub).mpr hbase
  refine ⟨h.log_ge,h.log_le,h.constr,?_⟩
  intro r hr i hi b hb
  rcases List.mem_append.mp hi with hi|hi
  · exact h.bits r hr i hi b hb
  · exact hext.bits r hr i (List.mem_append_right _ hi) b hb

end ZkFormal.NearV3.Rcpt.Candidates.EmptyValue
