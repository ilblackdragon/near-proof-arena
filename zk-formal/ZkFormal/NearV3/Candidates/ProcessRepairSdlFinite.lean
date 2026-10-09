import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlFinite
import ZkFormal.NearV3.Candidates.ProcessRepairSdlInventory
import ZkFormal.NearV3.Candidates.ProcessRepairCodecParameters
import ZkFormal.NearV3.Candidates.ProcessRepairTrieViews
namespace ZkFormal.NearV3.Candidates.ProcessRepairSdlFinite
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec ProcPriorCodecSoundSdlDescent

/-- Physical log22 height excludes any closed SDL predecessor cycle, including
field-timestamp wrap. Consequently a live receive has a real public origin;
no independent timestamp bound or generator premise is needed. -/
theorem public_origin {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (r : Nat) (hr:r<tr.height 0) (hm:(ProcPriorCodecActual.interactions[7]!).multNat (ProcPriorRoutedCodecProjection.codec tr) 0 r pub≠0) :
    ∃seedTau,seedTau<P ∧ pubCount AP pub B_SDL true (Fp.ofNat seedTau::payload (ProcPriorRoutedCodecProjection.codec tr) 0 r pub)≠0 := by
  classical
  apply Classical.byContradiction
  intro hn
  let A (v : Nat) := v<tr.height 0 ∧
    (ProcPriorCodecActual.interactions[7]!).multNat (ProcPriorRoutedCodecProjection.codec tr) 0 v pub≠0 ∧ payload (ProcPriorRoutedCodecProjection.codec tr) 0 v pub=payload (ProcPriorRoutedCodecProjection.codec tr) 0 r pub
  have hheight:tr.height 0<P := by
    have hh:tr.height 0≤2^22:=Nat.pow_le_pow_right (by decide) (ProcessRepairTrieViews.value_local view).log_le
    have hp:2^22<P := by decide +kernel
    omega
  refine ProcSdlFiniteDescent.no_closed_set (tr.height 0) hheight A (fun v=>cv (ProcPriorRoutedCodecProjection.codec tr) 0 v tau) ?_ ?_ r ⟨hr,hm,rfl⟩
  · intro v hv
    exact ⟨hv.1,cv_lt v tau⟩
  · intro v hv
    have ht:0<AP.tables.length:=by rw [view.length];decide +kernel
    have hi:ProcPriorRoutedCodecProjection.interaction (ProcPriorCodecActual.interactions[7]!)∈AP.tables[0]!.interactions := by
      rw [view.wires]
      exact ProcPriorRoutedCodecProjection.member ProcPriorCodecSoundSdlRows.receive_member (by decide +kernel)
    rcases recv_src view.valid ht hv.1 hi (by rfl)
      (by rfl) (by rw [ProcPriorRoutedCodecProjection.mult];exact hv.2.1) with hp|hsrc
    · change pubCount AP pub B_SDL true ((ProcPriorRoutedCodecProjection.interaction (ProcPriorCodecActual.interactions[7]!)).msgVal tr 0 v pub)≠0 at hp
      have hpub:pubCount AP pub B_SDL true (Fp.ofNat (cv (ProcPriorRoutedCodecProjection.codec tr) 0 v tau)::payload (ProcPriorRoutedCodecProjection.codec tr) 0 r pub)≠0 := by
        simpa only [ProcPriorRoutedCodecProjection.message,(messages (ProcPriorRoutedCodecProjection.codec tr) 0 v pub).1,hv.2.2] using hp
      exact (hn ⟨cv (ProcPriorRoutedCodecProjection.codec tr) 0 v tau,cv_lt v tau,hpub⟩).elim
    · obtain ⟨t',ht',w,hw,i',hi',hb,hs,hmsg,hm'⟩:=hsrc
      have he:t'=0 := Classical.byContradiction (fun hn=>ProcessRepairSdlInventory.other_tables
        (AP:=ProcessRepairBalance.reference AP) rfl t' (by simpa [ProcessRepairBalance.reference,←view.length] using ht') hn i'
        (by simpa only [view.wires t',ProcessRepairBalance.reference] using hi') hs hb)
      subst t'
      rw [view.wires] at hi'
      have hei:=ProcessRepairSdlInventory.sender_eq hi' hb hs
      subst i'
      change (ProcPriorRoutedCodecProjection.interaction (ProcPriorCodecActual.interactions[8]!)).msgVal tr 0 w pub=_ at hmsg
      change (ProcPriorRoutedCodecProjection.interaction (ProcPriorCodecActual.interactions[8]!)).multNat tr 0 w pub≠0 at hm'
      rw [ProcPriorRoutedCodecProjection.message,ProcPriorRoutedCodecProjection.message,
        (messages (ProcPriorRoutedCodecProjection.codec tr) 0 w pub).2,
        (messages (ProcPriorRoutedCodecProjection.codec tr) 0 v pub).1] at hmsg
      rw [ProcPriorRoutedCodecProjection.mult] at hm'
      have hd:=List.cons.inj hmsg
      have hstamp:=congrArg Fp.toNat hd.1
      simp only [Fp.toNat_ofNat] at hstamp
      have hb:cv (ProcPriorRoutedCodecProjection.codec tr) 0 v tau<P := cv_lt v tau
      rw [Nat.mod_eq_of_lt hb] at hstamp
      refine ⟨w,⟨hw,?_,hd.2.trans hv.2.2⟩,hstamp⟩
      rwa [multiplicity_same]
end ZkFormal.NearV3.Candidates.ProcessRepairSdlFinite
