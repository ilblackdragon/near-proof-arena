import ZkFormal.NearV3.Candidates.ProcessRepairQueueEmpty
import ZkFormal.NearV3.Candidates.ProcessRepairQueueCountRead
import ZkFormal.NearV3.Qv.Extract.MainQueueReads
import ZkFormal.NearV3.Qv.Extract.AbsentBufferedRead
namespace ZkFormal.NearV3.Candidates.ProcessRepairMainQueue
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Qv Qv.Extract Qv.Candidates.CombinedTable
open Qv.Candidates.ValueTable (B_QVC)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem assemble {AP:AirP} {tr:Trace Fp} {pub:List Fp}
    (view:ProcessRepairInterface.View AP pub tr) (hpub:∀seg∈AP.pubSegs,seg.bus≠B_VBYTES)
    (hpubQ:∀seg∈AP.pubSegs,seg.bus≠B_QSH) (hpubC:∀seg∈AP.pubSegs,seg.bus≠B_QVC)
    (vs:List NodeS3) (hs:List HeadE) {es:List ValE} (hv:ValWf es)
    (hT:TableTraffic ValV3.interactions (ProcPriorRoutedRawBytes.value tr) 0 pub (valTraffic es))
    (hvb:∀e∈es,Bytes8 e.bytes)
    (q:WalkChain (ProcPriorRoutedKeyView.key tr) 0)
    (v:ParserChain (ProcPriorRoutedKeyView.key tr) 0 (segEnd 0 q.segs))
    (hread:∀i (hi:i<q.segs.length),
      (queueTree vs es hs (cv (ProcPriorRoutedKeyView.key tr) 0 q.segs[i].1 Qv.Candidates.ValueTable.tau)).find
        (NearSpec.nibbles (physicalWalkBytes (ProcPriorRoutedKeyView.key tr) 0 q.segs[i]))=
        some (queueValue vs es (ProcPriorRoutedKeyView.key tr) 0 q.segs[i].1)) :
    ∃ss,(queueMainValues vs es (ProcPriorRoutedKeyView.key tr) 0 q ss).Valid ∧
      (queueMainValues vs es (ProcPriorRoutedKeyView.key tr) 0 q ss).Reads
        (queueTree vs es hs 0) (queueTree vs es hs 0) (queueTree vs es hs 0) := by
  have hL:=Qv.Candidates.KeyTrafficRepair.local_to_base (ProcessRepairKeyView.local_key view)
  obtain ⟨h2,hm0,hm1,hm2⟩:=fixed_main_reads hL q
  have h0:0<q.segs.length:=by omega
  have h1:1<q.segs.length:=by omega
  have heget (j:Nat) (hj:j<q.segs.length):q.segs.getD j (0,0)=q.segs[j]:=by
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
  have hmain (j:Nat) (hj:j<q.segs.length) (hj3:j<3):
      (ProcPriorRoutedKeyView.key tr).cell 0 q.segs[j].1 main=1:=by
    have hh:=main_read_prefix hL q
    exact (hh.2 j hj).mpr (by omega)
  have hempty:∀j∈[0,2],cv (ProcPriorRoutedKeyView.key tr) 0 (q.segs.getD j (0,0)).1 absent=0→
      ∃e∈es,e.vid=cv (ProcPriorRoutedKeyView.key tr) 0 (q.segs.getD j (0,0)).1 Qv.Candidates.ValueTable.vid ∧
        EmptyQueue (some (toBytes e.bytes)):=by
    intro j hj ha
    have hj02:j=0∨j=2:=by simpa using hj
    have hjlt:j<q.segs.length:=by omega
    rw [heget j hjlt] at ha ⊢
    have hm:cv (ProcPriorRoutedKeyView.key tr) 0 q.segs[j].1 Qv.Candidates.ValueTable.len=0:=by
      rw [main_read_mode hL q j hjlt (hmain j hjlt (by omega))]
      simp only [hj02,ite_true]
    have hacell:(ProcPriorRoutedKeyView.key tr).cell 0 q.segs[j].1 absent=0:=by
      exact (Fp.ofNat_toNat _).symm.trans (congrArg Fp.ofNat ha)
    exact ProcessRepairQueueEmpty.read view hpub hpubC hv hT hvb q v q.segs[j] (List.getElem_mem hjlt) hacell hm
  have hab:=isBool hL (q.start_lt 1 h1) (x:=absent) (by simp [walkBools])
  rcases hab with ha|ha
  · have hn:cv (ProcPriorRoutedKeyView.key tr) 0 q.segs[1].1 absent=0:=by simp only [cv,ha];decide
    have hseg:=q.valid q.segs[1] (List.getElem_mem h1)
    have hw:(ProcPriorRoutedKeyView.key tr).cell 0 q.segs[1].1 walk=1:=by
      simpa only [isOne,decide_eq_true_eq] using hseg.2.2.2.1 q.segs[1].1 (by omega) (by have:=hseg.1;omega)
    have hk:=WalkChain.main_kind hL q 1 h1 hm1
    simp only [show ¬(1=0∨1=2) by decide,show (1:Nat)<2 by decide,ite_false,ite_true] at hk
    have hend:=seg_le_end q.segs 0 q.consecutive q.segs[1] (List.getElem_mem h1)
    have hfit:=Nat.le_trans hend.2 q.fits
    have hlen: q.segs[1].2=1:=(walk_kind_length hL hfit hseg).2 (Or.inr hk.2)
    have hlast:(ProcPriorRoutedKeyView.key tr).cell 0 q.segs[1].1 wl=1:=by
      simpa only [hlen,Nat.add_sub_cancel,isOne,decide_eq_true_eq] using hseg.2.2.1
    have hp: (ProcPriorRoutedKeyView.key tr).cell 0 q.segs[1].1 present=1:=
      (present_iff hL (q.start_lt 1 h1)).mpr ⟨hlast,ha⟩
    have hcount:(ProcPriorRoutedKeyView.key tr).cell 0 q.segs[1].1 countRead=1:=
      (count_request_gate hL (q.start_lt 1 h1)).mpr ⟨hp,hm1,hk.1,hk.2⟩
    obtain ⟨e,he,hz,hid,ss,hbuf,hlen,hcnt,hrequests⟩:=ProcessRepairQueueCountRead.read view hpub hpubQ hpubC
      hv hT hvb q v q.segs[1] (List.getElem_mem h1) hcount
    refine ⟨ss,?_,main_queue_reads hL q vs es hs ss _ hlen h1 hcnt hrequests hread⟩
    apply main_queue_valid vs hv (ProcPriorRoutedKeyView.key tr) 0 q ss hempty
    · intro _;exact ⟨e,he,by simpa only [heget 1 h1] using hid,hbuf⟩
    · intro hbad
      rw [heget 1 h1,hn] at hbad
      exact False.elim (hbad rfl)
  · have hn:cv (ProcPriorRoutedKeyView.key tr) 0 q.segs[1].1 absent=1:=by simp only [cv,ha];decide
    refine ⟨[],?_,?_⟩
    · apply main_queue_valid vs hv (ProcPriorRoutedKeyView.key tr) 0 q [] hempty
      · intro hz;rw [heget 1 h1,hn] at hz;omega
      · intro _;rfl
    · have hr0:=main_fixed_root_read hL q 0 h0 hm0 (by omega) (hread 0 h0)
      have hr1:=main_fixed_root_read hL q 1 h1 hm1 (by omega) (hread 1 h1)
      have hr2:=main_fixed_root_read hL q 2 h2 hm2 (by omega) (hread 2 h2)
      simp only [MainValues.Reads,queueMainValues,heget 0 h0,heget 1 h1,heget 2 h2]
      refine ⟨?_,?_,?_,?_⟩
      · simpa using hr0
      · simpa using hr1
      · intro x hx;simp at hx
      · simpa using hr2
end ZkFormal.NearV3.Candidates.ProcessRepairMainQueue
