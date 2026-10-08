import ZkFormal.NearV3.Candidates.SourceSizeTraffic
namespace ZkFormal.NearV3.Candidates.SizeComponents
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Render
open Rcpt.Candidates Rcpt.Candidates.SourceLog22 Rcpt.Candidates.DedupPartitionTable Rcpt.Candidates.DedupRender
open SizeCountReceiver SourceSizeTraffic

def view (vs : List NodeS3) (es : List ValE) (bs : List SrcpB) : SizeV :=
  ⟨((vs.filter fun e=>!e.dup).map fun e=>(e.v.ser false).length).sum,
   ((es.filter fun e=>!e.vz && !e.dup).map ValE.len).sum,size bs⟩
def counts (vs : List NodeS3) (es : List ValE) : Counts :=
  ⟨(vs.filter fun e=>!e.dup).length,(es.filter fun e=>!e.dup).length⟩

/-- Exact SIZE balance for the actual node/value, four partitioned source,
and receiver traces, all tied to the same semantic payload/count inputs. -/
theorem balance {tr : Trace Fp} {t0 t1 t2 t3 H : Nat} {pub : List Fp}
    (bs : List SrcpB) (rep : Nat → Bool) (hn : bs≠[])
    (hh : ∀ t∈[t0,t1,t2,t3],tr.height t=H)
    (hR : R bs≤3*(H-1)+H)
    (hshape : ∀ B∈bs,B.root.length=32 ∧ B.leaf.length=32 ∧
      ∀ it∈B.path,it.sib.length=32 ∧ it.acc.length=32)
    (h0 : ∀ r,r<H → ∀ x,tr.cell t0 r x=Fp.ofNat (cell bs rep r x))
    (h1 : ∀ r,r<H → ∀ x,tr.cell t1 r x=Fp.ofNat (cell bs rep ((H-1)+r) x))
    (h2 : ∀ r,r<H → ∀ x,tr.cell t2 r x=Fp.ofNat (cell bs rep (2*(H-1)+r) x))
    (h3 : ∀ r,r<H → ∀ x,tr.cell t3 r x=Fp.ofNat (cell bs rep (3*(H-1)+r) x))
    (vs : List NodeS3) (es : List ValE) (hnodes : NodeOk vs) (hvalues : ValOk es)
    (tn tv ts : Nat) (m : List Fp) :
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node vs pub) tn pub B_SIZE true m+
      tableBusCount SizeCount.valTable.interactions (TrieCountHeight.value es pub) tv pub B_SIZE true m+
      fourCount tr t0 t1 t2 t3 pub true m+
      tableBusCount SizeCount.sizeTable.interactions (trace pub (view vs es bs) (counts vs es)) ts pub B_SIZE true m=
    tableBusCount SizeCount.nodeTable.interactions (TrieCountHeight.node vs pub) tn pub B_SIZE false m+
      tableBusCount SizeCount.valTable.interactions (TrieCountHeight.value es pub) tv pub B_SIZE false m+
      fourCount tr t0 t1 t2 t3 pub false m+
      tableBusCount SizeCount.sizeTable.interactions (trace pub (view vs es bs) (counts vs es)) ts pub B_SIZE false m := by
  rw [SizeRecordTraffic.node_traffic vs hnodes,SizeRecordTraffic.value_traffic es hvalues,
    SizeRecordTraffic.node_traffic vs hnodes,SizeRecordTraffic.value_traffic es hvalues,
    four_size_count bs rep hn hh hR hshape h0 h1 h2 h3,
    four_size_count bs rep hn hh hR hshape h0 h1 h2 h3,
    (receiver_traffic pub (view vs es bs) (counts vs es) ts B_SIZE m).1,
    (receiver_traffic pub (view vs es bs) (counts vs es) ts B_SIZE m).2]
  simp [SizeCountReceiver.traffic,SizeCountReceiver.messages,SizeRender.ofNat0,view,counts,SizeRecordTraffic.nodeMessage,SizeRecordTraffic.valueMessage,
    Near.Msg.toFp,List.count_cons]
  omega

/-- Local legality uses precisely the existing base-payload limit and the
encoded witness charge including store-record headers. -/
theorem receiver_complete (pub : List Fp) (vs : List NodeS3) (es : List ValE) (bs : List SrcpB)
    (h : Valid pub (view vs es bs) (counts vs es)) (t : Nat) :
    TableLocal SizeCount.sizeTable (trace pub (view vs es bs) (counts vs es)) t pub ∧
    TableTraffic SizeCount.sizeTable.interactions (trace pub (view vs es bs) (counts vs es)) t pub
      (SizeCountReceiver.traffic (view vs es bs) (counts vs es)) :=
  ⟨SizeCountLocal.receiver_local pub _ _ h t,receiver_traffic pub _ _ t⟩
end ZkFormal.NearV3.Candidates.SizeComponents
