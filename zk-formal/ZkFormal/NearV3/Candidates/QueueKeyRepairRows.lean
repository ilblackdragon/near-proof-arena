import ZkFormal.NearV3.Candidates.QueueKeyRepairTransport

namespace ZkFormal.NearV3.Candidates.QueueKeyRepair
open NearSpec ZkFormal.Near Qv Qv.Candidates Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Algebra ValueGen

def keys : List Interaction := interactions.drop 5 |>.take 3

theorem key_filter (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic interactions tr t r pub B_KEYNIB true=rowTraffic keys tr t r pub B_KEYNIB true := by
  simp [interactions,keys,CombinedTable.interactions,rowTraffic,Dsl.send,Dsl.recv,
    B_KEYNIB,B_VBYTES,B_QSH,B_FINAL,ValueTable.B_QVC]

def rowMessages (w : Walk) (pos : Nat) (b : UInt8) : List Msg :=
  let wid:=W_QV+w.tau+64*w.slot
  [[wid,2*pos,b.toNat/16,0],[wid,2*pos+1,b.toNat%16,0]]++
  (if pos+1=w.kind.bytes.length then [[wid,2*pos+2,SYM_END,1]] else [])

theorem natural_bits (w : Walk) (pos : Nat) (b : UInt8) :
    ∀i∈keys,(∀e∈i.mult,rowNatExpr e=true ∧ rowNatEval (w.row pos b) e≤1) ∧
      (∀e∈i.msg,rowNatExpr e=true) := by
  simp [keys,interactions,CombinedTable.interactions,Dsl.send,Dsl.recv,
    rowNatExpr,rowNatEval,CombinedTable.walk,CombinedTable.wl,CombinedTable.wp,
    CombinedTable.wid,CombinedTable.nibble,Dsl.c,Dsl.k,Dsl.smul,Dsl.sum]
  cases (pos+1 == w.kind.bytes.length) <;> decide

theorem natural_messages (w : Walk) (pos : Nat) (b : UInt8) :
    natRowTraffic keys (w.row pos b) B_KEYNIB true=rowMessages w pos b := by
  have hi:=w.high_nibble pos b
  have lo:=w.low_nibble pos b
  simp only [keys,interactions,CombinedTable.interactions,List.drop,List.take,
    natRowTraffic,Dsl.send,Dsl.recv]
  simp [CombinedTable.wl,CombinedTable.walk,CombinedTable.wp,CombinedTable.wid,
    CombinedTable.slot,ValueTable.tau,Dsl.c,Dsl.k,Dsl.smul,Dsl.sum,rowNatEval,rowMessages,natMultBits] at hi lo ⊢
  by_cases hl : pos+1=w.kind.bytes.length <;> simp [hl,hi,lo,Nat.add_assoc]

theorem field_messages (w : Walk) (pos : Nat) (b : UInt8)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (hc : ∀c,tr.cell t r c=Fp.ofNat ((w.row pos b).getD c 0)) :
    rowTraffic interactions tr t r pub B_KEYNIB true=(rowMessages w pos b).map Msg.toFp := by
  rw [key_filter]
  rw [rowTraffic_nat _ _ _ _ _ _ hc (natural_bits w pos b) _ _,natural_messages]

theorem word_messages (w : Walk) :
    w.kind.bytes.zipIdx.flatMap (fun bi=>rowMessages w bi.2 bi.1)=keyMessages w := by
  cases hk:w.kind <;>
    simp [rowMessages,keyMessages,RcptE.keyMsgs,walkId,Kind.bytes,hk,
      NearSpec.nibbles,NearSpec.u64,leN,List.range_succ,List.zipIdx]

end ZkFormal.NearV3.Candidates.QueueKeyRepair
