import ZkFormal.NearV3.Rcpt.Candidates.SizeCountNodeSender
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountValSender
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountSourceSender
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountAccumulator

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

def sendRows (T : ZkFormal.Air.Table) (tr : Trace Fp) (t : Nat) (pub : List Fp) : List (List Fp) :=
  (List.range (tr.height t)).flatMap (fun r => rowTraffic T.interactions tr t r pub B_SIZE true)

/-- Physical candidate sender/receiver balance authenticates exactly the payload
and count of the SAME segmented node/value views. Source traffic coverage and
absence of extraneous providers remain explicit global assembly obligations. -/
theorem count_balance_from_physical {tr : Trace Fp} {pub : List Fp} {tv ts tz : Nat}
    (hn : TableLocal nodeTable tr T_NODE pub) (hv : TableLocal valTable tr tv pub)
    (ns vs : List (Nat×Nat)) (hns : NodeProof3.NodeSegs tr ns)
    (hvc : Consec 0 vs) (hve : segEnd 0 vs≤tr.height tv)
    (hvs : ∀ p∈vs, IsSeg (ValProof.isOne tr tv ValV3.act)
      (ValProof.isOne tr tv ValV3.vf) (ValProof.isOne tr tv ValV3.vl) p.1 p.2)
    (hvp : ∀ r,segEnd 0 vs≤r → r<tr.height tv → ValProof.isOne tr tv ValV3.act r=false)
    (S : ZkFormal.Air.Table) (sourceSize : Nat)
    (hsource : sendRows S tr ts pub=[[2,(sourceSize:Fp)]])
    (hbal : ∀ m, tableBusCount sizeTable.interactions tr tz pub B_SIZE false m=
      (sendRows nodeTable tr T_NODE pub++sendRows valTable tr tv pub++
        sendRows (sourceTable S) tr ts pub).count m) :
    ∀ m, tableBusCount sizeTable.interactions tr tz pub B_SIZE false m=
      ([[0,(nodePayload (NodeProof3.viewOf tr pub ns):Fp),
          (((NodeProof3.viewOf tr pub ns).filter fun v => !v.dup).length:Fp)],
        [1,(valPayload (vs.map (ValProof.valOf tr tv)):Fp),
          (((vs.map (ValProof.valOf tr tv)).filter fun v => !v.dup).length:Fp)],
        [2,(sourceSize:Fp),0]] : List (List Fp)).count m := by
  intro m
  rw [hbal]
  unfold sendRows
  rw [node_size_sender hn hns,val_size_sender hv vs hvc hve hvs hvp,
    source_size_sender S tr ts pub sourceSize hsource]
  rfl

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
