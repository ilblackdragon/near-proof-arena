import ZkFormal.NearV3.Candidates.ProcPriorRecordQueryActivity
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordQueryMessage
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable

theorem message (tr:Trace Fp) (t r:Nat) (pub:List Fp):
    ProcPriorRecordQueryActivity.query.msgVal tr t r pub=
      [Fp.ofNat (cv tr t r tau),Fp.ofNat (2*cv tr t r record+cv tr t r receiver),
       Fp.ofNat (cv tr t r lo),Fp.ofNat (cv tr t r mid),Fp.ofNat (cv tr t r hi)]:=by
  have hc (x:Nat):tr.cell t r x=Fp.ofNat (cv tr t r x):=(Fp.ofNat_toNat _).symm
  have ck (n:Nat):(n:Fp)=Fp.ofNat n:=rfl
  simp [ProcPriorRecordQueryActivity.query,ProcPriorRecordLinear.interactions,
    ProcPriorRecordTable.interactions,ProcPriorVertical4Linear.interaction,Interaction.msgVal,
    queryOrdinal,ProcPriorVertical4Linear.expression,Expr.eval,Expr.evalWith,rowEnv,c,k,hc,ck 2,
    ZkFormal.Near.ofNat_add',ZkFormal.Near.ofNat_mul']
end ZkFormal.NearV3.Candidates.ProcPriorRecordQueryMessage
