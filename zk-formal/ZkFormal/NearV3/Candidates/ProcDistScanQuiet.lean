import ZkFormal.NearV3.Candidates.ProcScanRequestLocal
namespace ZkFormal.NearV3.Candidates.ProcDistScanQuiet
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched

set_option maxRecDepth 32768 in
theorem integer (Z:ZEnv)(hp:Z.cur Scan.kP=0)(hs:Z.cur Scan.kS=0)
    (hf:Z.cur Scan.fQ=0)(hr:Z.cur Scan.re=0)(hu0:Z.cur Scan.us0=0)(hu1:Z.cur Scan.us1=0) :
    ∀e∈Scan.own,zev Z e=0 := by
  simp only [Scan.own,Scan.ownBool,Scan.body,List.forall_mem_append,List.forall_mem_cons,List.forall_mem_nil,List.forall_mem_map]
  simp [Scan.own,Scan.ownBool,Scan.body,Scan.gC,Scan.notE,Scan.mul3,Scan.instCols,Scan.reqCols,
    ZkFormal.Chacha.Table.boolC,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.n,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.smul,
    zev,hp,hs,hf,hr,hu0,hu1]

theorem physical (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hp:tr.cell t r Scan.kP=0)(hs:tr.cell t r Scan.kS=0)
    (hf:tr.cell t r Scan.fQ=0)(hr:tr.cell t r Scan.re=0)
    (hu0:tr.cell t r Scan.us0=0)(hu1:tr.cell t r Scan.us1=0) :
    ∀e∈Scan.own,e.eval tr t r pub=0 := by
  have hcur (col:Nat)(h:tr.cell t r col=0):(tenv tr t r pub).cur col=0:=by
    change (tr.cell t r col).toNat=0;rw [h];rfl
  intro e he
  apply eval_zero_of
  exact integer _ (hcur _ hp) (hcur _ hs) (hcur _ hf) (hcur _ hr) (hcur _ hu0) (hcur _ hu1) e he
end ZkFormal.NearV3.Candidates.ProcDistScanQuiet
