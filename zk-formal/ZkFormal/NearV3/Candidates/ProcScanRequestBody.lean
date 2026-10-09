import ZkFormal.NearV3.Candidates.ProcScanRequestBodyFirst
import ZkFormal.NearV3.Candidates.ProcScanRequestBodyEnd
import ZkFormal.NearV3.Candidates.ProcScanRequestBodyTerminal
import ZkFormal.NearV3.Candidates.ProcScanRequestBodyBoundary
import ZkFormal.NearV3.Candidates.ProcScanRequestBodyTail
namespace ZkFormal.NearV3.Candidates.ProcScanRequestBody
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcScanRequestFactor ProcScanRequestFieldEquations
attribute [local irreducible] ProcScanRequestFactor.row Scan.reqRows

private theorem join {α:Type}(xs:List α)(P:α→Prop)(n:Nat)
    (ha:∀x∈xs.take n,P x)(hb:∀x∈xs.drop n,P x) : ∀x∈xs,P x := by
  intro x hx
  have hh:x∈xs.take n++xs.drop n:=by simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hh with hh|hh
  · exact ha x hh
  · exact hb x hh

theorem physical (R:Run)(c:CReq)(rho:Nat)(hr:rho<20)
    (hbits:c.bits=setBits c.bm)(hlink:c.link=c.s*R.n+c.r)(hk:c.key<P)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (Scan.reqRows R c)[rho]![col]!)
    (hnext:rho<19→∀col,tr.cell t ((r+1)%tr.height t) col=Fp.ofNat (Scan.reqRows R c)[rho+1]![col]!)
    (hboundary:rho=19→ProcScanRequestBodyBoundary.Next tr t r) :
    ∀e∈Scan.body,e.eval tr t r pub=0 := by
  let jj:=ProcScanRequestCount.before c.bm rho
  let cv:=(ProcScanRequestState.state R c rho).2.2
  have hcur:∀col,tr.cell t r col=cell R c rho jj cv col:=by
    intro col;rw [hrow,ProcScanRequestState.native_at R c rho hr];rfl
  have hstart:rho=0→jj=0 ∧cv=R.base:=by intro he;subst rho;exact ⟨rfl,rfl⟩
  have h0:=ProcScanRequestBodyPrefix.physical R c rho jj cv tr t r pub hcur
  have h1:=ProcScanRequestBodyFirst.physical R c rho jj cv hstart hlink tr t r pub hcur
  have h2:∀e∈(Scan.body.drop 23).take 26,e.eval tr t r pub=0 := by
    by_cases hi:rho<19
    · apply ProcScanRequestBodyInterior.physical R c rho jj cv hi tr t r pub hcur
      intro col
      rw [hnext hi col,ProcScanRequestState.native_at R c (rho+1) (by omega)]
      have hs:=ProcScanRequestState.succ R c rho
      have hh:(ProcScanRequestState.state R c (rho+1)).2.2=nextCur R c rho cv:=by rw [hs];rfl
      rw [hh,←ProcScanRequestCount.next c rho]
      rfl
    · have he:rho=19:=by omega
      subst rho
      exact ProcScanRequestBodyTerminal.physical R c jj cv tr t r pub hcur
  have h3:=ProcScanRequestBodyEnd.physical R c rho cv hr hbits tr t r pub hcur
  have h4:=ProcScanRequestBodyBoundary.physical R c rho jj cv hr tr t r pub hcur hboundary
  have h5:=ProcScanRequestBodyTail.physical R c rho jj cv hk tr t r pub hcur
  apply join Scan.body _ 16 h0
  apply join (Scan.body.drop 16) _ 7 h1
  simp only [List.drop_drop,Nat.reduceAdd]
  apply join (Scan.body.drop 23) _ 26 h2
  simp only [List.drop_drop,Nat.reduceAdd]
  apply join (Scan.body.drop 49) _ 4 h3
  simp only [List.drop_drop,Nat.reduceAdd]
  apply join (Scan.body.drop 53) _ 6 h4
  simpa only [List.drop_drop,Nat.reduceAdd] using h5
end ZkFormal.NearV3.Candidates.ProcScanRequestBody
