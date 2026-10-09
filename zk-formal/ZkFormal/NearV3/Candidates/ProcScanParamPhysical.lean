import ZkFormal.NearV3.Candidates.ProcScanParamLocal
namespace ZkFormal.NearV3.Candidates.ProcScanParamPhysical
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open SchedSetAll ProcScanParamLocal
private theorem lookup_bound (xs:List (Nat×Nat))(c v B:Nat)(hv:v<B)
    (h:∀p∈xs,p.2<B) : lookup xs c v<B := by
  induction xs generalizing v with
  | nil=>exact hv
  | cons p ps ih=>
    unfold lookup
    rw [List.foldl_cons]
    apply ih
    · split
      · exact h p (by simp)
      · exact hv
    · intro q hq;exact h q (by simp [hq])

set_option maxRecDepth 32768
set_option maxHeartbeats 800000

theorem row_all (R:Run)(c:Nat) : (Scan.paramRow R)[c]! =lookup (assignments R) c 0 := by
  by_cases hc:c<Scan.width
  · exact row_cell R c hc
  · have hsize:(Scan.paramRow R).size=Scan.width := by rw [row_eq,SchedSetAll.width]
    rw [getElem!_neg _ _ (by omega)]
    symm
    apply lookup_miss
    simp only [assignments,List.forall_mem_cons,List.forall_mem_nil]
    simp [Scan.width,Scan.act,Scan.kP,Scan.tau,Scan.nn,Scan.base,Scan.dd,Scan.q,Scan.clo,Scan.chi,
      Dist.width,Dist.act,Dist.kP,Dist.tau,Dist.nn,Dist.a,Dist.r,Dist.fw] at hc ⊢
    omega

theorem row_small (R:Run)(ht:R.tau<P)(hn:R.n<P)(hb:R.base<256^3)(hd:R.D<256^3)(c:Nat) :
    (Scan.paramRow R)[c]! < P := by
  rw [row_all]
  refine lookup_bound (assignments R) c 0 P (by decide) ?_
  simp only [assignments,List.forall_mem_cons,List.forall_mem_nil]
  simp only [Scan.byteOf]
  have hm:∀x:Nat,x%256<256:=fun x=>Nat.mod_lt x (by decide)
  simp only [P] at ht hn ⊢
  repeat' apply And.intro
  all_goals first | exact ht | exact hn | omega | simp

theorem native_bounds (I:Input)(tau:Nat)(R:Run)(hr:ActualRun.run I tau=.ok R) :
    R.base<256^3 ∧ R.D<256^3 := by
  have hp:=ProcActualRunProjection.run_params I tau R hr
  have hf:=ProcActualRunProjection.run_fields I tau R hr
  rw [hf.2.2.1,hf.2.2.2.1]
  exact hp

theorem physical (I:Input)(tau:Nat)(R:Run)(hr:ActualRun.run I tau=.ok R)
    (ht:R.tau<P)(hn:R.n<P)(tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀c,tr.cell t r c=Fp.ofNat (Scan.paramRow R)[c]!)
    (hl:r+1<tr.height t)
    (hf:tr.cell t ((r+1)%tr.height t) Scan.fQ=1)
    (hcid:tr.cell t ((r+1)%tr.height t) Scan.cid=0)
    (hnt:tr.cell t ((r+1)%tr.height t) Scan.tau=Fp.ofNat R.tau)
    (hnn:tr.cell t ((r+1)%tr.height t) Scan.nn=Fp.ofNat R.n)
    (hnb:tr.cell t ((r+1)%tr.height t) Scan.base=Fp.ofNat R.base)
    (hnd:tr.cell t ((r+1)%tr.height t) Scan.dd=Fp.ofNat R.D) :
    ∀e∈ScanDist.constraints,e.eval tr t r pub=0 := by
  have hp:=native_bounds I tau R hr
  have hbase:R.base<P:=by unfold P;omega
  have hD:R.D<P:=by unfold P;omega
  intro e he
  apply eval_zero_of
  apply constraints R (tenv tr t r pub) _ _ _ _ _ _ _ _ hp.1 hp.2 e he
  · intro c
    change Int.ofNat ((tr.cell t r c).toNat)=_
    rw [hrow,Fp.toNat_ofNat,Nat.mod_eq_of_lt (row_small R ht hn hp.1 hp.2 c),row_all]
  · simp [tenv,show r+1≠tr.height t by omega]
  · change ((tr.cell t ((r+1)%tr.height t) Scan.fQ).toNat)=1
    rw [hf];rfl
  · change ((tr.cell t ((r+1)%tr.height t) Scan.cid).toNat)=0
    rw [hcid];rfl
  · change ((tr.cell t ((r+1)%tr.height t) Scan.tau).toNat)=_
    rw [hnt,Fp.toNat_ofNat,Nat.mod_eq_of_lt ht]
  · change ((tr.cell t ((r+1)%tr.height t) Scan.nn).toNat)=_
    rw [hnn,Fp.toNat_ofNat,Nat.mod_eq_of_lt hn]
  · change ((tr.cell t ((r+1)%tr.height t) Scan.base).toNat)=_
    rw [hnb,Fp.toNat_ofNat,Nat.mod_eq_of_lt hbase]
  · change ((tr.cell t ((r+1)%tr.height t) Scan.dd).toNat)=_
    rw [hnd,Fp.toNat_ofNat,Nat.mod_eq_of_lt hD]

end ZkFormal.NearV3.Candidates.ProcScanParamPhysical
