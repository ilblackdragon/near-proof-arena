import ZkFormal.NearV3.Candidates.ProcDistHeader
namespace ZkFormal.NearV3.Candidates.ProcDistHeaderPhysical
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open SchedSetAll ProcDistHeader
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

theorem row_all (tv n i sv count left c:Nat) :
    (row tv n i sv count left)[c]! =lookup (assignments tv n i sv count left) c 0 := by
  by_cases hc:c<Dist.width
  · exact cell _ _ _ hc
  · have hsize:(row tv n i sv count left).size=Dist.width:=SchedSetAll.width _ _
    rw [getElem!_neg _ _ (by omega)]
    symm
    apply lookup_miss
    simp only [assignments,List.forall_mem_cons,List.forall_mem_nil]
    simp [Dist.width,Dist.act,Dist.kGH,Dist.tau,Dist.nn,Dist.a,Dist.b,Dist.r,Dist.N2,Dist.L2,Dist.dlrg] at hc ⊢
    omega

theorem small (tv n i sv count left c:Nat)(ht:tv<P)(hn:n<P)(hi:i<P)(hs:sv<P)(hN:count<P)(hL:left<P) :
    (row tv n i sv count left)[c]! <P := by
  rw [row_all]
  apply lookup_bound _ c 0 P (by decide)
  simp [assignments,ht,hn,hi,hs,hN,hL]
  decide

theorem physical (tv n i sv count left:Nat)(ht:tv<P)(hn:n<P)(hi:i<P)(hs:sv<P)(hN:count<P)(hL:left<P)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀c,tr.cell t r c=Fp.ofNat (row tv n i sv count left)[c]!)
    (hf:r≠0)(hl:r+1<tr.height t)
    (hc:tr.cell t ((r+1)%tr.height t) Dist.kC=1)
    (hb:tr.cell t ((r+1)%tr.height t) Dist.b=0)
    (ha:tr.cell t ((r+1)%tr.height t) Dist.a=Fp.ofNat i)
    (hsv:tr.cell t ((r+1)%tr.height t) Dist.s=Fp.ofNat sv)
    (hcnt:tr.cell t ((r+1)%tr.height t) Dist.N1=Fp.ofNat count)
    (hleft:tr.cell t ((r+1)%tr.height t) Dist.L1=Fp.ofNat left)
    (htv:tr.cell t ((r+1)%tr.height t) Dist.tau=Fp.ofNat tv)
    (hnn:tr.cell t ((r+1)%tr.height t) Dist.nn=Fp.ofNat n) :
    ∀e∈ScanDist.constraints,e.eval tr t r pub=0 := by
  have ncell (col v:Nat)(hv:v<P)(he:tr.cell t ((r+1)%tr.height t) col=Fp.ofNat v) :
      (tenv tr t r pub).nxt col=v := by
    change (tr.cell t ((r+1)%tr.height t) col).toNat=_
    rw [he,Fp.toNat_ofNat,Nat.mod_eq_of_lt hv]
  intro e he
  apply eval_zero_of
  apply constraints tv n i sv count left (tenv tr t r pub) _ _ _
    (ncell _ 1 (by decide) hc) (ncell _ 0 (by decide) hb)
    (ncell _ i hi ha) (ncell _ sv hs hsv) (ncell _ count hN hcnt)
    (ncell _ left hL hleft) (ncell _ tv ht htv) (ncell _ n hn hnn) e he
  · intro c
    change Int.ofNat ((tr.cell t r c).toNat)=_
    rw [hrow,Fp.toNat_ofNat,Nat.mod_eq_of_lt (small tv n i sv count left c ht hn hi hs hN hL),row_all]
  · simp [tenv,hf]
  · simp [tenv,show r+1≠tr.height t by omega]
end ZkFormal.NearV3.Candidates.ProcDistHeaderPhysical
