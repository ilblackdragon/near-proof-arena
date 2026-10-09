import ZkFormal.NearV3.Candidates.ProcComparatorSound
import ZkFormal.NearV3.Candidates.ProcPriorMemorySoundRows
namespace ZkFormal.NearV3.Candidates.ProcPriorStampOrder
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorMemoryTable

/-- Within an address group, successive writes have increasing original
ordinals. The gate equality is the actual gated-memory row constraint. -/
theorem next_write_order {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) {tc t r : Nat} (own:ProcComparatorSound.Own AP tc 69)
    (ht:t<AP.tables.length) (hr:r+1<tr.height t)
    (hi:(ProcPriorMemoryGated.interactions 67 68 69)[3]!∈AP.tables[t]!.interactions)
    (hg:ProcPriorMemoryGated.gateEq.eval tr t r pub=0)
    (ha:cv tr t r act=1) (hn:cv tr t (r+1) act=1)
    (hs:cv tr t r same=1) (hq:cv tr t (r+1) query=0)
    (hx:cv tr t r stamp+1<2^29) (hy:cv tr t (r+1) stamp<2^29) :
    cv tr t r stamp<cv tr t (r+1) stamp := by
  have hgate:ProcPriorMemoryGated.gateExpr.eval tr t r pub=1 :=
    Codec.ev_of (by simp only [ProcPriorMemoryGated.gateExpr,adjacent,notE,
      zev_mul,zev_sub,zev_k,zev_c,zev_n,cur_cv,Codec.nx hr,ha,hn,hs,hq];rfl)
  have hgc:(c ProcPriorMemoryGated.stampGate).eval tr t r pub=1 := by
    simp only [ProcPriorMemoryGated.gateEq,sub,ZkFormal.Near.eval_add,ZkFormal.Near.eval_neg,hgate] at hg
    grind only
  have hm:((ProcPriorMemoryGated.interactions 67 68 69)[3]!).multNat tr t r pub≠0 := by
    simp [ProcPriorMemoryGated.interactions,interactions,Interaction.multNat,Interaction.multNat.go,hgc]
  have hcur:(.add (c stamp) (k 1) : Expr).eval tr t r pub=Fp.ofNat (cv tr t r stamp+1) :=
    Codec.ev_of (by simp only [zev_add,zev_c,zev_k,cur_cv,Int.natCast_add,Int.natCast_one])
  have hnext:(n stamp).eval tr t r pub=Fp.ofNat (cv tr t (r+1) stamp) :=
    Codec.ev_of (by simp only [zev_n,Codec.nx hr])
  have hmsg:((ProcPriorMemoryGated.interactions 67 68 69)[3]!).msgVal tr t r pub=
      [Fp.ofNat (cv tr t (r+1) stamp),Fp.ofNat (cv tr t r stamp+1),1] := by
    simp [ProcPriorMemoryGated.interactions,interactions,Interaction.msgVal,hcur,hnext]
    rfl
  have hxp:cv tr t r stamp+1<P := by unfold P;omega
  have hyp:cv tr t (r+1) stamp<P := by unfold P;omega
  have hto (n : Nat) (h:n<P):(Fp.ofNat n).toNat=n := by simp only [Fp.toNat_ofNat,Nat.mod_eq_of_lt h]
  have he:=ProcComparatorSound.prior_ge hH own ht (by omega) hi rfl rfl hm hmsg
    (by rw [hto _ hyp];exact hy) (by rw [hto _ hxp];exact hx)
  rw [hto _ hxp,hto _ hyp] at he
  omega
end ZkFormal.NearV3.Candidates.ProcPriorStampOrder
