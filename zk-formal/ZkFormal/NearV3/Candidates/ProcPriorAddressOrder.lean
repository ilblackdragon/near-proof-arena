import ZkFormal.NearV3.Candidates.ProcComparatorSound
import ZkFormal.NearV3.Candidates.ProcPriorMemorySoundRows
namespace ZkFormal.NearV3.Candidates.ProcPriorAddressOrder
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorMemoryTable

def address (tr : Trace Fp) (t r : Nat) : Nat := 4096*cv tr t r tau+cv tr t r link

theorem adjacent_order {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) {tc t r : Nat} (own:ProcComparatorSound.Own AP tc 69)
    (ht:t<AP.tables.length) (hr:r+1<tr.height t)
    (hi:(interactions 67 68 69)[2]!∈AP.tables[t]!.interactions)
    (ha:cv tr t r act=1) (hn:cv tr t (r+1) act=1)
    (hx:address tr t r<2^29) (hy:address tr t (r+1)<2^29) :
    address tr t r≤address tr t (r+1) := by
  have hcur:addr.eval tr t r pub=Fp.ofNat (address tr t r) :=
    Codec.ev_of (by simp only [address,addr,zev_add,zev_mul,zev_k,zev_c,cur_cv,Int.natCast_add,Int.natCast_mul])
  have hnext:nextAddr.eval tr t r pub=Fp.ofNat (address tr t (r+1)) :=
    Codec.ev_of (by simp only [address,nextAddr,zev_add,zev_mul,zev_k,zev_n,Codec.nx hr,Int.natCast_add,Int.natCast_mul])
  have hag:adjacent.eval tr t r pub=1 :=
    Codec.ev_of (by simp only [adjacent,zev_mul,zev_c,zev_n,cur_cv,Codec.nx hr,ha,hn];rfl)
  have hm:((interactions 67 68 69)[2]!).multNat tr t r pub≠0 := by
    simp [interactions,Interaction.multNat,Interaction.multNat.go,hag]
  have hmsg:((interactions 67 68 69)[2]!).msgVal tr t r pub=
      [Fp.ofNat (address tr t (r+1)),Fp.ofNat (address tr t r),1] := by
    simp only [interactions,List.getElem!_cons_succ,List.getElem!_cons_zero,Interaction.msgVal,
      List.map_cons,List.map_nil,hcur,hnext]
    rfl
  have hxp:address tr t r<P := by unfold P;omega
  have hyp:address tr t (r+1)<P := by unfold P;omega
  have hto (n : Nat) (h:n<P):(Fp.ofNat n).toNat=n := by simp only [Fp.toNat_ofNat,Nat.mod_eq_of_lt h]
  have he:=ProcComparatorSound.prior_ge hH own ht (by omega) hi rfl rfl hm hmsg
    (by rw [hto _ hyp];exact hy) (by rw [hto _ hxp];exact hx)
  simpa only [hto _ hxp,hto _ hyp] using he
/-- Ordering holds throughout the active prefix, not only for one pair.
The active-prefix fact follows from memory constraints; address ranges and
actual comparator interaction membership are still explicit obligations. -/
theorem active_order {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) {tc t : Nat} (own:ProcComparatorSound.Own AP tc 69)
    (ht:t<AP.tables.length)
    (hi:(interactions 67 68 69)[2]!∈AP.tables[t]!.interactions)
    (hL:ProcPriorMemorySound.LocalM tr t pub)
    (hbound:∀r,r<tr.height t→cv tr t r act=1→address tr t r<2^29)
    (s : Nat) (hs:s<tr.height t) (ha:cv tr t s act=1)
    (r : Nat) (hrs:r≤s) : address tr t r≤address tr t s := by
  induction s generalizing r with
  | zero=>have :r=0 := by omega
          subst r
          exact Nat.le_refl _
  | succ s ih=>
    by_cases he:r=s+1
    · subst r;exact Nat.le_refl _
    · have hp:=ProcPriorMemorySound.active_prev hL hs ha
      have hsp:s<tr.height t := by omega
      have hleft:=ih hsp hp r (by omega)
      have hright:=adjacent_order hH own ht hs hi hp ha (hbound s hsp hp) (hbound (s+1) hs ha)
      exact Nat.le_trans hleft hright

end ZkFormal.NearV3.Candidates.ProcPriorAddressOrder
