import ZkFormal.NearV3.Candidates.ProcessRepairIdComparisons
import ZkFormal.NearV3.Candidates.ProcessRepairIdRowBounds
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdOrder
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorIdTable ProcessRepairIdComparisons
open ProcPriorCodecFamilyLastWrite (memory)
def Live (tr:Trace Fp) (r:Nat):Prop :=cv tr 0 r (ProcPriorVertical4Linear.stage 1)=1 ∧ cv tr 0 r act=1
def keyTop (tr:Trace Fp) (r:Nat):Nat :=65536*cv tr 0 r tau+cv tr 0 r keyHi
set_option maxHeartbeats 1000000
theorem top_order {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    {r : Nat} (hr:r+1<tr.height 0) (ha:Live (memory tr) r) (hn:Live (memory tr) (r+1))
    (hx:keyTop (memory tr) r<2^29) (hy:keyTop (memory tr) (r+1)<2^29) :
    keyTop (memory tr) r≤keyTop (memory tr) (r+1) := by
  have hrm:r+1<(memory tr).height 0 :=hr
  have hcur:(top false).eval (memory tr) 0 r pub=Fp.ofNat (keyTop (memory tr) r) :=
    Codec.ev_of (by
      change zev (tenv (memory tr) 0 r pub) (.add (.mul (k 65536) (c tau)) (c keyHi))=_
      simp only [keyTop,zev_add,zev_mul,zev_k,zev_c,cur_cv,Int.natCast_add,Int.natCast_mul])
  have hnext:(top true).eval (memory tr) 0 r pub=Fp.ofNat (keyTop (memory tr) (r+1)) :=
    Codec.ev_of (by
      change zev (tenv (memory tr) 0 r pub) (.add (.mul (k 65536) (n tau)) (n keyHi))=_
      simp only [keyTop,zev_add,zev_mul,zev_k,zev_n,Codec.nx hrm,Int.natCast_add,Int.natCast_mul])
  have hm:(request 3).multNat tr 0 r pub=1 := by
    rw [request_mult]
    apply Codec.mult_of rfl
    change zev (tenv (memory tr) 0 r pub) (.mul (c (ProcPriorVertical4Linear.stage 1)) adjacent)=1
    simp only [adjacent,zev_mul,zev_c,zev_n,cur_cv,Codec.nx hrm,ha.1,ha.2,hn.2]
    rfl
  have hmsg:(request 3).msgVal tr 0 r pub=
      [Fp.ofNat (keyTop (memory tr) (r+1)),Fp.ofNat (keyTop (memory tr) r),1] := by
    rw [request_message]
    change [(top true).eval (memory tr) 0 r pub,(top false).eval (memory tr) 0 r pub,Fp.ofNat 1]=_
    rw [hcur,hnext];rfl
  have hxp:keyTop (memory tr) r<P := by unfold P;omega
  have hyp:keyTop (memory tr) (r+1)<P := by unfold P;omega
  have hto (n : Nat) (h:n<P):(Fp.ofNat n).toNat=n := by simp only [Fp.toNat_ofNat,Nat.mod_eq_of_lt h]
  have he:=ProcessRepairIdComparisons.compare view hpub 3 (by simp) (by omega) (by rw [hm];decide) hmsg
    (by rw [hto _ hyp];exact hy) (by rw [hto _ hxp];exact hx)
  simpa only [hto _ hxp,hto _ hyp] using he

end ZkFormal.NearV3.Candidates.ProcessRepairIdOrder
