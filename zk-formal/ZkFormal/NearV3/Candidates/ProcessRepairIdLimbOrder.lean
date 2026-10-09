import ZkFormal.NearV3.Candidates.ProcessRepairIdOrder
import ZkFormal.NearV3.Candidates.ProcPriorIdPrefixGates
import ZkFormal.NearV3.Candidates.ProcPriorIdInterval
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdLimbOrder
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorIdTable ProcessRepairIdComparisons ProcessRepairIdOrder
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxHeartbeats 1000000
theorem middle_order {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    {r : Nat} (hr:r+1<tr.height 0) (ha:Live (memory tr) r) (hn:Live (memory tr) (r+1))
    (hg:cv (memory tr) 0 r gTop=1)
    (hx:cv (memory tr) 0 r keyMid<2^29) (hy:cv (memory tr) 0 (r+1) keyMid<2^29) :
    cv (memory tr) 0 r keyMid≤cv (memory tr) 0 (r+1) keyMid := by
  have hrm:r+1<(memory tr).height 0 :=hr
  have hcur:(c keyMid).eval (memory tr) 0 r pub=Fp.ofNat (cv (memory tr) 0 r keyMid) := Codec.ev_c _ _
  have hnext:(n keyMid).eval (memory tr) 0 r pub=Fp.ofNat (cv (memory tr) 0 (r+1) keyMid) :=
    Codec.ev_of (by simp only [zev_n,Codec.nx hrm])
  have hm:(request 4).multNat tr 0 r pub=1 := by
    rw [request_mult]
    apply Codec.mult_of rfl
    change zev (tenv (memory tr) 0 r pub) (.mul (c (ProcPriorVertical4Linear.stage 1)) (c gTop))=1
    simp only [adjacent,zev_mul,zev_c,zev_n,cur_cv,Codec.nx hrm,ha.1,hg]
    rfl
  have hmsg:(request 4).msgVal tr 0 r pub=
      [Fp.ofNat (cv (memory tr) 0 (r+1) keyMid),Fp.ofNat (cv (memory tr) 0 r keyMid),1] := by
    rw [request_message]
    change [(n keyMid).eval (memory tr) 0 r pub,(c keyMid).eval (memory tr) 0 r pub,Fp.ofNat 1]=_
    rw [hcur,hnext];rfl
  have hxp:cv (memory tr) 0 r keyMid<P := by unfold P;omega
  have hyp:cv (memory tr) 0 (r+1) keyMid<P := by unfold P;omega
  have hto (n : Nat) (h:n<P):(Fp.ofNat n).toNat=n := by simp only [Fp.toNat_ofNat,Nat.mod_eq_of_lt h]
  have he:=ProcessRepairIdComparisons.compare view hpub 4 (by simp) (by omega) (by rw [hm];decide) hmsg
    (by rw [hto _ hyp];exact hy) (by rw [hto _ hxp];exact hx)
  simpa only [hto _ hxp,hto _ hyp] using he

theorem lower_order {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    {r : Nat} (hr:r+1<tr.height 0) (ha:Live (memory tr) r) (hn:Live (memory tr) (r+1))
    (hg:cv (memory tr) 0 r gMid=1)
    (hx:cv (memory tr) 0 r keyLo<2^29) (hy:cv (memory tr) 0 (r+1) keyLo<2^29) :
    cv (memory tr) 0 r keyLo≤cv (memory tr) 0 (r+1) keyLo := by
  have hrm:r+1<(memory tr).height 0 :=hr
  have hcur:(c keyLo).eval (memory tr) 0 r pub=Fp.ofNat (cv (memory tr) 0 r keyLo) := Codec.ev_c _ _
  have hnext:(n keyLo).eval (memory tr) 0 r pub=Fp.ofNat (cv (memory tr) 0 (r+1) keyLo) :=
    Codec.ev_of (by simp only [zev_n,Codec.nx hrm])
  have hm:(request 5).multNat tr 0 r pub=1 := by
    rw [request_mult]
    apply Codec.mult_of rfl
    change zev (tenv (memory tr) 0 r pub) (.mul (c (ProcPriorVertical4Linear.stage 1)) (c gMid))=1
    simp only [adjacent,zev_mul,zev_c,zev_n,cur_cv,Codec.nx hrm,ha.1,hg]
    rfl
  have hmsg:(request 5).msgVal tr 0 r pub=
      [Fp.ofNat (cv (memory tr) 0 (r+1) keyLo),Fp.ofNat (cv (memory tr) 0 r keyLo),1] := by
    rw [request_message]
    change [(n keyLo).eval (memory tr) 0 r pub,(c keyLo).eval (memory tr) 0 r pub,Fp.ofNat 1]=_
    rw [hcur,hnext];rfl
  have hxp:cv (memory tr) 0 r keyLo<P := by unfold P;omega
  have hyp:cv (memory tr) 0 (r+1) keyLo<P := by unfold P;omega
  have hto (n : Nat) (h:n<P):(Fp.ofNat n).toNat=n := by simp only [Fp.toNat_ofNat,Nat.mod_eq_of_lt h]
  have he:=ProcessRepairIdComparisons.compare view hpub 5 (by simp) (by omega) (by rw [hm];decide) hmsg
    (by rw [hto _ hyp];exact hy) (by rw [hto _ hxp];exact hx)
  simpa only [hto _ hxp,hto _ hyp] using he

end ZkFormal.NearV3.Candidates.ProcessRepairIdLimbOrder
