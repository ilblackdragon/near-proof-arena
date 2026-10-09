import ZkFormal.NearV3.Candidates.ProcessRepairMemoryRequests
import ZkFormal.NearV3.Candidates.ProcessRepairRawBytes
namespace ZkFormal.NearV3.Candidates.ProcessRepairMemoryOrder
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder ProcPriorVerticalLastWrite
open ProcPriorCodecFamilyLastWrite (memory Ordered Bounded StampOrdered)
open ProcPriorRoutedMemoryRequests
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem adjacent_order {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    {r : Nat} (hr:r+1<tr.height 0) (ha:Live (memory tr) 0 r) (hn:Live (memory tr) 0 (r+1))
    (hx:address (memory tr) 0 r<2^29) (hy:address (memory tr) 0 (r+1)<2^29) :
    address (memory tr) 0 r≤address (memory tr) 0 (r+1) := by
  have hrm:r+1<(memory tr).height 0 :=hr
  have hcur:addr.eval (memory tr) 0 r pub=Fp.ofNat (address (memory tr) 0 r) :=
    Codec.ev_of (by simp only [address,addr,zev_add,zev_mul,zev_k,zev_c,cur_cv,Int.natCast_add,Int.natCast_mul])
  have hnext:nextAddr.eval (memory tr) 0 r pub=Fp.ofNat (address (memory tr) 0 (r+1)) :=
    Codec.ev_of (by simp only [address,nextAddr,zev_add,zev_mul,zev_k,zev_n,Codec.nx hrm,Int.natCast_add,Int.natCast_mul])
  have hm:(request 2).multNat tr 0 r pub=1 := by
    rw [request_mult]
    apply Codec.mult_of rfl
    change zev (tenv (memory tr) 0 r pub) (.mul (c (ProcPriorVertical4Linear.stage 0)) adjacent)=1
    simp only [adjacent,zev_mul,zev_c,zev_n,cur_cv,Codec.nx hrm,ha.1,ha.2,hn.2]
    rfl
  have hmsg:(request 2).msgVal tr 0 r pub=
      [Fp.ofNat (address (memory tr) 0 (r+1)),Fp.ofNat (address (memory tr) 0 r),1] := by
    rw [request_message]
    change [nextAddr.eval (memory tr) 0 r pub,addr.eval (memory tr) 0 r pub,Fp.ofNat 1]=_
    rw [hcur,hnext];rfl
  have hxp:address (memory tr) 0 r<P := by unfold P;omega
  have hyp:address (memory tr) 0 (r+1)<P := by unfold P;omega
  have hto (n : Nat) (h:n<P):(Fp.ofNat n).toNat=n := by simp only [Fp.toNat_ofNat,Nat.mod_eq_of_lt h]
  have he:=ProcessRepairMemoryRequests.compare view hpub 2 (by simp) (by omega) (by rw [hm];decide) hmsg
    (by rw [hto _ hyp];exact hy) (by rw [hto _ hxp];exact hx)
  simpa only [hto _ hxp,hto _ hyp] using he

theorem local_memory {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr) :
    ProcPriorVerticalMemorySound.LocalV (memory tr) 0 pub := by
  exact ProcessRepairRawBytes.overlay_local view

theorem ordered {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    (hb:∀r,r<tr.height 0→Live (memory tr) 0 r→address (memory tr) 0 r<2^29) :Ordered tr := by
  have hL:=local_memory view
  intro s hs ha r hrs
  induction s generalizing r with
  | zero=>have :r=0 := by omega
          subst r;exact Nat.le_refl _
  | succ s ih=>
    by_cases he:r=s+1
    · subst r;exact Nat.le_refl _
    · have hp:=live_prev hL hs ha
      have hsp:s<tr.height 0 := by omega
      exact Nat.le_trans (ih hsp hp r (by omega))
        (adjacent_order view hpub hs hp ha (hb s hsp hp) (hb (s+1) hs ha))

theorem next_write_order {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    {r : Nat} (hr:r+1<tr.height 0) (ha:Live (memory tr) 0 r) (hn:Live (memory tr) 0 (r+1))
    (had:address (memory tr) 0 r=address (memory tr) 0 (r+1)) (hq:cv (memory tr) 0 (r+1) query=0)
    (hx:cv (memory tr) 0 r stamp+1<2^29) (hy:cv (memory tr) 0 (r+1) stamp<2^29) :
    cv (memory tr) 0 r stamp<cv (memory tr) 0 (r+1) stamp := by
  have hrm:r+1<(memory tr).height 0 :=hr
  have hL:=local_memory view
  have hs:=ProcPriorMemoryLastWrite.same_of_address (live_local hL (show r<(memory tr).height 0 by omega) ha) hrm ha.2 hn.2 had
  have hg:=gate_value hL (show r<(memory tr).height 0 by exact Nat.lt_trans (Nat.lt_succ_self _) hr) ha.1
  have hgate:ProcPriorMemoryGated.gateExpr.eval (memory tr) 0 r pub=1 :=
    Codec.ev_of (by simp only [ProcPriorMemoryGated.gateExpr,adjacent,notE,zev_mul,zev_sub,zev_k,zev_c,zev_n,
      cur_cv,Codec.nx hrm,ha.2,hn.2,hs,hq];rfl)
  have hgc:(c ProcPriorMemoryGated.stampGate).eval (memory tr) 0 r pub=1 := by
    simp only [ProcPriorMemoryGated.gateEq,sub,ZkFormal.Near.eval_add,ZkFormal.Near.eval_neg,hgate] at hg
    grind only
  have hm:(request 3).multNat tr 0 r pub=1 := by
    rw [request_mult]
    have hstage:(c (ProcPriorVertical4Linear.stage 0)).eval (memory tr) 0 r pub=1 := by rw [Codec.ev_c,ha.1];rfl
    change (if (c (ProcPriorVertical4Linear.stage 0)).eval (memory tr) 0 r pub*
      (c ProcPriorMemoryGated.stampGate).eval (memory tr) 0 r pub=1 then 1 else 0)+0=1
    rw [hstage,hgc]
    decide +kernel
  have hcur:(.add (c stamp) (k 1) : Expr).eval (memory tr) 0 r pub=Fp.ofNat (cv (memory tr) 0 r stamp+1) :=
    Codec.ev_of (by simp only [zev_add,zev_c,zev_k,cur_cv,Int.natCast_add,Int.natCast_one])
  have hnext:(n stamp).eval (memory tr) 0 r pub=Fp.ofNat (cv (memory tr) 0 (r+1) stamp) :=
    Codec.ev_of (by simp only [zev_n,Codec.nx hrm])
  have hmsg:(request 3).msgVal tr 0 r pub=
      [Fp.ofNat (cv (memory tr) 0 (r+1) stamp),Fp.ofNat (cv (memory tr) 0 r stamp+1),1] := by
    rw [request_message]
    change [(n stamp).eval (memory tr) 0 r pub,(.add (c stamp) (k 1) :Expr).eval (memory tr) 0 r pub,Fp.ofNat 1]=_
    rw [hcur,hnext];rfl
  have hxp:cv (memory tr) 0 r stamp+1<P := by unfold P;omega
  have hyp:cv (memory tr) 0 (r+1) stamp<P := by unfold P;omega
  have hto (n : Nat) (h:n<P):(Fp.ofNat n).toNat=n := by simp only [Fp.toNat_ofNat,Nat.mod_eq_of_lt h]
  have he:=ProcessRepairMemoryRequests.compare view hpub 3 (by simp) (by omega) (by rw [hm];decide) hmsg
    (by rw [hto _ hyp];exact hy) (by rw [hto _ hxp];exact hx)
  rw [hto _ hxp,hto _ hyp] at he
  omega

theorem stamp_ordered {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    (hb:∀r,r<tr.height 0→Live (memory tr) 0 r→cv (memory tr) 0 r query=0→
      cv (memory tr) 0 r stamp+1<2^29) :StampOrdered tr := by
  intro r hr ha hn had hq
  have hrm:r+1<(memory tr).height 0 :=hr
  have hL:=local_memory view
  have hl:=live_local hL (show r<(memory tr).height 0 by omega) ha
  have hq0:cv (memory tr) 0 r query=0 := by
    have hbit:=ProcPriorMemorySoundRows.flag hl (x:=query) (by simp)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hbit with hz|hz
    · exact hz
    · exact (ProcPriorMemoryLastWrite.query_stop hl hrm ha.2 hn.2 hz had).elim
  exact next_write_order view hpub hr ha hn had hq (hb r (by omega) ha hq0)
    (by have :=hb (r+1) hr hn hq;omega)

/-- All comparison/order premises of the stage0 last-write theorem are now
consequences of actual shared-comparator family validity. Only authenticated
natural address bounds and original-write ordinal bounds remain. -/
theorem order_predicates {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    (ha:∀r,r<tr.height 0→Live (memory tr) 0 r→address (memory tr) 0 r<2^29)
    (hs:∀r,r<tr.height 0→Live (memory tr) 0 r→cv (memory tr) 0 r query=0→
      cv (memory tr) 0 r stamp+1<2^29) :Ordered tr ∧ Bounded tr ∧ StampOrdered tr := by
  refine ⟨ordered view hpub ha,?_,stamp_ordered view hpub hs⟩
  intro r hr hl
  have :=ha r hr hl
  unfold P;omega
end ZkFormal.NearV3.Candidates.ProcessRepairMemoryOrder
