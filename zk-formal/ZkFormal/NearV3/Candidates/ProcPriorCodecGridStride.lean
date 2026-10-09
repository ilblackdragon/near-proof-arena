import ZkFormal.NearV3.Candidates.ProcPriorCodecGridNext
import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundOrigin
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGridStride
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
open ProcPriorCodecSoundGeometry
variable {tr:Trace Fp} {t:Nat} {pub:List Fp}
set_option maxHeartbeats 1000000

theorem record_rows (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r:Nat}
    (hr:r<tr.height t) (hs:cv tr t r rs=1) :
    ∀i,i<24→r+i<tr.height t ∧ cv tr t (r+i) kR=1 := by
  intro i hi
  by_cases h8:i<8
  · obtain ⟨hb,hS,_⟩:=sender_walk hL hr hs i h8
    have K:=kinds hL hb
    exact ⟨hb,by omega⟩
  · by_cases h16:i<16
    · obtain ⟨hb,hR,_⟩:=ProcPriorCodecSoundReceiver.receiver_walk hL hr hs (i-8) (by omega)
      have he:r+8+(i-8)=r+i:=by omega
      rw [he] at hb hR
      have K:=kinds hL hb
      exact ⟨hb,by omega⟩
    · obtain ⟨hb,hA,_⟩:=ProcPriorCodecGridAmount.amount_walk hL hr hs (i-16) (by omega)
      have he:r+16+(i-16)=r+i:=by omega
      rw [he] at hb hA
      have K:=kinds hL hb
      exact ⟨hb,by omega⟩

theorem constant_record (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r:Nat}
    (hr:r<tr.height t) (hs:cv tr t r rs=1) (x:Nat)
    (hx:x∈[tau,pres,vid,nn,NN,base,fair]) :
    ∀i,i<24→cv tr t (r+i) x=cv tr t r x := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro hi
    obtain ⟨hb,hR⟩:=record_rows hL hr hs (i+1) hi
    have K:=kinds hL hb
    have hc:=ProcPriorCodecSoundOrigin.constant_next hL x hx
      (r:=r+i) (by simpa [Nat.add_assoc] using hb)
      (by simpa [Nat.add_assoc] using (show cv tr t (r+(i+1)) act=1 by omega))
      (by simpa [Nat.add_assoc] using (show cv tr t (r+(i+1)) kF=0 by omega))
    simpa [Nat.add_assoc] using hc.trans (ih (by omega))

theorem next_record (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r:Nat}
    (hr:r<tr.height t) (hs:cv tr t r rs=1)
    (hk:cv tr t r kidx+1<cv tr t r NN) (hN:cv tr t r NN≤4096) :
    r+24<tr.height t ∧ cv tr t (r+24) rs=1 ∧
    cv tr t (r+24) kidx=cv tr t r kidx+1 ∧
    ∀x∈[tau,pres,vid,nn,NN,base,fair],cv tr t (r+24) x=cv tr t r x := by
  obtain ⟨hb,hA,hg,hki,_⟩:=ProcPriorCodecGridAmount.amount_walk hL hr hs 7 (by decide)
  have hn:=constant_record hL hr hs NN (by simp) 23 (by decide)
  have he:r+16+7=r+23:=by omega
  rw [he] at hb hA hg hki
  obtain ⟨hb1,hS1,hg1,hk1,hs1⟩:=ProcPriorCodecGridNext.amount_end hL hb hA hg
    (by omega) (by omega)
  have he1:r+23+1=r+24:=by omega
  rw [he1] at hb1 hS1 hg1 hk1 hs1
  refine ⟨hb1,hs1,by omega,?_⟩
  intro x hx
  have K:=kinds hL hb1
  have hc:=ProcPriorCodecSoundOrigin.constant_next hL x hx
    (r:=r+23) (by omega)
    (by simpa only [he1] using (show cv tr t (r+24) act=1 by omega))
    (by simpa only [he1] using (show cv tr t (r+24) kF=0 by omega))
  rw [he1] at hc
  exact hc.trans (constant_record hL hr hs x hx 23 (by decide))
end ZkFormal.NearV3.Candidates.ProcPriorCodecGridStride
