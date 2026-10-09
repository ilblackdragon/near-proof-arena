import ZkFormal.NearV3.Candidates.ProcPriorCodecGridComplete
import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundIndex
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGridCarry
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
open ProcPriorCodecSoundGeometry
variable {tr:Trace Fp} {t:Nat} {pub:List Fp}
set_option maxHeartbeats 1000000

theorem end_zero (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r:Nat}
    (hr:r<tr.height t) (hs:cv tr t r rs=1) {i:Nat} (hi:i<23) :
    cv tr t (r+i) rend=0 := by
  obtain ⟨hb,hR⟩:=ProcPriorCodecGridStride.record_rows hL hr hs i (by omega)
  have K:=kinds hL hb
  obtain ⟨q,hq⟩:=Mem.zdvd hL hb (rec_member
    (sub (c rend) (.mul (c fA) (c e7))) (by simp [cRec]) (by decide +kernel))
  have lr:=Codec.lt (tr:=tr) (t:=t) (r+i) rend
  by_cases h8:i<8
  · have hS:=(sender_walk hL hr hs i h8).2.1
    have hA:cv tr t (r+i) fA=0:=by omega
    zs hq [hA];omega
  · by_cases h16:i<16
    · have hF:=(ProcPriorCodecSoundReceiver.receiver_walk hL hr hs (i-8) (by omega)).2.1
      rw [show r+8+(i-8)=r+i by omega] at hF
      have hA:cv tr t (r+i) fA=0:=by omega
      zs hq [hA];omega
    · have hg:=(ProcPriorCodecGridAmount.amount_walk hL hr hs (i-16) (by omega)).2.2.1
      rw [show r+16+(i-16)=r+i by omega] at hg
      have h7:=e7_zero hL hb hR (by omega)
      zs hq [h7];omega

theorem next (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r:Nat}
    (hr:r+1<tr.height t) (hR:cv tr t r kR=1) (he:cv tr t r rend=0)
    (x:Nat) (hx:x∈[al,gb,srcC,hasC,useC]) :cv tr t (r+1) x=cv tr t r x := by
  obtain ⟨q,hq⟩:=Mem.zdvd hL (show r<tr.height t by omega) (rec_member
    (.mul (sub (c kR) (c rend)) (sub (n x) (c x))) (by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp [cRec]) (by
      have hh:∀x∈[al,gb,srcC,hasC,useC],ProcPriorCodecActual.retiredRec.contains
        (.mul (sub (c kR) (c rend)) (sub (n x) (c x)))=false:=by decide +kernel
      exact hh x hx))
  zs hq [hR,he,nx hr]
  have :=Codec.lt (tr:=tr) (t:=t) r x
  have :=Codec.lt (tr:=tr) (t:=t) (r+1) x
  omega

theorem record (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r:Nat}
    (hr:r<tr.height t) (hs:cv tr t r rs=1) (x:Nat) (hx:x∈[al,gb,srcC,hasC,useC]) :
    ∀i,i<24→cv tr t (r+i) x=cv tr t r x := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
    intro hi
    have hb:=(ProcPriorCodecGridStride.record_rows hL hr hs (i+1) hi).1
    have hR:=(ProcPriorCodecGridStride.record_rows hL hr hs i (by omega)).2
    have he:=end_zero hL hr hs (i:=i) (by omega)
    have hc:=next hL (r:=r+i) (by simpa [Nat.add_assoc] using hb) hR he x hx
    simpa [Nat.add_assoc] using hc.trans (ih (by omega))
end ZkFormal.NearV3.Candidates.ProcPriorCodecGridCarry
