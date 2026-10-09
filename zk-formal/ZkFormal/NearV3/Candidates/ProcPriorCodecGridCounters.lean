import ZkFormal.NearV3.Candidates.ProcPriorCodecGridCarry
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGridCounters
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
open ProcPriorCodecSoundGeometry ProcPriorCodecSoundIndex
variable {tr:Trace Fp} {t:Nat} {pub:List Fp}
set_option maxHeartbeats 1000000

theorem wrap (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r:Nat}
    (hr:r<tr.height t) (hs:cv tr t r rs=1)
    (hu:cv tr t r useC<cv tr t r nn) (hn:cv tr t r nn≤64) :
    cv tr t r hasC=if cv tr t r useC+1=cv tr t r nn then 1 else 0 := by
  have hS:=(start hL hr hs).1
  have hR:=(sender_kind hL hr hS).1
  have hb:=rec_bool hL hr hR (x:=hasC) (by simp [recBoolCols])
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (addition_member
    (.mul (c rs) (sub (c hasC) (notE (.mul (sub (c useC) (sub (c nn) (k 1))) (c ib)))))
    (by simp [ProcPriorCodecActual.additions,isZ]))
  obtain ⟨qz,hz⟩:=Mem.zdvd hL hr (addition_member
    (.mul (c rs) (.mul (sub (c useC) (sub (c nn) (k 1))) (c hasC)))
    (by simp [ProcPriorCodecActual.additions,isZ]))
  by_cases he:cv tr t r useC+1=cv tr t r nn
  · rw [if_pos he]
    have hv:((cv tr t r useC:Int)-((cv tr t r nn:Int)-1))=0:=by omega
    zs hq [hs]
    simp only [Int.natCast_one] at hq
    rw [hv] at hq
    simp only [Int.zero_mul,Int.sub_zero,Int.one_mul] at hq
    omega
  · rw [if_neg he]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h|h
    · exact h
    · zs hz [hs,h];omega

theorem zero_receiver (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r:Nat}
    (hr:r<tr.height t) (hs:cv tr t r rs=1) (hu:cv tr t r useC=0) :cv tr t r nzb=1 := by
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (addition_member
    (.mul (c rs) (sub (c nzb) (notE (.mul (c useC) (c ig2)))))
    (by simp [ProcPriorCodecActual.additions,isZ]))
  zs hq [hs,hu]
  have :=Codec.lt (tr:=tr) (t:=t) r nzb
  omega

theorem initial (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {f:Nat}
    (hf:f<tr.height t) (hF:cv tr t f kF=1) :
    cv tr t (f+5) srcC=0 ∧ cv tr t (f+5) useC=0 := by
  obtain ⟨hb,hh,hp⟩:=ProcPriorCodecGridHeader.header hL hf hF 4 (by decide)
  have he:=ProcPriorCodecGridHeader.end_flag hL hb hh hp
  have hn: f+4+1<tr.height t:=by have :=(ProcPriorCodecGridHeader.first_record hL hf hF).1;omega
  obtain ⟨q1,h1⟩:=Mem.zdvd hL hb (addition_member (.mul (c ehp) (n srcC)) (by simp [ProcPriorCodecActual.additions]))
  obtain ⟨q2,h2⟩:=Mem.zdvd hL hb (addition_member (.mul (c ehp) (n useC)) (by simp [ProcPriorCodecActual.additions]))
  zs h1 [he,nx hn];zs h2 [he,nx hn]
  have :=Codec.lt (tr:=tr) (t:=t) (f+5) srcC
  have :=Codec.lt (tr:=tr) (t:=t) (f+5) useC
  rw [show f+4+1=f+5 by omega] at h1 h2
  exact ⟨by omega,by omega⟩

theorem next (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r:Nat}
    (hr:r<tr.height t) (hs:cv tr t r rs=1)
    (hk:cv tr t r kidx+1<cv tr t r NN) (hN:cv tr t r NN≤4096)
    (hsb:cv tr t r srcC≤64) (hu:cv tr t r useC<cv tr t r nn) (hn:cv tr t r nn≤64) :
    cv tr t (r+24) srcC=cv tr t r srcC+(if cv tr t r useC+1=cv tr t r nn then 1 else 0) ∧
    cv tr t (r+24) useC=if cv tr t r useC+1=cv tr t r nn then 0 else cv tr t r useC+1 := by
  have hw:=wrap hL hr hs hu hn
  have hsc:=ProcPriorCodecGridCarry.record hL hr hs srcC (by simp) 23 (by decide)
  have huc:=ProcPriorCodecGridCarry.record hL hr hs useC (by simp) 23 (by decide)
  have hhc:=ProcPriorCodecGridCarry.record hL hr hs hasC (by simp) 23 (by decide)
  have hnc:=ProcPriorCodecGridStride.constant_record hL hr hs NN (by simp) 23 (by decide)
  obtain ⟨hb,hA,hg,hki,_⟩:=ProcPriorCodecGridAmount.amount_walk hL hr hs 7 (by decide)
  rw [show r+16+7=r+23 by omega] at hb hA hg hki
  have K:=kinds hL hb
  have hR:cv tr t (r+23) kR=1:=by omega
  have h7:=ProcPriorCodecSoundReceiver.e7_one hL hb hR hg
  have hl:=ProcPriorCodecGridNext.not_last hL hb hR (by omega) (by omega)
  have hnext:r+23+1<tr.height t:=by have :=(ProcPriorCodecGridStride.next_record hL hr hs hk hN).1;omega
  obtain ⟨qd,hd⟩:=Mem.zdvd hL hb (rec_member (sub (c rend) (.mul (c fA) (c e7))) (by simp [cRec]) (by decide +kernel))
  zs hd [hA,h7]
  have hrd:cv tr t (r+23) rend=1:=by have :=Codec.lt (tr:=tr) (t:=t) (r+23) rend;omega
  obtain ⟨q1,h1⟩:=Mem.zdvd hL hb (addition_member
    (mul3 (c rend) (notE (c ekl)) (sub (n srcC) (.add (c srcC) (c hasC)))) (by simp [ProcPriorCodecActual.additions]))
  obtain ⟨q2,h2⟩:=Mem.zdvd hL hb (addition_member
    (mul3 (c rend) (notE (c ekl)) (sub (n useC) (.mul (notE (c hasC)) (.add (c useC) (k 1))))) (by simp [ProcPriorCodecActual.additions]))
  zs h1 [hrd,hl,nx hnext,hsc,hhc];zs h2 [hrd,hl,nx hnext,huc,hhc]
  rw [show r+23+1=r+24 by omega] at h1 h2
  have :=Codec.lt (tr:=tr) (t:=t) (r+24) srcC
  have :=Codec.lt (tr:=tr) (t:=t) (r+24) useC
  by_cases he:cv tr t r useC+1=cv tr t r nn
  · simp only [if_pos he] at hw ⊢
    rw [hw] at h1 h2
    simp only [Int.natCast_one,Int.sub_self,Int.zero_mul,Int.sub_zero] at h1 h2
    exact ⟨by omega,by omega⟩
  · simp only [if_neg he] at hw ⊢
    rw [hw] at h1 h2
    simp only [Int.natCast_zero,Int.sub_zero,Int.one_mul,Int.add_zero] at h1 h2
    exact ⟨by omega,by omega⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecGridCounters
