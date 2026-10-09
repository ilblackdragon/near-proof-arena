import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundReceiver
import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundRecordBound
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGridAmount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
open ProcPriorCodecSoundGeometry ProcPriorCodecSoundReceiver
abbrev LocalC := ProcPriorCodecSoundRows.CLocal
variable {tr:Trace Fp} {t:Nat} {pub:List Fp}
set_option maxHeartbeats 1000000

theorem amount_kind (hL:LocalC tr t pub) {r:Nat} (hr:r<tr.height t)
    (hA:cv tr t r fA=1) :cv tr t r kR=1 ∧ cv tr t r act=1 ∧ cv tr t r kH+cv tr t r kR+cv tr t r kZ=1 := by
  have hh:=ProcPriorCodecSoundGeometry.kinds hL hr
  omega
theorem receiver_end (hL : LocalC tr t pub) {r : Nat} (hr : r<tr.height t)
    (hS : cv tr t r fR=1) (hg : cv tr t r g=7) :
    r+1<tr.height t ∧ cv tr t (r+1) fA=1 ∧ cv tr t (r+1) g=0 ∧
      cv tr t (r+1) kidx=cv tr t r kidx := by
  have hh:=ProcPriorCodecSoundGeometry.kinds hL hr
  have hA:cv tr t r fA=0 := by omega
  have hR:cv tr t r kR=1 := by omega
  have hact:cv tr t r act=1 := by omega
  have h7:=e7_one hL hr hR hg
  have hr1:=act_next hL hr hact
  obtain ⟨qd,hd⟩:=Mem.zdvd hL hr (rec_member
    (sub (c rend) (.mul (c fA) (c e7))) (by simp [cRec]) (by decide +kernel))
  zs hd [hA]
  have hrd:cv tr t r rend=0 := by have := Codec.lt (tr:=tr) (t:=t) r rend; omega
  obtain ⟨q1,h1⟩:=Mem.zdvd hL hr (rec_member
    (.mul (sub (c e7) (.mul (c rend) (c ekl))) (n g)) (by simp [cRec]) (by decide +kernel))
  obtain ⟨q2,h2⟩:=Mem.zdvd hL hr (rec_member
    (mul3 (c e7) (c fR) (notE (n fA))) (by simp [cRec]) (by decide +kernel))
  obtain ⟨q3,h3⟩:=Mem.zdvd hL hr (rec_member
    (mul3 (c e7) (c fR) (sub (n kidx) (c kidx))) (by simp [cRec]) (by decide +kernel))
  zs h1 [h7,hrd,nx hr1]; zs h2 [h7,hS,nx hr1]; zs h3 [h7,hS,nx hr1]
  have := Codec.lt (tr:=tr) (t:=t) (r+1) g
  have := Codec.lt (tr:=tr) (t:=t) (r+1) fA
  have := Codec.lt (tr:=tr) (t:=t) (r+1) kidx
  have := Codec.lt (tr:=tr) (t:=t) r kidx
  exact ⟨hr1,by omega,by omega,by omega⟩

theorem amount_step (hL : LocalC tr t pub) {r x : Nat} (hr : r<tr.height t)
    (hRr : cv tr t r fA=1) (hg : cv tr t r g=x) (hx : x<7) :
    r+1<tr.height t ∧ cv tr t (r+1) fA=1 ∧ cv tr t (r+1) g=x+1 ∧
      cv tr t (r+1) kidx=cv tr t r kidx := by
  obtain ⟨hR,hA,_⟩:=amount_kind hL hr hRr
  have h7:=e7_zero hL hr hR (by omega)
  have hr1:=act_next hL hr hA
  obtain ⟨q1,h1⟩:=Mem.zdvd hL hr (rec_member
    (mul3 (c kR) (notE (c e7)) (sub (n fA) (c fA))) (by simp [cRec]) (by decide +kernel))
  obtain ⟨q2,h2⟩:=Mem.zdvd hL hr (rec_member
    (mul3 (c kR) (notE (c e7)) (sub (n g) (.add (c g) (k 1)))) (by simp [cRec]) (by decide +kernel))
  obtain ⟨q3,h3⟩:=Mem.zdvd hL hr (rec_member
    (mul3 (c kR) (notE (c e7)) (sub (n kidx) (c kidx))) (by simp [cRec]) (by decide +kernel))
  zs h1 [hR,h7,hRr,nx hr1]; zs h2 [hR,h7,hg,nx hr1]; zs h3 [hR,h7,nx hr1]
  have := Codec.lt (tr:=tr) (t:=t) (r+1) fA
  have := Codec.lt (tr:=tr) (t:=t) (r+1) g
  have := Codec.lt (tr:=tr) (t:=t) (r+1) kidx
  have := Codec.lt (tr:=tr) (t:=t) r kidx
  exact ⟨hr1,by omega,by omega,by omega⟩

theorem amount_walk (hL : LocalC tr t pub) {r : Nat} (hr : r<tr.height t)
    (hs : cv tr t r rs=1) : ∀i,i<8→r+16+i<tr.height t ∧
      cv tr t (r+16+i) fA=1 ∧ cv tr t (r+16+i) g=i ∧
      cv tr t (r+16+i) kidx=cv tr t r kidx ∧
      cv tr t (r+16+i) kH+cv tr t (r+16+i) kR+cv tr t (r+16+i) kZ=1 := by
  obtain ⟨hr15,hR15,hg15,hks,_⟩:=ProcPriorCodecSoundReceiver.receiver_walk hL hr hs 7 (by decide)
  obtain ⟨hr16,hA16,hg16,hk16⟩:=receiver_end hL hr15 hR15 hg15
  have hrow : ∀i,i<8→r+16+i<tr.height t ∧ cv tr t (r+16+i) fA=1 ∧
      cv tr t (r+16+i) g=i ∧ cv tr t (r+16+i) kidx=cv tr t r kidx := by
    intro i
    induction i with
    | zero => intro _; simpa only [Nat.add_zero,show r+8+7+1=r+16 by omega] using ⟨hr16,hA16,hg16,hk16.trans hks⟩
    | succ i ih =>
      intro hi
      obtain ⟨hri,hRi,hgi,hki⟩:=ih (by omega)
      obtain ⟨hrn,hRn,hgn,hkn⟩:=amount_step hL hri hRi hgi (by omega)
      exact ⟨by simpa [Nat.add_assoc] using hrn,by simpa [Nat.add_assoc] using hRn,
        by simpa [Nat.add_assoc] using hgn,by simpa [Nat.add_assoc] using hkn.trans hki⟩
  intro i hi
  obtain ⟨hri,hRi,hgi,hki⟩:=hrow i hi
  exact ⟨hri,hRi,hgi,hki,(amount_kind hL hri hRi).2.2⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecGridAmount
