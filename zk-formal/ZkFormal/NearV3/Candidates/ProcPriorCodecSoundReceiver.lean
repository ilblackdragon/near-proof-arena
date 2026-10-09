import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSdlIds
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundReceiver
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
open ProcPriorCodecSoundGeometry
abbrev LocalC := ProcPriorCodecSoundRows.CLocal
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem receiver_kind (hL : LocalC tr t pub) {r : Nat} (hr : r<tr.height t)
    (hR : cv tr t r fR=1) : cv tr t r kR=1 ∧ cv tr t r act=1 ∧
      cv tr t r kH+cv tr t r kR+cv tr t r kZ=1 := by
  have hh:=ProcPriorCodecSoundGeometry.kinds hL hr
  omega

theorem e7_one (hL : LocalC tr t pub) {r : Nat} (hr : r<tr.height t)
    (hR : cv tr t r kR=1) (hg : cv tr t r g=7) : cv tr t r e7=1 := by
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (kind_member
    (.mul (c kR) (sub (c e7) (notE (.mul (sub (c g) (k 7)) (c ig7)))))
    (by simp [cKind,isZ]) (by decide +kernel))
  zs hq [hR,hg]
  have := Codec.lt (tr:=tr) (t:=t) r e7
  omega

theorem sender_end (hL : LocalC tr t pub) {r : Nat} (hr : r<tr.height t)
    (hS : cv tr t r fS=1) (hg : cv tr t r g=7) :
    r+1<tr.height t ∧ cv tr t (r+1) fR=1 ∧ cv tr t (r+1) g=0 ∧
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
    (mul3 (c e7) (c fS) (notE (n fR))) (by simp [cRec]) (by decide +kernel))
  obtain ⟨q3,h3⟩:=Mem.zdvd hL hr (rec_member
    (mul3 (c e7) (c fS) (sub (n kidx) (c kidx))) (by simp [cRec]) (by decide +kernel))
  zs h1 [h7,hrd,nx hr1]; zs h2 [h7,hS,nx hr1]; zs h3 [h7,hS,nx hr1]
  have := Codec.lt (tr:=tr) (t:=t) (r+1) g
  have := Codec.lt (tr:=tr) (t:=t) (r+1) fR
  have := Codec.lt (tr:=tr) (t:=t) (r+1) kidx
  have := Codec.lt (tr:=tr) (t:=t) r kidx
  exact ⟨hr1,by omega,by omega,by omega⟩

theorem receiver_step (hL : LocalC tr t pub) {r x : Nat} (hr : r<tr.height t)
    (hRr : cv tr t r fR=1) (hg : cv tr t r g=x) (hx : x<7) :
    r+1<tr.height t ∧ cv tr t (r+1) fR=1 ∧ cv tr t (r+1) g=x+1 ∧
      cv tr t (r+1) kidx=cv tr t r kidx := by
  obtain ⟨hR,hA,_⟩:=receiver_kind hL hr hRr
  have h7:=e7_zero hL hr hR (by omega)
  have hr1:=act_next hL hr hA
  obtain ⟨q1,h1⟩:=Mem.zdvd hL hr (rec_member
    (mul3 (c kR) (notE (c e7)) (sub (n fR) (c fR))) (by simp [cRec]) (by decide +kernel))
  obtain ⟨q2,h2⟩:=Mem.zdvd hL hr (rec_member
    (mul3 (c kR) (notE (c e7)) (sub (n g) (.add (c g) (k 1)))) (by simp [cRec]) (by decide +kernel))
  obtain ⟨q3,h3⟩:=Mem.zdvd hL hr (rec_member
    (mul3 (c kR) (notE (c e7)) (sub (n kidx) (c kidx))) (by simp [cRec]) (by decide +kernel))
  zs h1 [hR,h7,hRr,nx hr1]; zs h2 [hR,h7,hg,nx hr1]; zs h3 [hR,h7,nx hr1]
  have := Codec.lt (tr:=tr) (t:=t) (r+1) fR
  have := Codec.lt (tr:=tr) (t:=t) (r+1) g
  have := Codec.lt (tr:=tr) (t:=t) (r+1) kidx
  have := Codec.lt (tr:=tr) (t:=t) r kidx
  exact ⟨hr1,by omega,by omega,by omega⟩

theorem receiver_walk (hL : LocalC tr t pub) {r : Nat} (hr : r<tr.height t)
    (hs : cv tr t r rs=1) : ∀i,i<8→r+8+i<tr.height t ∧
      cv tr t (r+8+i) fR=1 ∧ cv tr t (r+8+i) g=i ∧
      cv tr t (r+8+i) kidx=cv tr t r kidx ∧
      cv tr t (r+8+i) kH+cv tr t (r+8+i) kR+cv tr t (r+8+i) kZ=1 := by
  obtain ⟨hr7,hS7,hg7,_,_⟩:=sender_walk hL hr hs 7 (by decide)
  obtain ⟨hr8,hR8,hg8,hk8⟩:=sender_end hL hr7 hS7 hg7
  have hks:=ProcPriorCodecSoundSdlIds.sender_index hL hr hs 7 (by decide)
  have hrow : ∀i,i<8→r+8+i<tr.height t ∧ cv tr t (r+8+i) fR=1 ∧
      cv tr t (r+8+i) g=i ∧ cv tr t (r+8+i) kidx=cv tr t r kidx := by
    intro i
    induction i with
    | zero => intro _; simpa only [Nat.add_zero,show r+7+1=r+8 by omega] using ⟨hr8,hR8,hg8,hk8.trans hks⟩
    | succ i ih =>
      intro hi
      obtain ⟨hri,hRi,hgi,hki⟩:=ih (by omega)
      obtain ⟨hrn,hRn,hgn,hkn⟩:=receiver_step hL hri hRi hgi (by omega)
      exact ⟨by simpa [Nat.add_assoc] using hrn,by simpa [Nat.add_assoc] using hRn,
        by simpa [Nat.add_assoc] using hgn,by simpa [Nat.add_assoc] using hkn.trans hki⟩
  intro i hi
  obtain ⟨hri,hRi,hgi,hki⟩:=hrow i hi
  exact ⟨hri,hRi,hgi,hki,(receiver_kind hL hri hRi).2.2⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundReceiver
