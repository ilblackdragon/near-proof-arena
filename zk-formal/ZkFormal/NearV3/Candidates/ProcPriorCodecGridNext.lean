import ZkFormal.NearV3.Candidates.ProcPriorCodecGridAmount
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGridNext
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
open ProcPriorCodecSoundGeometry ProcPriorCodecSoundReceiver ProcPriorCodecGridAmount
variable {tr:Trace Fp} {t:Nat} {pub:List Fp}
set_option maxHeartbeats 1000000

theorem not_last (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r:Nat} (hr:r<tr.height t)
    (hR:cv tr t r kR=1) (hk:cv tr t r kidx+1<cv tr t r NN) (hN:cv tr t r NN≤4096) :
    cv tr t r ekl=0 := by
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (kind_member
    (.mul (c kR) (.mul (sub (c kidx) (sub (c NN) (k 1))) (c ekl)))
    (by simp [cKind,isZ]) (by decide +kernel))
  have hb:=hL.bool hr (kind_member (Table.boolC ekl) (by simp [cKind,boolCols]) (by decide +kernel))
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h0|h1
  · exact h0
  · zs hq [hR,h1]
    omega

theorem amount_end (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r:Nat} (hr:r<tr.height t)
    (hA:cv tr t r fA=1) (hg:cv tr t r g=7)
    (hk:cv tr t r kidx+1<cv tr t r NN) (hN:cv tr t r NN≤4096) :
    r+1<tr.height t ∧ cv tr t (r+1) fS=1 ∧ cv tr t (r+1) g=0 ∧
    cv tr t (r+1) kidx=cv tr t r kidx+1 ∧ cv tr t (r+1) rs=1 := by
  have K:=ProcPriorCodecSoundGeometry.kinds hL hr
  have hR:cv tr t r kR=1:=by omega
  have hact:cv tr t r act=1:=by omega
  have h7:=e7_one hL hr hR hg
  have hl:=not_last hL hr hR hk hN
  have hr1:=act_next hL hr hact
  obtain ⟨qd,hd⟩:=Mem.zdvd hL hr (rec_member (sub (c rend) (.mul (c fA) (c e7)))
    (by simp [cRec]) (by decide +kernel))
  zs hd [hA,h7]
  have hrd:cv tr t r rend=1:=by have hh:=Codec.lt (tr:=tr) (t:=t) r rend;omega
  obtain ⟨q1,c1⟩:=Mem.zdvd hL hr (rec_member (.mul (sub (c e7) (.mul (c rend) (c ekl))) (n g))
    (by simp [cRec]) (by decide +kernel))
  obtain ⟨q2,c2⟩:=Mem.zdvd hL hr (rec_member (mul3 (c rend) (notE (c ekl)) (notE (n fS)))
    (by simp [cRec]) (by decide +kernel))
  obtain ⟨q3,c3⟩:=Mem.zdvd hL hr (rec_member (mul3 (c rend) (notE (c ekl)) (sub (n kidx) (.add (c kidx) (k 1))))
    (by simp [cRec]) (by decide +kernel))
  obtain ⟨q4,c4⟩:=Mem.zdvd hL hr (rec_member (mul3 (c rend) (notE (c ekl)) (notE (n rs)))
    (by simp [cRec]) (by decide +kernel))
  zs c1 [nx hr1,h7,hrd,hl];zs c2 [nx hr1,hrd,hl];zs c3 [nx hr1,hrd,hl];zs c4 [nx hr1,hrd,hl]
  have ltg:=Codec.lt (tr:=tr) (t:=t) (r+1) g
  have lts:=Codec.lt (tr:=tr) (t:=t) (r+1) fS
  have ltk:=Codec.lt (tr:=tr) (t:=t) (r+1) kidx
  have ltr:=Codec.lt (tr:=tr) (t:=t) (r+1) rs
  exact ⟨hr1,by omega,by omega,by omega,by omega⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecGridNext
