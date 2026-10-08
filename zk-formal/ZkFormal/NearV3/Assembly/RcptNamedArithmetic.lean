import ZkFormal.NearV3.Assembly.RcptNamedInverseComposition

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
open ZkFormal.Near.Render ZkFormal.Near.Render.RcptGen ZkFormal.Near.Render.RcptP

theorem named_score_end (r : Receipt) (i : Nat) (hi : i+1=r.receiverId.length) :
    let d := characterData r
    Fp.ofNat (pV1 d)=(Fp.ofNat r.receiverId.length-64)^2+
      (Fp.ofNat (accV d i)-Fp.ofNat r.receiverId.length)^2 ∧
    Fp.ofNat (pV2 d)=(Fp.ofNat r.receiverId.length-42)^2+
      (Fp.ofNat (d.recv.getD 0 0)-48)^2+(Fp.ofNat (d.recv.getD 1 0)-120)^2+
      (Fp.ofNat (accV d i)-Fp.ofNat (h01V d)-40)^2 ∧
    Fp.ofNat (pV3 d)=(Fp.ofNat r.receiverId.length-42)^2+
      (Fp.ofNat (d.recv.getD 0 0)-48)^2+(Fp.ofNat (d.recv.getD 1 0)-115)^2+
      (Fp.ofNat (accV d i)-Fp.ofNat (h01V d)-40)^2 := by
  dsimp only
  have he : (characterData r).recv.length=r.receiverId.length := by simp [characterData,toNats]
  have hj : r.receiverId.length-1=i := by omega
  simp only [pV1,pV2,pV3,ofNat_mod,ofNat_add_e,ofNat_sqd,he,hj]
  simp only [show Fp.ofNat 64=(64:Fp) by rfl,show Fp.ofNat 42=(42:Fp) by rfl,show Fp.ofNat 48=(48:Fp) by rfl,show Fp.ofNat 120=(120:Fp) by rfl,show Fp.ofNat 115=(115:Fp) by rfl,show Fp.ofNat 40=(40:Fp) by rfl]
  constructor
  · grind only
  · constructor <;> grind only

theorem named_score_start (r : Receipt) :
    Fp.ofNat (accV (characterData r) 0)=Fp.ofNat (b2n (isHexC ((characterData r).recv.getD 0 0))) := by
  rw [accV_zero]

theorem named_score_step (r : Receipt) (i : Nat) :
    Fp.ofNat (accV (characterData r) (i+1))=Fp.ofNat (accV (characterData r) i)+
      Fp.ofNat (b2n (isHexC ((characterData r).recv.getD (i+1) 0))) := by
  rw [accV_succ,ofNat_add_e]

end ZkFormal.NearV3.Assembly.RcptSkeleton
