import ZkFormal.NearV3.Candidates.ProcPriorOverlayCuts
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayGeometry
open ZkFormal.Air ZkFormal.Algebra
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorOverlayCuts ProcPriorVertical4Clock

def start (bs : List NativeBlock) (i : Nat) : Nat :=
  if i=0 then 0 else if i=1 then cutMemory bs else if i=2 then cutIds bs else cutRaw bs
def stop (bs : List NativeBlock) (i : Nat) : Nat :=
  if i=0 then cutMemory bs else if i=1 then cutIds bs else if i=2 then cutRaw bs else 2^22

theorem position (bs : List NativeBlock) (hc:0<cutMemory bs ∧ cutMemory bs<cutIds bs ∧
      cutIds bs<cutRaw bs ∧ cutRaw bs<2^22)
    (component : Nat→Nat→Nat→Fp) (r : Nat) (hr:r<2^22) :
    let i:=stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r
    start bs i≤r ∧ r<stop bs i ∧ stop bs i≤2^22 ∧
    data bs component r=component i (r-start bs i) ∧
    firstAt (cutMemory bs) (cutIds bs) (cutRaw bs) r=decide (r-start bs i=0) ∧
    lastAt (cutMemory bs) (cutIds bs) (cutRaw bs) (2^22) r=decide (r-start bs i+1=stop bs i-start bs i) ∧
    (r+1<stop bs i→data bs component ((r+1)%2^22)=component i (r-start bs i+1)) := by
  dsimp only
  by_cases hm:r<cutMemory bs
  · have hs:stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r=0:=by simp [stageAt,hm]
    rw [hs]
    simp only [start,stop,show ¬(1:Nat)=0 by decide,show ¬(2:Nat)=0 by decide,
      show ¬(2:Nat)=1 by decide,show ¬(3:Nat)=0 by decide,show ¬(3:Nat)=1 by decide,
      show ¬(3:Nat)=2 by decide,ite_false,ite_true,Nat.sub_zero]
    refine ⟨by omega,hm,by omega,?_,?_,?_,?_⟩
    · simp [data,hm]
    · simp only [firstAt,decide_eq_decide];omega
    · simp only [lastAt,decide_eq_decide];omega
    · intro hn
      rw [Nat.mod_eq_of_lt (by omega),data,ite_eq_left hn]
  · by_cases hi:r<cutIds bs
    · have hs:stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r=1:=by simp [stageAt,hm,hi]
      rw [hs]
      simp only [start,stop,show ¬(1:Nat)=0 by decide,show ¬(2:Nat)=0 by decide,
        show ¬(2:Nat)=1 by decide,show ¬(3:Nat)=0 by decide,show ¬(3:Nat)=1 by decide,
        show ¬(3:Nat)=2 by decide,ite_false,ite_true,Nat.sub_zero]
      refine ⟨by omega,hi,by omega,?_,?_,?_,?_⟩
      · simp [data,hm,hi]
      · simp only [firstAt,decide_eq_decide];omega
      · simp only [lastAt,decide_eq_decide];omega
      · intro hn
        rw [Nat.mod_eq_of_lt (by omega),data,ite_eq_right (by omega),ite_eq_left hn]
        congr 1;omega
    · by_cases hw:r<cutRaw bs
      · have hs:stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r=2:=by simp [stageAt,hm,hi,hw]
        rw [hs]
        simp only [start,stop,show ¬(1:Nat)=0 by decide,show ¬(2:Nat)=0 by decide,
          show ¬(2:Nat)=1 by decide,show ¬(3:Nat)=0 by decide,show ¬(3:Nat)=1 by decide,
          show ¬(3:Nat)=2 by decide,ite_false,ite_true,Nat.sub_zero]
        refine ⟨by omega,hw,by omega,?_,?_,?_,?_⟩
        · simp [data,hm,hi,hw]
        · simp only [firstAt,decide_eq_decide];omega
        · simp only [lastAt,decide_eq_decide];omega
        · intro hn
          rw [Nat.mod_eq_of_lt (by omega),data,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left hn]
          congr 1;omega
      · have hs:stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r=3:=by simp [stageAt,hm,hi,hw]
        rw [hs]
        simp only [start,stop,show ¬(1:Nat)=0 by decide,show ¬(2:Nat)=0 by decide,
          show ¬(2:Nat)=1 by decide,show ¬(3:Nat)=0 by decide,show ¬(3:Nat)=1 by decide,
          show ¬(3:Nat)=2 by decide,ite_false,ite_true,Nat.sub_zero]
        refine ⟨by omega,hr,by omega,?_,?_,?_,?_⟩
        · simp [data,hm,hi,hw]
        · simp only [firstAt,decide_eq_decide];omega
        · simp only [lastAt,decide_eq_decide];omega
        · intro hn
          rw [Nat.mod_eq_of_lt hn,data,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega)]
          congr 1;omega
end ZkFormal.NearV3.Candidates.ProcPriorOverlayGeometry
