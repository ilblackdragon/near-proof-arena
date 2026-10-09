import ZkFormal.NearV3.Render.Ups.CopyFields

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.UpsGen

theorem copy_address {I : UpsInst} {Q : UpsPartI} {st ix wi start p : Nat}
    (hkind : Q.kind<12) (hs : st<9) (hk8 : Q.kind≠8) (hc : CpB I Q st wi=true)
    (hp : p=start+ix) : sposV I Q st ix wi p=sourceFieldStart I Q st wi start+(ix : Int) := by
  rcases (show Q.kind=0 ∨ Q.kind=1 ∨ Q.kind=2 ∨ Q.kind=3 ∨ Q.kind=4 ∨ Q.kind=5 ∨ Q.kind=6 ∨ Q.kind=7 ∨ Q.kind=8 ∨ Q.kind=9 ∨ Q.kind=10 ∨ Q.kind=11 by omega)
    with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk <;>
    rcases (show st=0 ∨ st=1 ∨ st=2 ∨ st=3 ∨ st=4 ∨ st=5 ∨ st=6 ∨ st=7 ∨ st=8 by omega)
    with ht | ht | ht | ht | ht | ht | ht | ht | ht <;>
    simp [hk,ht,CpB,WfrB,VcpB] at hc hk8 <;>
    by_cases hw : wi=0 <;> by_cases hy : I.ts=1 <;>
    simp [sposV,sourceFieldStart,hk,ht,aftV,AftB,FwB,hw,hy,ind] <;> omega

end ZkFormal.NearV3.Render.UpsGen
