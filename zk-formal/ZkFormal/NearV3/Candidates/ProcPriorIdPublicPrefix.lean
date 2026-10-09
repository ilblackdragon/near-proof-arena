import ZkFormal.NearV3.Candidates.ProcPriorIdSameKey
namespace ZkFormal.NearV3.Candidates.ProcPriorIdPublicPrefix
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorIdTable ProcPriorIdSoundRows

theorem previous {tr:Trace Fp} {t r:Nat} {pub:List Fp}
    (hL:At tr t r pub) (hr:r+1<tr.height t)
    (hg:cv tr t r gAll=1) (hp:cv tr t (r+1) isPublic=1) :cv tr t r isPublic=1 := by
  obtain ⟨q,hq⟩:=zdvd hL
    (e:=.mul (.mul (c gAll) (notE (c isPublic))) (n isPublic)) (by simp [constraints])
  simp only [notE,zev_mul,zev_sub,zev_k,zev_c,zev_n,cur_cv,Codec.nx hr,hg,hp] at hq
  have hh:=flag hL (x:=isPublic) (by simp)
  omega
end ZkFormal.NearV3.Candidates.ProcPriorIdPublicPrefix
