import ZkFormal.NearV3.Candidates.ProcPriorIdKeyCarry
namespace ZkFormal.NearV3.Candidates.ProcPriorIdFirstCarry
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorIdTable ProcPriorIdSoundRows
variable {tr:Trace Fp} {t:Nat} {pub:List Fp}
theorem previous {r : Nat} (hL:At tr t r pub) (hr:r+1<tr.height t)
    (ha:cv tr t (r+1) act=1) (hf:cv tr t (r+1) found=1) :
    cv tr t r act=1 ∧
    ((cv tr t r found=1 ∧ cv tr t (r+1) index=cv tr t r index) ∨
     (cv tr t r isPublic=1 ∧ cv tr t r found=0 ∧ cv tr t (r+1) index=cv tr t r ordinal)) := by
  have hp:=active_prev hL hr ha
  have hfb:=flag hL (x:=found) (by simp)
  have hpb:=flag hL (x:=isPublic) (by simp)
  have htb:=flag hL (x:=ProcPriorIdTable.take) (by simp)
  have hgb:=flag hL (x:=gAll) (by simp)
  obtain ⟨qf,ef⟩:=zdvd hL (e:=.mul adjacent
    (sub (n found) (.mul (c gAll) (.add (c found) (c ProcPriorIdTable.take))))) (by simp [constraints])
  obtain ⟨qt,et⟩:=zdvd hL (e:=.mul (c act)
    (sub (c ProcPriorIdTable.take) (.mul (c isPublic) (notE (c found))))) (by simp [constraints])
  obtain ⟨qi,ei⟩:=zdvd hL (e:=.mul adjacent
    (sub (n index) (.mul (c gAll) (.add (c index) (.mul (c ProcPriorIdTable.take) (c ordinal)))))) (by simp [constraints])
  obtain ⟨qz,ez⟩:=zdvd hL (e:=.mul (notE (c found)) (c index)) (by simp [constraints])
  simp only [adjacent,notE,zev_mul,zev_sub,zev_add,zev_c,zev_n,zev_k,
    cur_cv,Codec.nx hr,hp,ha,hf] at ef et ei ez
  have hix:=cv_lt (tr:=tr) (t:=t) r index
  have hnx:=cv_lt (tr:=tr) (t:=t) (r+1) index
  have ho:=cv_lt (tr:=tr) (t:=t) r ordinal
  refine ⟨hp,?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hfb with h0|h1
  · right
    have ht:cv tr t r ProcPriorIdTable.take=1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp htb with hh|hh
      · rw [h0,hh] at ef; omega
      · exact hh
    have hg:cv tr t r gAll=1 := by rw [h0,ht] at ef; omega
    have hh:cv tr t r isPublic=1 := by rw [h0,ht] at et; omega
    have hz:cv tr t r index=0 := by rw [h0] at ez; omega
    rw [hg,ht,hz] at ei
    exact ⟨hh,h0,by omega⟩
  · left
    have ht:cv tr t r ProcPriorIdTable.take=0 := by rw [h1] at et; omega
    have hg:cv tr t r gAll=1 := by rw [h1,ht] at ef; omega
    rw [hg,ht] at ei
    exact ⟨h1,by omega⟩
end ZkFormal.NearV3.Candidates.ProcPriorIdFirstCarry
