import ZkFormal.NearV3.Candidates.ProcPriorMemorySoundRows
import ZkFormal.NearV3.Candidates.ProcPriorIdTable
namespace ZkFormal.NearV3.Candidates.ProcPriorIdSoundRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorIdTable
abbrev At (tr : Trace Fp) (t r : Nat) (pub : List Fp) := ∀e∈constraints,e.eval tr t r pub=0
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem zdvd {r : Nat} (hL:At tr t r pub) {e : Expr} (he:e∈constraints) :
    ∃q : Int,zev (tenv tr t r pub) e=2013265921*q := by
  have h:=hL e he
  rw [eval_eq] at h
  have hd:=(Lean.Grind.IsCharP.intCast_eq_zero_iff (α:=Fp) P _).mp h
  rw [P_val] at hd
  exact ⟨zev (tenv tr t r pub) e/2013265921,by omega⟩

theorem flag {r x : Nat} (hL:At tr t r pub)
    (hx:x∈[act,isPublic,found,ProcPriorIdTable.take,eqTop,eqMid,eqLo,gTop,gMid,gAll,gPublic]) : cv tr t r x≤1 :=
  Codec.bool_of_eval (pub:=pub) (hL _ (by simp only [constraints,List.mem_append];left;left;left;left;exact List.mem_map.mpr ⟨x,hx,rfl⟩))

theorem active_prev {r : Nat} (hL:At tr t r pub) (hr:r+1<tr.height t)
    (ha:cv tr t (r+1) act=1) : cv tr t r act=1 := by
  have hb:=flag hL (x:=act) (by simp)
  obtain ⟨q,hq⟩:=zdvd hL
    (e:=.mul (.mul .isTransition (notE (c act))) (n act)) (by simp [constraints])
  simp only [zev_mul,zev_sub,notE,zev_k,zev_c,zev_n,cur_cv,Codec.nx hr,ha] at hq
  simp only [zev,Mem.tenv_last_zero hr] at hq
  omega

theorem first {r : Nat} (hL:At tr t r pub) (hr:r=0) : cv tr t r found=0 := by
  subst r
  obtain ⟨q,hq⟩:=zdvd hL (e:=.mul .isFirst (c found)) (by simp [constraints])
  simp only [zev_mul,zev_c,cur_cv,zev_isFirst] at hq
  have hf:(tenv tr t 0 pub).first=1 := by simp [tenv]
  rw [hf] at hq
  have hb:=cv_lt (tr:=tr) (t:=t) 0 found
  omega

/-- An active found row carries either an earlier index or the immediately
preceding public row's ordinal. No generated-row assumption is used. -/
theorem previous {r : Nat} (hL:At tr t r pub) (hr:r+1<tr.height t)
    (ha:cv tr t (r+1) act=1) (hf:cv tr t (r+1) found=1) :
    cv tr t r act=1 ∧
    ((cv tr t r found=1 ∧ cv tr t (r+1) index=cv tr t r index) ∨
     (cv tr t r isPublic=1 ∧ cv tr t (r+1) index=cv tr t r ordinal)) := by
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
    exact ⟨hh,by omega⟩
  · left
    have ht:cv tr t r ProcPriorIdTable.take=0 := by rw [h1] at et; omega
    have hg:cv tr t r gAll=1 := by rw [h1,ht] at ef; omega
    rw [hg,ht] at ei
    exact ⟨h1,by omega⟩
end ZkFormal.NearV3.Candidates.ProcPriorIdSoundRows
