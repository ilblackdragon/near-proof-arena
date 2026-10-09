import ZkFormal.NearV3.Candidates.ProcPriorVerticalMemorySound
import ZkFormal.NearV3.Candidates.ProcPriorIdSoundRows
namespace ZkFormal.NearV3.Candidates.ProcPriorVerticalIdRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorVertical4Linear
abbrev LocalV := ProcPriorVerticalMemorySound.LocalV
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem component_value (hL:LocalV tr t pub) {r : Nat} (hr:r<tr.height t)
    (hs:cv tr t r (stage 1)=1) (e : Expr) (he:e∈ProcPriorIdTable.constraints) :
    (expression e).eval tr t r pub=0 := by
  have hm:.mul (c (stage 1)) (expression e)∈table.constraints := by
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨(ProcPriorIdTable.table 70 71 72 69,1),by simp [components,List.zipIdx],?_⟩
    exact List.mem_map.mpr ⟨e,he,rfl⟩
  have hh:=hL r hr _ hm
  have hc:tr.cell t r (stage 1)=(1:Fp) := by
    change tr.cell t r (stage 1)=Fp.ofNat 1
    exact (Fp.ofNat_toNat _).symm.trans (congrArg Fp.ofNat hs)
  change tr.cell t r (stage 1)*(expression e).eval tr t r pub=0 at hh
  rw [hc] at hh
  grind only

theorem first_zero (hL:LocalV tr t pub) {r : Nat} (hr:r<tr.height t)
    (hs:cv tr t r (stage 1)=1) (hf:cv tr t r ProcPriorIdTable.found=1) :
    cv tr t r first=0 := by
  have he:=component_value hL hr hs (.mul .isFirst (c ProcPriorIdTable.found)) (by simp [ProcPriorIdTable.constraints])
  change tr.cell t r first*tr.cell t r ProcPriorIdTable.found=0 at he
  have hf':tr.cell t r ProcPriorIdTable.found=1:=by rw [←Fp.ofNat_toNat (tr.cell t r _)];change Fp.ofNat (cv tr t r _)=1;rw [hf];rfl
  rw [hf'] at he
  have hz:tr.cell t r first=0:=by grind only
  unfold cv;rw [hz];rfl

theorem predecessor (hL:LocalV tr t pub) {r : Nat} (hr:r+1<tr.height t)
    (hs:cv tr t (r+1) (stage 1)=1) (hf:cv tr t (r+1) ProcPriorIdTable.found=1) :
    cv tr t r (stage 1)=1 ∧ cv tr t r last=0 := by
  have hz:=first_zero hL hr hs hf
  have hr0:r<tr.height t:=by omega
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr0 (ProcPriorVerticalMemorySound.window_member
    (.mul .isTransition (sub (n first) (c last))) (by simp [windows]))
  simp only [zev_mul,zev_sub,zev_c,zev_n,cur_cv,Codec.nx hr,hz] at hq
  simp only [zev,Mem.tenv_last_zero hr] at hq
  have hb:=cv_lt (tr:=tr) (t:=t) r last
  have hl:cv tr t r last=0:=by omega
  obtain ⟨q',hq'⟩:=Mem.zdvd hL hr0 (ProcPriorVerticalMemorySound.window_member
    (.mul (.mul .isTransition (sub (k 1) (c last))) (sub (n (stage 1)) (c (stage 1))))
    (List.mem_append_right _ (List.mem_map.mpr ⟨1,by decide,rfl⟩)))
  simp only [zev_mul,zev_sub,zev_k,zev_c,zev_n,cur_cv,Codec.nx hr,hs,hl] at hq'
  simp only [zev,Mem.tenv_last_zero hr] at hq'
  have hh:=cv_lt (tr:=tr) (t:=t) r (stage 1)
  exact ⟨by omega,hl⟩

/-- Dropping a virtual first flag is safe for the ID reset constraints; at
physical row zero the global window constraint fixes that flag to one. -/
theorem row_local (hL:LocalV tr t pub) {r : Nat} (hr:r+1<tr.height t)
    (hs:cv tr t r (stage 1)=1) (hl:cv tr t r last=0) :
    ProcPriorIdSoundRows.At tr t r pub := by
  have hlc:tr.cell t r last=(0:Fp):=by
    rw [←Fp.ofNat_toNat (tr.cell t r last)];change Fp.ofNat (cv tr t r last)=0;rw [hl];rfl
  have hn:r+1≠tr.height t:=by omega
  have first0:r=0→tr.cell t r first=1:=by
    intro hz;subst r
    have hh:=hL 0 (by omega) _ (ProcPriorVerticalMemorySound.window_member
      (.mul .isFirst (sub (c first) (k 1))) (by simp [windows]))
    change (1:Fp)*(tr.cell t 0 first + -1)=0 at hh
    grind only
  intro e he
  have hv:=component_value hL (show r<tr.height t by omega) hs e he
  simp only [ProcPriorIdTable.constraints,List.mem_append,List.mem_map,
    List.mem_cons,List.not_mem_nil,or_false,ProcPriorIdTable.eqs] at he
  rcases he with (((he|he)|he)|he)|he
  · obtain ⟨x,hx,rfl⟩:=he
    exact hv
  all_goals rcases he with rfl|he
  all_goals try (rcases he with rfl|he)
  all_goals try (rcases he with rfl|he)
  all_goals try (rcases he with rfl|he)
  all_goals try (rcases he with rfl|he)
  all_goals try (rcases he with rfl|he)
  all_goals try (rcases he with rfl|he)
  all_goals try (rcases he with rfl|he)
  all_goals try (rcases he with rfl|he)
  all_goals try (rcases he with rfl|he)
  all_goals try (rcases he with rfl|he)
  all_goals try (rcases he with rfl|he)
  all_goals try (rcases he with rfl|he)
  all_goals try subst he
  all_goals try exact hv
  all_goals simp only [expression,Expr.eval,Expr.evalWith,rowEnv,c,k,sub,hlc,hn,ite_false,
    Bool.false_eq_true,ProcPriorIdTable.notE] at hv ⊢
  all_goals by_cases hz:r=0
  all_goals try simp only [hz,ite_true,ite_false] at hv ⊢
  all_goals try rw [first0 hz] at hv
  all_goals first | exact hv | grind only
end ZkFormal.NearV3.Candidates.ProcPriorVerticalIdRows
