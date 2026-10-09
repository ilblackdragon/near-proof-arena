import ZkFormal.NearV3.Candidates.ProcPriorVertical4Eval
import ZkFormal.NearV3.Candidates.ProcPriorMemorySoundRows
namespace ZkFormal.NearV3.Candidates.ProcPriorVerticalMemorySound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorVertical4Linear
abbrev LocalV (tr : Trace Fp) (t : Nat) (pub : List Fp) := Local table.constraints tr t pub
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem window_member (e : Expr) (he:e∈windows) :e∈table.constraints := List.mem_append_left _ he

theorem component_value (hL:LocalV tr t pub) {r : Nat} (hr:r<tr.height t)
    (hs:cv tr t r (stage 0)=1) (e : Expr) (he:e∈ProcPriorMemoryTable.constraints) :
    (expression e).eval tr t r pub=0 := by
  have hm:.mul (c (stage 0)) (expression e)∈table.constraints := by
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨(ProcPriorMemoryGated.table 67 68 69,0),by simp [components,List.zipIdx],?_⟩
    exact List.mem_map.mpr ⟨e,List.mem_append_left _ he,rfl⟩
  have hh:=hL r hr _ hm
  have hc:tr.cell t r (stage 0)=(1:Fp) := by
    change tr.cell t r (stage 0)=Fp.ofNat 1
    rw [←hs];exact (Fp.ofNat_toNat _).symm
  change tr.cell t r (stage 0)*(expression e).eval tr t r pub=0 at hh
  rw [hc] at hh
  grind only

theorem stage_prev (hL:LocalV tr t pub) {r : Nat} (hr:r+1<tr.height t)
    (hs:cv tr t (r+1) (stage 0)=1) :cv tr t r (stage 0)=1 ∧ cv tr t r last=0 := by
  have hr0:r<tr.height t := by omega
  have bl:=hL.bool hr0 (window_member (Table.boolC last) (by simp [windows]))
  obtain ⟨ql,hl⟩:=Mem.zdvd hL hr0 (window_member
    (.mul (.mul .isTransition (c last)) (n (stage 0))) (by simp [windows]))
  simp only [zev_mul,zev_c,zev_n,cur_cv,Codec.nx hr,hs] at hl
  simp only [zev,Mem.tenv_last_zero hr] at hl
  have hlast:cv tr t r last=0 := by omega
  obtain ⟨qs,hs'⟩:=Mem.zdvd hL hr0 (window_member
    (.mul (.mul .isTransition (sub (k 1) (c last))) (sub (n (stage 0)) (c (stage 0)))) (List.mem_append_right _ (List.mem_map.mpr ⟨0,by decide,rfl⟩)))
  simp only [zev_mul,zev_sub,zev_k,zev_c,zev_n,cur_cv,Codec.nx hr,hs,hlast] at hs'
  simp only [zev,Mem.tenv_last_zero hr] at hs'
  have hb:=hL.bool hr0 (window_member (Table.boolC (stage 0)) (by simp [windows]))
  exact ⟨by omega,hlast⟩

theorem first_value (hL:LocalV tr t pub) {r : Nat} (hr:r<tr.height t)
    (hs:cv tr t r (stage 0)=1) :cv tr t r first=if r=0 then 1 else 0 := by
  cases r with
  | zero=>
    obtain ⟨q,hq⟩:=Mem.zdvd hL hr (window_member
      (.mul .isFirst (sub (c first) (k 1))) (by simp [windows]))
    simp only [zev_mul,zev_sub,zev_c,zev_k,cur_cv,zev_isFirst] at hq
    have hf:(tenv tr t 0 pub).first=1 := by simp [tenv]
    rw [hf] at hq
    have hb:=hL.bool hr (window_member (Table.boolC first) (by simp [windows]))
    simp only [ite_true]
    omega
  | succ r=>
    have hp:=stage_prev hL hr hs
    obtain ⟨q,hq⟩:=Mem.zdvd hL (show r<tr.height t by omega) (window_member
      (.mul .isTransition (sub (n first) (c last))) (by simp [windows]))
    simp only [zev_mul,zev_sub,zev_c,zev_n,cur_cv,Codec.nx hr,hp.2] at hq
    simp only [zev,Mem.tenv_last_zero hr] at hq
    have hb:=hL.bool hr (window_member (Table.boolC first) (by simp [windows]))
    simp only [Nat.add_one_ne_zero,ite_false]
    omega

theorem active_not_last (hL:LocalV tr t pub) {r : Nat} (hr:r<tr.height t)
    (hs:cv tr t r (stage 0)=1) (ha:cv tr t r ProcPriorMemoryTable.act=1) :
    cv tr t r last=0 ∧ r+1<tr.height t := by
  have he:=component_value hL hr hs (.mul .isLast (c ProcPriorMemoryTable.act)) (by simp [ProcPriorMemoryTable.constraints])
  have hx:.mul (c last) (c ProcPriorMemoryTable.act)=expression (.mul .isLast (c ProcPriorMemoryTable.act)) := rfl
  rw [←hx,ZkFormal.Near.eval_mul,Codec.ev_c,Codec.ev_c,ha] at he
  have hz:cv tr t r last=0 := by
    have he':Fp.ofNat (cv tr t r last)=0 := by change Fp.ofNat (cv tr t r last)*(1:Fp)=0 at he;grind only
    exact ProcPriorCodecSoundPublicId.nat_eq _ 0 (cv_lt r last) (by decide) he'
  refine ⟨hz,?_⟩
  apply Classical.byContradiction
  intro hh
  have heq:r+1=tr.height t := by omega
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (window_member (.mul .isLast (sub (c last) (k 1))) (by simp [windows]))
  simp only [zev_mul,zev_sub,zev_c,zev_k,cur_cv,hz] at hq
  have hl:(tenv tr t r pub).last=1 := by simp [tenv,heq]
  change (tenv tr t r pub).last*(↑(0:Nat)-↑(1:Nat))=2013265921*q at hq
  rw [hl] at hq
  omega

theorem row_local (hL:LocalV tr t pub) {r : Nat} (hr:r+1<tr.height t)
    (hs:cv tr t r (stage 0)=1) (hl:cv tr t r last=0) :
    ProcPriorMemorySoundRows.At tr t r pub := by
  have hf:=first_value hL (show r<tr.height t by omega) hs
  have hfc:tr.cell t r first=(if r=0 then (1:Fp) else 0) := by
    rw [←Fp.ofNat_toNat (tr.cell t r first)]
    change Fp.ofNat (cv tr t r first)=_
    rw [hf]
    split <;> rfl
  have hlc:tr.cell t r last=(0:Fp) := by
    rw [←Fp.ofNat_toNat (tr.cell t r last)]
    change Fp.ofNat (cv tr t r last)=_
    rw [hl];rfl
  have hw:windowEnv (rowEnv tr t r pub)=rowEnv tr t r pub := by
    have hn:r+1≠tr.height t := by omega
    simp only [windowEnv,rowEnv,Bool.false_eq_true,ite_false,hfc,hlc,hn]
    congr 1
  intro e he
  have hv:=component_value hL (show r<tr.height t by omega) hs e he
  change (expression e).evalWith (rowEnv tr t r pub)=0 at hv
  rw [expression_eval,hw] at hv
  exact hv

theorem query_origin (hL:LocalV tr t pub) {r : Nat} (hr:r<tr.height t)
    (hs:cv tr t r (stage 0)=1) (ha:cv tr t r ProcPriorMemoryTable.act=1)
    (hq:cv tr t r ProcPriorMemoryTable.query=1) :
    (cv tr t r ProcPriorMemoryTable.lo=0 ∧ cv tr t r ProcPriorMemoryTable.hi=0) ∨
    ∃v,r=v+1 ∧ cv tr t v ProcPriorMemoryTable.act=1 ∧ cv tr t v ProcPriorMemoryTable.query=0 ∧
      ProcPriorMemoryTable.addr.eval tr t v pub=ProcPriorMemoryTable.addr.eval tr t r pub ∧
      cv tr t v ProcPriorMemoryTable.lo=cv tr t r ProcPriorMemoryTable.lo ∧
      cv tr t v ProcPriorMemoryTable.hi=cv tr t r ProcPriorMemoryTable.hi := by
  obtain ⟨hl,hr1⟩:=active_not_last hL hr hs ha
  apply ProcPriorMemorySoundRows.query_origin (row_local hL hr1 hs hl) ?_ hr ha hq
  intro v he
  subst r
  obtain ⟨hsv,hlv⟩:=stage_prev hL hr hs
  exact row_local hL hr hsv hlv
end ZkFormal.NearV3.Candidates.ProcPriorVerticalMemorySound
