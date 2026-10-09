import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundGeometry
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundOrigin
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec ProcPriorCodecSoundGeometry
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem pad_next (hL : ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat} (hr : r+1<tr.height t)
    (ha : cv tr t r act=0) : cv tr t (r+1) act=0 := by
  obtain ⟨q,hq⟩:=Mem.zdvd hL (show r<tr.height t by omega)
    (kind_member (mul3 .isTransition (notE (c act)) (n act)) (by simp [cKind]) (by decide +kernel))
  zs hq [nx hr,ha]
  simp only [zev,Mem.tenv_last_zero hr] at hq
  have := Codec.lt (tr:=tr) (t:=t) (r+1) act
  omega

theorem active_prev (hL : ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat} (hr : r+1<tr.height t)
    (ha : cv tr t (r+1) act=1) : cv tr t r act=1 := by
  have hb:cv tr t r act≤1 := (ProcPriorCodecSoundGeometry.kinds hL (by omega)).1
  by_cases hz:cv tr t r act=0
  · have := pad_next hL hr hz; omega
  · omega

theorem first_flag (hL : ProcPriorCodecSoundRows.CLocal tr t pub) (hr : 0<tr.height t)
    (ha : cv tr t 0 act=1) : cv tr t 0 kF=1 := by
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr
    (kind_member (.mul .isFirst (.mul (c act) (notE (c kF)))) (by simp [cKind]) (by decide +kernel))
  have hf:(tenv tr t 0 pub).first=1 := by simp [tenv]
  zs hq [zev_isFirst,hf,ha]
  have := (ProcPriorCodecSoundGeometry.kinds hL hr).2.2.2.2.2.1
  omega

/-- Across every active successor that is not a new first row, instance
constants are retained. This uses only the corrected table's retained rules. -/
theorem constant_next (hL : ProcPriorCodecSoundRows.CLocal tr t pub) (x : Nat) (hx : x∈[tau,pres,vid,nn,NN,base,fair]) {r : Nat} (hr : r+1<tr.height t)
    (ha : cv tr t (r+1) act=1) (hf : cv tr t (r+1) kF=0) :
    cv tr t (r+1) x=cv tr t r x := by
  have hr0:r<tr.height t := by omega
  have hp:=active_prev hL hr ha
  have hka:cv tr t r kA≤1 := (ProcPriorCodecSoundGeometry.kinds hL hr0).2.2.2.2.1
  have hes:cv tr t r esj≤1 := hL.bool hr0 (kind_member (Table.boolC esj)
    (by simp [cKind,boolCols]) (by decide +kernel))
  obtain ⟨qe,he⟩:=Mem.zdvd hL hr0
    (kind_member (mul3 (c kA) (c esj) (.mul (n act) (notE (n kF))))
      (by simp [cKind]) (by decide +kernel))
  obtain ⟨qt,ht⟩:=Mem.zdvd hL hr0
    (kind_member (.mul gT (sub (n x) (c x))) (by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [cKind]) (by
      have hc : ∀x∈[tau,pres,vid,nn,NN,base,fair],
          ProcPriorCodecActual.retiredKind.contains (.mul gT (sub (n x) (c x)))=false := by decide +kernel
      exact hc x hx))
  have h0:=Codec.lt (tr:=tr) (t:=t) r x
  have h1:=Codec.lt (tr:=tr) (t:=t) (r+1) x
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hka with hk|hk <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hes with hs|hs
  all_goals zs he [hk,hs,ha,hf,nx hr]
  all_goals zs ht [gT,hk,hs,hp,nx hr]
  all_goals omega

theorem tau_next (hL : ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat}
    (hr : r+1<tr.height t) (ha : cv tr t (r+1) act=1) (hf : cv tr t (r+1) kF=0) :
    cv tr t (r+1) tau=cv tr t r tau :=
  constant_next hL tau (by simp) hr ha hf

/-- Every active row has an earlier first row with exactly the same timestamp;
no full original Codec block extraction is assumed. -/
theorem origin (hL : ProcPriorCodecSoundRows.CLocal tr t pub) : ∀r,r<tr.height t→cv tr t r act=1→
    ∃f,f≤r ∧ cv tr t f kF=1 ∧ cv tr t f tau=cv tr t r tau := by
  intro r
  induction r with
  | zero => intro hr ha; exact ⟨0,Nat.le_refl _,first_flag hL hr ha,rfl⟩
  | succ r ih =>
    intro hr ha
    by_cases hf:cv tr t (r+1) kF=1
    · exact ⟨r+1,Nat.le_refl _,hf,rfl⟩
    · have hb:cv tr t (r+1) kF≤1 := (ProcPriorCodecSoundGeometry.kinds hL hr).2.2.2.2.2.1
      have hz:cv tr t (r+1) kF=0 := by omega
      obtain ⟨f,hf0,hF,ht⟩:=ih (by omega) (active_prev hL hr ha)
      exact ⟨f,by omega,hF,ht.trans (tau_next hL hr ha hz).symm⟩

theorem instance_origin (hL : ProcPriorCodecSoundRows.CLocal tr t pub) :
    ∀r,r<tr.height t→cv tr t r act=1→∃f,f≤r ∧ cv tr t f kF=1 ∧
      ∀x∈[tau,pres,vid,nn,NN,base,fair],cv tr t f x=cv tr t r x := by
  intro r
  induction r with
  | zero => intro hr ha; exact ⟨0,Nat.le_refl _,first_flag hL hr ha,by intro x hx; rfl⟩
  | succ r ih =>
    intro hr ha
    by_cases hf:cv tr t (r+1) kF=1
    · exact ⟨r+1,Nat.le_refl _,hf,by intro x hx; rfl⟩
    · have hb:cv tr t (r+1) kF≤1 := (ProcPriorCodecSoundGeometry.kinds hL hr).2.2.2.2.2.1
      have hz:cv tr t (r+1) kF=0 := by omega
      obtain ⟨f,hf0,hF,ht⟩:=ih (by omega) (active_prev hL hr ha)
      refine ⟨f,by omega,hF,?_⟩
      intro x hx
      exact (ht x hx).trans (constant_next hL x hx hr ha hz).symm
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundOrigin
