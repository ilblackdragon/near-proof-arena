import ZkFormal.NearV3.Candidates.ProcPriorMemorySound
namespace ZkFormal.NearV3.Candidates.ProcPriorMemorySoundRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched
open ProcPriorMemoryTable
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
    (hx:x∈[act,query,hi,beforeHi,same]) : cv tr t r x≤1 :=
  Codec.bool_of_eval (pub:=pub) (hL _ (List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩)))

theorem active_prev {r : Nat} (hL:At tr t r pub) (hr:r+1<tr.height t)
    (ha:cv tr t (r+1) act=1) : cv tr t r act=1 := by
  have hb:=flag hL (x:=act) (by simp)
  obtain ⟨q,hq⟩:=zdvd hL
    (e:=.mul (.mul .isTransition (notE (c act))) (n act)) (by simp [constraints])
  simp only [zev_mul,zev_sub,notE,zev_k,zev_c,zev_n,cur_cv,Codec.nx hr,ha] at hq
  simp only [zev,Mem.tenv_last_zero hr] at hq
  omega

theorem query_before {r : Nat} (hL:At tr t r pub)
    (ha:cv tr t r act=1) (hq:cv tr t r query=1) :
    cv tr t r lo=cv tr t r beforeLo ∧ cv tr t r hi=cv tr t r beforeHi := by
  have hc (x y : Nat) (hx:(x=lo ∧ y=beforeLo) ∨ (x=hi ∧ y=beforeHi)) :
      cv tr t r x=cv tr t r y := by
    obtain ⟨q,hq'⟩:=zdvd hL (e:=.mul (.mul (c act) (c query)) (sub (c x) (c y))) (by
      rcases hx with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [constraints])
    simp only [zev_mul,zev_sub,zev_c,cur_cv,ha,hq] at hq'
    have :=cv_lt (tr:=tr) (t:=t) r x
    have :=cv_lt (tr:=tr) (t:=t) r y
    omega
  exact ⟨hc lo beforeLo (by simp),hc hi beforeHi (by simp)⟩

/-- Arbitrary memory queries read zero at group entry, or the immediately
preceding actual write. Address equality is a field equality; unpacking it
requires authenticated timestamp/link ranges, and global last-write semantics
additionally requires the comparison bus to order every group and stamp. -/
theorem query_origin {r : Nat} (hL:At tr t r pub) (hprev:∀v,r=v+1→At tr t v pub) (hr:r<tr.height t)
    (ha:cv tr t r act=1) (hq:cv tr t r query=1) :
    (cv tr t r lo=0 ∧ cv tr t r hi=0) ∨
    ∃v,r=v+1 ∧ cv tr t v act=1 ∧ cv tr t v query=0 ∧
      addr.eval tr t v pub=addr.eval tr t r pub ∧
      cv tr t v lo=cv tr t r lo ∧ cv tr t v hi=cv tr t r hi := by
  obtain ⟨hlo,hhi⟩:=query_before hL ha hq
  cases r with
  | zero=>
    left
    have hz (x : Nat) (hx:x=beforeLo ∨ x=beforeHi) :cv tr t 0 x=0 := by
      obtain ⟨q,hq'⟩:=zdvd hL (e:=.mul .isFirst (c x)) (by rcases hx with rfl|rfl <;> simp [constraints])
      simp only [zev_mul,zev_c,cur_cv,zev_isFirst] at hq'
      have hf:(tenv tr t 0 pub).first=1 := by simp [tenv]
      rw [hf] at hq'
      have hb:=cv_lt (tr:=tr) (t:=t) 0 x
      omega
    exact ⟨by rw [hlo,hz beforeLo (by simp)],by rw [hhi,hz beforeHi (by simp)]⟩
  | succ v=>
    have hprev:=hprev v rfl
    have hp:=active_prev hprev hr ha
    have hv:v<tr.height t := by omega
    have hs:=flag hprev (x:=same) (by simp)
    have hqbit:=flag hprev (x:=query) (by simp)
    have carry (x y : Nat) (hx:(x=beforeLo ∧ y=lo) ∨ (x=beforeHi ∧ y=hi)) :
        cv tr t (v+1) x=cv tr t v same*cv tr t v y := by
      obtain ⟨q,hq'⟩:=zdvd hprev
        (e:=.mul adjacent (sub (n x) (.mul (c same) (c y)))) (by
          rcases hx with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [constraints])
      simp only [adjacent,zev_mul,zev_sub,zev_c,zev_n,cur_cv,Codec.nx hr,hp,ha] at hq'
      have hxlt:=cv_lt (tr:=tr) (t:=t) (v+1) x
      have hylt:=cv_lt (tr:=tr) (t:=t) v y
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with hz|hz <;> rw [hz] at hq' ⊢ <;> omega
    have cl:=carry beforeLo lo (by simp)
    have ch:=carry beforeHi hi (by simp)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with hz|hz
    · left;rw [hz] at cl ch;omega
    · right
      have hquery:cv tr t v query=0 := by
        obtain ⟨q,hq'⟩:=zdvd hprev (e:=.mul adjacent (.mul (c query) (c same))) (by simp [constraints])
        simp only [adjacent,zev_mul,zev_c,zev_n,cur_cv,Codec.nx hr,hp,ha,hz] at hq'
        omega
      have he:addr.eval tr t v pub=addr.eval tr t (v+1) pub := by
        obtain ⟨q,hq'⟩:=zdvd hprev (e:=.mul adjacent (.mul delta (c same))) (by simp [constraints])
        have hd:zev (tenv tr t v pub) (sub nextAddr addr)=2013265921*q := by
          simpa only [adjacent,delta,zev_mul,zev_c,zev_n,cur_cv,Codec.nx hr,hp,ha,hz,
            Int.natCast_one,Int.one_mul,Int.mul_one] using hq'
        have hzero:(sub nextAddr addr).eval tr t v pub=0 := by
          rw [eval_eq]
          apply (Lean.Grind.IsCharP.intCast_eq_zero_iff (α:=Fp) P _).mpr
          rw [P_val]
          omega
        have hn:nextAddr.eval tr t v pub=addr.eval tr t (v+1) pub := by
          have hn:nextAddr.eval tr t v pub=Fp.ofNat (4096*cv tr t (v+1) tau+cv tr t (v+1) link) :=
            Codec.ev_of (by simp only [nextAddr,zev_add,zev_mul,zev_k,zev_n,Codec.nx hr,Int.natCast_add,Int.natCast_mul])
          have hc:addr.eval tr t (v+1) pub=Fp.ofNat (4096*cv tr t (v+1) tau+cv tr t (v+1) link) :=
            Codec.ev_of (by simp only [addr,zev_add,zev_mul,zev_k,zev_c,cur_cv,Int.natCast_add,Int.natCast_mul])
          exact hn.trans hc.symm
        change nextAddr.eval tr t v pub + -(addr.eval tr t v pub)=0 at hzero
        rw [hn] at hzero
        grind only
      refine ⟨v,rfl,hp,hquery,he,?_,?_⟩ <;> rw [hz] at cl ch <;> omega

end ZkFormal.NearV3.Candidates.ProcPriorMemorySoundRows
