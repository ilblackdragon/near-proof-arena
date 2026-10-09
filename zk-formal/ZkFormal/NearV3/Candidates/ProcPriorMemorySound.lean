import ZkFormal.NearV3.Candidates.ProcPriorMemoryTransport
import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundIndex
namespace ZkFormal.NearV3.Candidates.ProcPriorMemorySound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched
open ProcPriorMemoryTable
abbrev LocalM (tr : Trace Fp) (t : Nat) (pub : List Fp) := Local constraints tr t pub
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem flag (hL:LocalM tr t pub) {r x : Nat} (hr:r<tr.height t)
    (hx:x∈[act,query,hi,beforeHi,same]) : cv tr t r x≤1 :=
  hL.bool hr (List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩))

theorem active_prev (hL:LocalM tr t pub) {r : Nat} (hr:r+1<tr.height t)
    (ha:cv tr t (r+1) act=1) : cv tr t r act=1 := by
  have hb:=flag hL (show r<tr.height t by omega) (x:=act) (by simp)
  obtain ⟨q,hq⟩:=Mem.zdvd hL (show r<tr.height t by omega)
    (e:=.mul (.mul .isTransition (notE (c act))) (n act)) (by simp [constraints])
  simp only [zev_mul,zev_sub,notE,zev_k,zev_c,zev_n,cur_cv,Codec.nx hr,ha] at hq
  simp only [zev,Mem.tenv_last_zero hr] at hq
  omega

theorem query_before (hL:LocalM tr t pub) {r : Nat} (hr:r<tr.height t)
    (ha:cv tr t r act=1) (hq:cv tr t r query=1) :
    cv tr t r lo=cv tr t r beforeLo ∧ cv tr t r hi=cv tr t r beforeHi := by
  have hc (x y : Nat) (hx:(x=lo ∧ y=beforeLo) ∨ (x=hi ∧ y=beforeHi)) :
      cv tr t r x=cv tr t r y := by
    obtain ⟨q,hq'⟩:=Mem.zdvd hL hr (e:=.mul (.mul (c act) (c query)) (sub (c x) (c y))) (by
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
theorem query_origin (hL:LocalM tr t pub) {r : Nat} (hr:r<tr.height t)
    (ha:cv tr t r act=1) (hq:cv tr t r query=1) :
    (cv tr t r lo=0 ∧ cv tr t r hi=0) ∨
    ∃v,r=v+1 ∧ cv tr t v act=1 ∧ cv tr t v query=0 ∧
      addr.eval tr t v pub=addr.eval tr t r pub ∧
      cv tr t v lo=cv tr t r lo ∧ cv tr t v hi=cv tr t r hi := by
  obtain ⟨hlo,hhi⟩:=query_before hL hr ha hq
  cases r with
  | zero=>
    left
    have hz (x : Nat) (hx:x=beforeLo ∨ x=beforeHi) :cv tr t 0 x=0 := by
      obtain ⟨q,hq'⟩:=Mem.zdvd hL hr (e:=.mul .isFirst (c x)) (by rcases hx with rfl|rfl <;> simp [constraints])
      simp only [zev_mul,zev_c,cur_cv,zev_isFirst] at hq'
      have hf:(tenv tr t 0 pub).first=1 := by simp [tenv]
      rw [hf] at hq'
      have hb:=cv_lt (tr:=tr) (t:=t) 0 x
      omega
    exact ⟨by rw [hlo,hz beforeLo (by simp)],by rw [hhi,hz beforeHi (by simp)]⟩
  | succ v=>
    have hp:=active_prev hL hr ha
    have hv:v<tr.height t := by omega
    have hs:=flag hL hv (x:=same) (by simp)
    have hqbit:=flag hL hv (x:=query) (by simp)
    have carry (x y : Nat) (hx:(x=beforeLo ∧ y=lo) ∨ (x=beforeHi ∧ y=hi)) :
        cv tr t (v+1) x=cv tr t v same*cv tr t v y := by
      obtain ⟨q,hq'⟩:=Mem.zdvd hL hv
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
        obtain ⟨q,hq'⟩:=Mem.zdvd hL hv (e:=.mul adjacent (.mul (c query) (c same))) (by simp [constraints])
        simp only [adjacent,zev_mul,zev_c,zev_n,cur_cv,Codec.nx hr,hp,ha,hz] at hq'
        omega
      have he:addr.eval tr t v pub=addr.eval tr t (v+1) pub := by
        obtain ⟨q,hq'⟩:=Mem.zdvd hL hv (e:=.mul adjacent (.mul delta (c same))) (by simp [constraints])
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

theorem address_injective (a b : Nat)
    (hta:cv tr t a tau<33) (htb:cv tr t b tau<33)
    (hla:cv tr t a link<4096) (hlb:cv tr t b link<4096)
    (he:addr.eval tr t a pub=addr.eval tr t b pub) :
    cv tr t a tau=cv tr t b tau ∧ cv tr t a link=cv tr t b link := by
  have ev (r : Nat) :addr.eval tr t r pub=Fp.ofNat (4096*cv tr t r tau+cv tr t r link) :=
    Codec.ev_of (by simp only [addr,zev_add,zev_mul,zev_k,zev_c,cur_cv,Int.natCast_add,Int.natCast_mul])
  rw [ev a,ev b] at he
  have hp:135168<P := by decide +kernel
  have hn:=ProcPriorCodecSoundPublicId.nat_eq _ _ (by omega) (by omega) he
  omega
end ZkFormal.NearV3.Candidates.ProcPriorMemorySound
