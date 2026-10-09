import ZkFormal.NearV3.Candidates.ProcPriorMemoryLastWrite
namespace ZkFormal.NearV3.Candidates.ProcPriorMemoryPredicate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}
variable (live : Nat→Prop)
variable (hact:∀r,live r→cv tr t r act=1)
variable (hprefix:∀s,s<tr.height t→live s→∀r,r≤s→live r)
variable (hL:∀r,r<tr.height t→live r→ProcPriorMemorySoundRows.At tr t r pub)

include hact hprefix hL

theorem no_later_same
    (ho:∀s,s<tr.height t→live s→∀r,r≤s→address tr t r≤address tr t s)
    {q s : Nat} (hq:q<tr.height t) (hqa:live q) (hqq:cv tr t q query=1)
    (hs:s<tr.height t) (hsa:live s) (hqs:q<s) :address tr t q≠address tr t s := by
  intro he
  have hqa1:live (q+1) := hprefix s hs hsa (q+1) (by omega)
  have hq1:q+1<tr.height t := by omega
  have hab:=ho (q+1) hq1 hqa1 q (by omega)
  have hbc:=ho s hs hsa (q+1) (by omega)
  have he':address tr t q=address tr t (q+1) := by omega
  exact ProcPriorMemoryLastWrite.query_stop (hL q hq hqa) hq1 (hact q hqa) (hact _ hqa1) hqq he'

theorem write_before_query
    (ho:∀s,s<tr.height t→live s→∀r,r≤s→address tr t r≤address tr t s)
    {q w : Nat} (hq:q<tr.height t) (hqa:live q) (hqq:cv tr t q query=1)
    (hw:w<tr.height t) (hwa:live w) (hwq:cv tr t w query=0)
    (he:address tr t w=address tr t q) :w<q := by
  by_cases h:w<q
  · exact h
  · by_cases hqw:q=w
    · subst w;omega
    · exact (no_later_same live hact hprefix hL ho hq hqa hqq hw hwa (by omega) he.symm).elim

theorem query_with_write
    (ho:∀s,s<tr.height t→live s→∀r,r≤s→address tr t r≤address tr t s)
    {q w : Nat} (hq:q<tr.height t) (hqa:live q) (hqq:cv tr t q query=1)
    (hw:w<tr.height t) (hwa:live w) (hwq:cv tr t w query=0)
    (he:address tr t w=address tr t q) :
    ∃v,q=v+1 ∧ live v ∧ cv tr t v query=0 ∧
      address tr t v=address tr t q ∧ cv tr t v lo=cv tr t q lo ∧ cv tr t v hi=cv tr t q hi ∧
      ∀u,u<tr.height t→live u→cv tr t u query=0→address tr t u=address tr t q→u≤v := by
  have hwq':w<q:=write_before_query live hact hprefix hL ho hq hqa hqq hw hwa hwq he
  obtain ⟨v,hqv⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : q≠0)
  subst q
  simp only [Nat.succ_eq_add_one] at *
  have hv:v<tr.height t := by omega
  have hva:=hprefix (v+1) hq hqa v (by omega)
  have hleft:=ho v hv hva w (by omega)
  have hright:=ho (v+1) hq hqa v (by omega)
  have had:address tr t v=address tr t (v+1) := by omega
  have hav:=hact v hva
  have haq:=hact _ hqa
  have hlv:=hL v hv hva
  have hsame:=ProcPriorMemoryLastWrite.same_of_address hlv hq hav haq had
  have hvq:cv tr t v query=0 := by
    have hb:=ProcPriorMemorySoundRows.flag hlv (x:=query) (by simp)
    obtain ⟨z,hz⟩:=ProcPriorMemorySoundRows.zdvd hlv (e:=.mul adjacent (.mul (c query) (c same))) (by simp [constraints])
    simp only [adjacent,zev_mul,zev_c,zev_n,cur_cv,Codec.nx hq,hav,haq,hsame] at hz
    omega
  have carry (x y : Nat) (hx:(x=beforeLo ∧ y=lo) ∨ (x=beforeHi ∧ y=hi)) :cv tr t (v+1) x=cv tr t v y := by
    obtain ⟨z,hz⟩:=ProcPriorMemorySoundRows.zdvd hlv (e:=.mul adjacent (sub (n x) (.mul (c same) (c y)))) (by
      rcases hx with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [constraints])
    simp only [adjacent,zev_mul,zev_sub,zev_c,zev_n,cur_cv,Codec.nx hq,hav,haq,hsame] at hz
    have hb0:=cv_lt (tr:=tr) (t:=t) (v+1) x
    have hb1:=cv_lt (tr:=tr) (t:=t) v y
    omega
  have hc:=ProcPriorMemorySoundRows.query_before (hL _ hq hqa) haq hqq
  refine ⟨v,rfl,hva,hvq,had,?_,?_,?_⟩
  · exact (hc.1.trans (carry beforeLo lo (by simp))).symm
  · exact (hc.2.trans (carry beforeHi hi (by simp))).symm
  · intro u hu hua huq hue
    have :=write_before_query live hact hprefix hL ho hq hqa hqq hu hua huq hue
    omega

theorem query_without_write
    (hb:∀r,r<tr.height t→live r→address tr t r<P)
    {q : Nat} (hq:q<tr.height t) (ha:live q) (hqq:cv tr t q query=1)
    (hn:∀w,w<tr.height t→live w→cv tr t w query=0→address tr t w≠address tr t q) :
    cv tr t q lo=0 ∧ cv tr t q hi=0 := by
  have hp:∀v,q=v+1→ProcPriorMemorySoundRows.At tr t v pub := by
    intro v he
    exact hL v (by omega) (hprefix q hq ha v (by omega))
  rcases ProcPriorMemorySoundRows.query_origin (hL q hq ha) hp hq (hact q ha) hqq with hz|⟨v,hv,hva,hvq,he,_,_⟩
  · exact hz
  · have hlive:=hprefix q hq ha v (by omega)
    have ev (r : Nat):addr.eval tr t r pub=Fp.ofNat (address tr t r) :=
      Codec.ev_of (by simp only [address,addr,zev_add,zev_mul,zev_k,zev_c,cur_cv,Int.natCast_add,Int.natCast_mul])
    rw [ev v,ev q] at he
    have had:=ProcPriorCodecSoundPublicId.nat_eq _ _ (hb v (by omega) hlive) (hb q hq ha) he
    exact (hn v (by omega) hlive hvq had).elim

theorem query_last_write
    (ho:∀s,s<tr.height t→live s→∀r,r≤s→address tr t r≤address tr t s)
    (hb:∀r,r<tr.height t→live r→address tr t r<P)
    {q : Nat} (hq:q<tr.height t) (hqa:live q) (hqq:cv tr t q query=1) :
    ((cv tr t q lo=0 ∧ cv tr t q hi=0) ∧
      ∀w,w<tr.height t→live w→cv tr t w query=0→address tr t w≠address tr t q) ∨
    ∃v,q=v+1 ∧ live v ∧ cv tr t v query=0 ∧
      address tr t v=address tr t q ∧ cv tr t v lo=cv tr t q lo ∧ cv tr t v hi=cv tr t q hi ∧
      ∀u,u<tr.height t→live u→cv tr t u query=0→address tr t u=address tr t q→u≤v := by
  classical
  by_cases hw:∃w,w<tr.height t ∧ live w ∧ cv tr t w query=0 ∧ address tr t w=address tr t q
  · obtain ⟨w,hw,hwa,hwq,hwe⟩:=hw
    exact Or.inr (query_with_write live hact hprefix hL ho hq hqa hqq hw hwa hwq hwe)
  · have hn:∀w,w<tr.height t→live w→cv tr t w query=0→address tr t w≠address tr t q := by
      intro w hw' hwa hwq hwe
      exact hw ⟨w,hw',hwa,hwq,hwe⟩
    exact Or.inl ⟨query_without_write live hact hprefix hL hb hq hqa hqq hn,hn⟩
end ZkFormal.NearV3.Candidates.ProcPriorMemoryPredicate
