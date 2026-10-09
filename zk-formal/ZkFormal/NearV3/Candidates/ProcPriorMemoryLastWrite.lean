import ZkFormal.NearV3.Candidates.ProcPriorAddressOrder
namespace ZkFormal.NearV3.Candidates.ProcPriorMemoryLastWrite
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem active_prefix (hL:ProcPriorMemorySound.LocalM tr t pub)
    (s : Nat) (hs:s<tr.height t) (ha:cv tr t s act=1) (r : Nat) (hr:r≤s) :cv tr t r act=1 := by
  induction s generalizing r with
  | zero=>have :r=0 := by omega
          subst r;exact ha
  | succ s ih=>
    by_cases he:r=s+1
    · subst r;exact ha
    · exact ih (by omega) (ProcPriorMemorySound.active_prev hL hs ha) r (by omega)

theorem same_of_address {r : Nat} (hL:ProcPriorMemorySoundRows.At tr t r pub)
    (hr:r+1<tr.height t) (ha:cv tr t r act=1) (hn:cv tr t (r+1) act=1)
    (he:address tr t r=address tr t (r+1)) :cv tr t r same=1 := by
  have hd:zev (tenv tr t r pub) delta=0 := by
    simp only [delta,nextAddr,addr,zev_sub,zev_add,zev_mul,zev_k,zev_c,zev_n,cur_cv,Codec.nx hr]
    unfold address at he
    omega
  obtain ⟨q,hq⟩:=ProcPriorMemorySoundRows.zdvd hL
    (e:=.mul adjacent (sub (.mul delta (c inverse)) (notE (c same)))) (by simp [constraints])
  simp only [adjacent,notE,zev_mul,zev_sub,zev_k,zev_c,zev_n,cur_cv,Codec.nx hr,ha,hn,hd] at hq
  have hb:=ProcPriorMemorySoundRows.flag hL (x:=same) (by simp)
  omega

theorem query_stop {r : Nat} (hL:ProcPriorMemorySoundRows.At tr t r pub)
    (hr:r+1<tr.height t) (ha:cv tr t r act=1) (hn:cv tr t (r+1) act=1)
    (hq:cv tr t r query=1) :address tr t r≠address tr t (r+1) := by
  intro he
  have hs:=same_of_address hL hr ha hn he
  obtain ⟨q,h⟩:=ProcPriorMemorySoundRows.zdvd hL
    (e:=.mul adjacent (.mul (c query) (c same))) (by simp [constraints])
  simp only [adjacent,zev_mul,zev_c,zev_n,cur_cv,Codec.nx hr,ha,hn,hq,hs] at h
  omega

/-- A query ends its entire address group when comparator-derived global
address ordering is available. It cannot be followed later by that address. -/
theorem no_later_same (hL:ProcPriorMemorySound.LocalM tr t pub)
    (ho:∀s,s<tr.height t→cv tr t s act=1→∀r,r≤s→address tr t r≤address tr t s)
    {q s : Nat} (hq:q<tr.height t) (hqa:cv tr t q act=1) (hqq:cv tr t q query=1)
    (hs:s<tr.height t) (hsa:cv tr t s act=1) (hqs:q<s) :address tr t q≠address tr t s := by
  intro he
  have hqa1:cv tr t (q+1) act=1 := active_prefix hL s hs hsa (q+1) (by omega)
  have hq1:q+1<tr.height t := by omega
  have hab:=ho (q+1) hq1 hqa1 q (by omega)
  have hbc:=ho s hs hsa (q+1) (by omega)
  have he':address tr t q=address tr t (q+1) := by omega
  exact query_stop (hL q hq) hq1 hqa hqa1 hqq he'

theorem write_before_query (hL:ProcPriorMemorySound.LocalM tr t pub)
    (ho:∀s,s<tr.height t→cv tr t s act=1→∀r,r≤s→address tr t r≤address tr t s)
    {q w : Nat} (hq:q<tr.height t) (hqa:cv tr t q act=1) (hqq:cv tr t q query=1)
    (hw:w<tr.height t) (hwa:cv tr t w act=1) (hwq:cv tr t w query=0)
    (he:address tr t w=address tr t q) :w<q := by
  by_cases h:w<q
  · exact h
  · by_cases hqw:q=w
    · subst w;omega
    · exact (no_later_same hL ho hq hqa hqq hw hwa (by omega) he.symm).elim

/-- If an address has any write, the query reads its greatest physical-row
write. Global stamp monotonicity can then identify the greatest original
ordinal; decoded write inventory/authentication remains a separate premise. -/
theorem query_with_write (hL:ProcPriorMemorySound.LocalM tr t pub)
    (ho:∀s,s<tr.height t→cv tr t s act=1→∀r,r≤s→address tr t r≤address tr t s)
    {q w : Nat} (hq:q<tr.height t) (hqa:cv tr t q act=1) (hqq:cv tr t q query=1)
    (hw:w<tr.height t) (hwa:cv tr t w act=1) (hwq:cv tr t w query=0)
    (he:address tr t w=address tr t q) :
    ∃v,q=v+1 ∧ cv tr t v act=1 ∧ cv tr t v query=0 ∧
      address tr t v=address tr t q ∧ cv tr t v lo=cv tr t q lo ∧ cv tr t v hi=cv tr t q hi ∧
      ∀u,u<tr.height t→cv tr t u act=1→cv tr t u query=0→address tr t u=address tr t q→u≤v := by
  have hwq':w<q:=write_before_query hL ho hq hqa hqq hw hwa hwq he
  have hq0:0<q := by omega
  obtain ⟨v,hqv⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : q≠0)
  subst q
  simp only [Nat.succ_eq_add_one] at *
  have hv:v<tr.height t := by omega
  have hva:=ProcPriorMemorySound.active_prev hL hq hqa
  have hleft:=ho v hv hva w (by omega)
  have hright:=ho (v+1) hq hqa v (by omega)
  have had:address tr t v=address tr t (v+1) := by omega
  have hsame:=same_of_address (hL v hv) hq hva hqa had
  have hvq:cv tr t v query=0 := by
    have hb:=ProcPriorMemorySound.flag hL hv (x:=query) (by simp)
    obtain ⟨z,hz⟩:=Mem.zdvd hL hv (e:=.mul adjacent (.mul (c query) (c same))) (by simp [constraints])
    simp only [adjacent,zev_mul,zev_c,zev_n,cur_cv,Codec.nx hq,hva,hqa,hsame] at hz
    omega
  have carry (x y : Nat) (hx:(x=beforeLo ∧ y=lo) ∨ (x=beforeHi ∧ y=hi)) :cv tr t (v+1) x=cv tr t v y := by
    obtain ⟨z,hz⟩:=Mem.zdvd hL hv (e:=.mul adjacent (sub (n x) (.mul (c same) (c y)))) (by
      rcases hx with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [constraints])
    simp only [adjacent,zev_mul,zev_sub,zev_c,zev_n,cur_cv,Codec.nx hq,hva,hqa,hsame] at hz
    have hb0:=cv_lt (tr:=tr) (t:=t) (v+1) x
    have hb1:=cv_lt (tr:=tr) (t:=t) v y
    omega
  have hc:=ProcPriorMemorySound.query_before hL hq hqa hqq
  refine ⟨v,rfl,hva,hvq,had,?_,?_,?_⟩
  · exact (hc.1.trans (carry beforeLo lo (by simp))).symm
  · exact (hc.2.trans (carry beforeHi hi (by simp))).symm
  · intro u hu hua huq hue
    have :=write_before_query hL ho hq hqa hqq hu hua huq hue
    omega

theorem query_without_write (hL:ProcPriorMemorySound.LocalM tr t pub)
    (hb:∀r,r<tr.height t→cv tr t r act=1→address tr t r<P)
    {q : Nat} (hq:q<tr.height t) (ha:cv tr t q act=1) (hqq:cv tr t q query=1)
    (hn:∀w,w<tr.height t→cv tr t w act=1→cv tr t w query=0→address tr t w≠address tr t q) :
    cv tr t q lo=0 ∧ cv tr t q hi=0 := by
  rcases ProcPriorMemorySound.query_origin hL hq ha hqq with hz|⟨v,hv,hva,hvq,he,_,_⟩
  · exact hz
  · have ev (r : Nat):addr.eval tr t r pub=Fp.ofNat (address tr t r) :=
      Codec.ev_of (by simp only [address,addr,zev_add,zev_mul,zev_k,zev_c,cur_cv,Int.natCast_add,Int.natCast_mul])
    rw [ev v,ev q] at he
    have had:=ProcPriorCodecSoundPublicId.nat_eq _ _ (hb v (by omega) hva) (hb q hq ha) he
    exact (hn v (by omega) hva hvq had).elim

/-- Full row-order last-write semantics for arbitrary memory Local. All writes
of this address are accounted for, including the initialized no-write case.
The global order/range premises are exactly the comparator/provenance bridge,
not an assumed generated event list or a native allowance equality. -/
theorem query_last_write (hL:ProcPriorMemorySound.LocalM tr t pub)
    (ho:∀s,s<tr.height t→cv tr t s act=1→∀r,r≤s→address tr t r≤address tr t s)
    (hb:∀r,r<tr.height t→cv tr t r act=1→address tr t r<P)
    {q : Nat} (hq:q<tr.height t) (hqa:cv tr t q act=1) (hqq:cv tr t q query=1) :
    ((cv tr t q lo=0 ∧ cv tr t q hi=0) ∧
      ∀w,w<tr.height t→cv tr t w act=1→cv tr t w query=0→address tr t w≠address tr t q) ∨
    ∃v,q=v+1 ∧ cv tr t v act=1 ∧ cv tr t v query=0 ∧
      address tr t v=address tr t q ∧ cv tr t v lo=cv tr t q lo ∧ cv tr t v hi=cv tr t q hi ∧
      ∀u,u<tr.height t→cv tr t u act=1→cv tr t u query=0→address tr t u=address tr t q→u≤v := by
  classical
  by_cases hw:∃w,w<tr.height t ∧ cv tr t w act=1 ∧ cv tr t w query=0 ∧ address tr t w=address tr t q
  · obtain ⟨w,hw,hwa,hwq,hwe⟩:=hw
    exact Or.inr (query_with_write hL ho hq hqa hqq hw hwa hwq hwe)
  · have hn:∀w,w<tr.height t→cv tr t w act=1→cv tr t w query=0→address tr t w≠address tr t q := by
      intro w hw' hwa hwq hwe
      exact hw ⟨w,hw',hwa,hwq,hwe⟩
    exact Or.inl ⟨query_without_write hL hb hq hqa hqq hn,hn⟩
end ZkFormal.NearV3.Candidates.ProcPriorMemoryLastWrite
