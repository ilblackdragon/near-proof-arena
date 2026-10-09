import ZkFormal.NearV3.Candidates.ProcPriorMemoryPredicate
namespace ZkFormal.NearV3.Candidates.ProcPriorMemoryStampMax
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorMemoryTable ProcPriorAddressOrder
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}
variable (live : Nat→Prop)
variable (hact:∀r,live r→cv tr t r act=1)
variable (hprefix:∀s,s<tr.height t→live s→∀r,r≤s→live r)
variable (hL:∀r,r<tr.height t→live r→ProcPriorMemorySoundRows.At tr t r pub)
variable (ho:∀s,s<tr.height t→live s→∀r,r≤s→address tr t r≤address tr t s)
variable (hstamp:∀r,r+1<tr.height t→live r→live (r+1)→address tr t r=address tr t (r+1)→
  cv tr t (r+1) query=0→cv tr t r stamp<cv tr t (r+1) stamp)
include hact hprefix hL ho hstamp

theorem stamp_order (v : Nat) (hv:v<tr.height t) (hva:live v) (hvq:cv tr t v query=0)
    (u : Nat) (hu:u≤v) (he:address tr t u=address tr t v) :cv tr t u stamp≤cv tr t v stamp := by
  induction v generalizing u with
  | zero=>have :u=0 := by omega
          subst u;exact Nat.le_refl _
  | succ v ih=>
    by_cases heq:u=v+1
    · subst u;exact Nat.le_refl _
    · have hva0:=hprefix (v+1) hv hva v (by omega)
      have hv0:v<tr.height t := by omega
      have hl:=ho v hv0 hva0 u (by omega)
      have hr:=ho (v+1) hv hva v (by omega)
      have had:address tr t v=address tr t (v+1) := by omega
      have hvq0:cv tr t v query=0 := by
        have hb:=ProcPriorMemorySoundRows.flag (hL v hv0 hva0) (x:=query) (by simp)
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hz|hz
        · exact hz
        · exact (ProcPriorMemoryLastWrite.query_stop (hL v hv0 hva0) hv (hact _ hva0) (hact _ hva) hz had).elim
      have hi:=ih hv0 hva0 hvq0 u (by omega) (by omega)
      have hs:=hstamp v hv hva0 hva had hvq
      omega

/-- Natural stamp order turns the greatest physical write into the greatest
original-ordinal candidate. Authenticating the stamp as an original decoded
record ordinal is supplied separately by the actual write67 provenance. -/
theorem query_max_stamp
    (hb:∀r,r<tr.height t→live r→address tr t r<P)
    {q : Nat} (hq:q<tr.height t) (hqa:live q) (hqq:cv tr t q query=1) :
    ((cv tr t q lo=0 ∧ cv tr t q hi=0) ∧
      ∀w,w<tr.height t→live w→cv tr t w query=0→address tr t w≠address tr t q) ∨
    ∃v,q=v+1 ∧ live v ∧ cv tr t v query=0 ∧
      address tr t v=address tr t q ∧ cv tr t v lo=cv tr t q lo ∧ cv tr t v hi=cv tr t q hi ∧
      ∀u,u<tr.height t→live u→cv tr t u query=0→address tr t u=address tr t q→
        u≤v ∧ cv tr t u stamp≤cv tr t v stamp := by
  rcases ProcPriorMemoryPredicate.query_last_write live hact hprefix hL ho hb hq hqa hqq with hz|⟨v,hv,hva,hvq,haddr,hlo,hhi,hmax⟩
  · exact Or.inl hz
  · refine Or.inr ⟨v,hv,hva,hvq,haddr,hlo,hhi,?_⟩
    intro u hu hua huq hue
    have huv:=hmax u hu hua huq hue
    exact ⟨huv,stamp_order live hact hprefix hL ho hstamp v (by omega) hva hvq u huv (hue.trans haddr.symm)⟩
end ZkFormal.NearV3.Candidates.ProcPriorMemoryStampMax
