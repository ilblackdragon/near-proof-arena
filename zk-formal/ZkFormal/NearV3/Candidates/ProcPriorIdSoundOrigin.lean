import ZkFormal.NearV3.Candidates.ProcPriorIdSoundRows
namespace ZkFormal.NearV3.Candidates.ProcPriorIdSoundOrigin
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ProcPriorIdTable ProcPriorIdSoundRows
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- A found index in an arbitrary locally valid trace originates at a real,
strictly earlier active public row. This is provenance, not yet first-key-match
soundness (which also requires authenticated comparisons and key ranges). -/
theorem origin (hL:∀r,r<tr.height t→At tr t r pub) {r : Nat}
    (hr:r<tr.height t) (ha:cv tr t r act=1) (hf:cv tr t r found=1) :
    ∃q,q<r ∧ cv tr t q act=1 ∧ cv tr t q isPublic=1 ∧
      cv tr t r index=cv tr t q ordinal := by
  induction r with
  | zero=>have hz:=first (hL 0 hr) rfl;omega
  | succ r ih=>
    obtain ⟨hp,hprev⟩:=previous (hL r (by omega)) hr ha hf
    rcases hprev with ⟨hfound,hindex⟩|⟨hpublic,hindex⟩
    · obtain ⟨q,hq,hqa,hqp,hqi⟩:=ih (by omega) hp hfound
      exact ⟨q,by omega,hqa,hqp,hindex.trans hqi⟩
    · exact ⟨r,by omega,hp,hpublic,hindex⟩

theorem index_bound (hL:∀r,r<tr.height t→At tr t r pub) (n : Nat)
    (hp:∀q,q<tr.height t→cv tr t q act=1→cv tr t q isPublic=1→cv tr t q ordinal<n)
    {r : Nat} (hr:r<tr.height t) (ha:cv tr t r act=1) (hf:cv tr t r found=1) :
    cv tr t r index<n := by
  obtain ⟨q,hq,hqa,hqp,he⟩:=origin hL hr ha hf
  rw [he]
  exact hp q (by omega) hqa hqp

theorem local_origin {pb qb rb cmp : Nat}
    (hL:ZkFormal.Near.TableLocal (ProcPriorIdTable.table pb qb rb cmp) tr t pub) {r : Nat}
    (hr:r<tr.height t) (ha:cv tr t r act=1) (hf:cv tr t r found=1) :
    ∃q,q<r ∧ cv tr t q act=1 ∧ cv tr t q isPublic=1 ∧
      cv tr t r index=cv tr t q ordinal :=
  origin hL.constr hr ha hf
end ZkFormal.NearV3.Candidates.ProcPriorIdSoundOrigin
