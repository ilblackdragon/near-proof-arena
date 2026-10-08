import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountLastWrite
namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec

/-- A nonzero selected version refers to the exact original write position,
not a compressed index among writes to that account. -/
theorem lastWriteRecord_position (key : List Nat) (start : Nat) (ws : List (List Nat×Bytes))
    {t : Nat} {bytes : Bytes} (h:lastWriteRecord key start ws=some (t,bytes)) :
    ∃j,ws[j]?=some (key,bytes) ∧ t=start+j+1 := by
  induction ws generalizing start with
  | nil=>simp [lastWriteRecord] at h
  | cons w ws ih=>
    cases hl:lastWriteRecord key (start+1) ws with
    | some p=>
      have he:p=(t,bytes):=by simpa only [lastWriteRecord,hl,Option.some.injEq] using h
      subst p
      obtain ⟨j,hj,hv⟩:=ih (start+1) hl
      exact ⟨j+1,by simpa using hj,by omega⟩
    | none=>
      simp only [lastWriteRecord,hl] at h
      split at h
      · rename_i hk
        have he:w.2=bytes:=congrArg Prod.snd (Option.some.inj h)
        have ht:start+1=t:=congrArg Prod.fst (Option.some.inj h)
        exact ⟨0,congrArg some (Prod.ext hk he),by omega⟩
      · cases h

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
