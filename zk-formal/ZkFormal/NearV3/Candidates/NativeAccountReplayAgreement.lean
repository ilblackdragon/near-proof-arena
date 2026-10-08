import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountReadPair
import ZkFormal.NearV3.Rcpt.Candidates.NativeAccountNativeAllocation

namespace ZkFormal.NearV3.Candidates.NativeAccountReplayAgreement
open NearSpec NearSpecV3 ZkFormal.Near Assembly Rcpt.Candidates Rcpt.Candidates.NodePostUpdate

theorem indexed_agreement {a b : PTrie} {key : List Nat} {i : Nat}
    (ha : valueIndex a key=some i) (hb : valueIndex b key=some i)
    (hr : a.find key=b.find key) :
    (NearSpecV3.valsOf a)[i]?=(NearSpecV3.valsOf b)[i]? := by
  obtain ⟨va,hva⟩:=valueIndex_defined a key i ha
  obtain ⟨vb,hvb⟩:=valueIndex_defined b key i hb
  have he : va=vb := Option.some.inj (Option.some.inj (hva.symm.trans (hr.trans hvb)))
  obtain ⟨j,hj,hja⟩:=valueIndex_complete a key va hva
  obtain ⟨l,hl,hlb⟩:=valueIndex_complete b key vb hvb
  have hji : j=i := Option.some.inj (hj.symm.trans ha)
  have hli : l=i := Option.some.inj (hl.symm.trans hb)
  subst j; subst l
  rw [hja,hlb,he]

theorem closing_agreement {pre a b : PTrie} (ha : WriteTreePair pre a)
    (hb : WriteTreePair pre b) (keys : List (List Nat)) (key : List Nat)
    (hr : a.find key=b.find key) :
    closingAccountView pre a keys key=closingAccountView pre b keys key := by
  unfold closingAccountView
  cases hi : valueIndex pre key with
  | none => rfl
  | some i =>
    have hia : valueIndex a key=some i := (write_value_index ha key).symm.trans hi
    have hib : valueIndex b key=some i := (write_value_index hb key).symm.trans hi
    simp only [bind,Option.bind]
    rw [indexed_agreement hia hib hr]

theorem list_agreement {pre a b : PTrie} (ha : WriteTreePair pre a)
    (hb : WriteTreePair pre b) (keys selected : List (List Nat))
    (hr : ∀key∈selected,a.find key=b.find key) :
    closingAccountViews pre a keys selected=closingAccountViews pre b keys selected := by
  induction selected with
  | nil => rfl
  | cons key rest ih =>
    simp only [closingAccountViews,closing_agreement ha hb keys key (hr key (by simp)),
      ih (fun key hk=>hr key (by simp [hk]))]

theorem native_agreement {pre a b : PTrie} (ha : WriteTreePair pre a)
    (hb : WriteTreePair pre b) (rs : List Receipt)
    (hr : ∀account,a.find (accountKeyPath account)=b.find (accountKeyPath account)) :
    nativeAccountViews pre a rs=nativeAccountViews pre b rs := by
  apply list_agreement ha hb
  intro key hk
  have hm := (distinctTouched_mem key _).mp hk
  obtain ⟨r,_,rfl⟩:=List.mem_map.mp hm
  exact hr r.receiverId

/-- Replays may be chosen independently, but their closing account records are
identical when their final scheduler updates yield the same actual final trie. -/
theorem scheduler_agreement {pre a b final : PTrie}
    (ha : WriteTreePair pre a) (hb : WriteTreePair pre b)
    (hwa : a.wf=true) (hwb : b.wf=true) {sa sb : Bytes}
    (hua : a.upsert keyBwState sa=some final) (hub : b.upsert keyBwState sb=some final)
    (rs : List Receipt) : nativeAccountViews pre a rs=nativeAccountViews pre b rs := by
  apply native_agreement ha hb rs
  intro account
  have hfa : final.find (accountKeyPath account)=a.find (accountKeyPath account) := ZkFormal.NearV3.find_upsert_ne hwa (by decide)
    (by simp [keyBwState,accountKeyPath,nibbles]) hua
  have hfb : final.find (accountKeyPath account)=b.find (accountKeyPath account) := ZkFormal.NearV3.find_upsert_ne hwb (by decide)
    (by simp [keyBwState,accountKeyPath,nibbles]) hub
  exact hfa.symm.trans hfb

/-- The allocated first scheduler witness supplies the concrete replay upsert
needed by the account agreement theorem. -/
theorem allocated_upsert (us : List SchedulerUpsertWitness) (oldPost final : PTrie)
    (rest : List (PTrie×PTrie))
    (hp : us.map (fun u=>(u.pre,u.run.output))=(oldPost,final)::rest)
    (hv : ∀u∈us,u.Valid) : ∃state,oldPost.upsert keyBwState state=some final := by
  cases us with
  | nil => simp at hp
  | cons u us =>
    have he : u.pre=oldPost ∧ u.run.output=final := by
      simpa only [List.map_cons,List.cons.injEq,Prod.mk.injEq] using (And.left (List.cons.inj hp))
    obtain ⟨so,hs,_⟩:=(hv u (by simp)).2
    obtain ⟨_,_,_,_,_,_,_,hu⟩:=schedStep_complete hs
    exact ⟨so.state,by simpa only [he.1,he.2] using hu⟩

end ZkFormal.NearV3.Candidates.NativeAccountReplayAgreement
