import ZkFormal.NearV3.Render.Ups.SchedulerPartInputs

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec NearSpecV3 UpsRows Assembly

theorem forestRootAt_exists_of_get : ∀ n vid ts tau t,
    ts[tau]?=some t → ∃ a,forestRootAt n vid ts tau=some a ∧ a.tree=t
  | _,_,[],_,_,h => by simp at h
  | n,vid,t::ts,0,t',h => by
    simp only [List.getElem?_cons_zero,Option.some.injEq] at h
    subst t'
    exact ⟨⟨n,vid,0,t⟩,rfl,rfl⟩
  | n,vid,t::ts,tau+1,t',h => forestRootAt_exists_of_get (n+tsize t) (vid+(valsOf t).length) ts tau t' h

/-- Accepted native input constructs all update parts and their local semantic
inputs. The theorem has no independent prefix, value, depth, byte-copy, window,
memory, child-ID or child-length premise. Global row placement and bus accounting
remain separate from this per-part construction. -/
theorem checkD0a_partInputs {cb wb : Bytes} {claim : WalkD0} {w : StateWitness}
    (hk : walkD0 cb=.ok claim) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    (baseI : Nat→UpsInst) (base : Nat→Nat→UpsPartI) :
    ∃ us : List SchedulerUpsertWitness,
      1≤us.length ∧ us.length≤32 ∧
      ∀ tau u,us[tau]?=some u → ∃ root : OccurrenceAddress,
        forestRootAt 0 0 (us.map SchedulerUpsertWitness.pre) tau=some root ∧
        ∃ Qs : List UpsPartI,
          encodeNativeParts
            (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])) root.tree u.run
            (nativeSourceBase (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
              u.run (base tau))=some Qs ∧
          ∀ k,k<Qs.length →
            let I := nativeInstance (pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15]))
              (baseI tau) root.tree u.run u.value Qs
            Nonempty (ByteInput I (part I k)) ∧ FieldsOk (part I k) ∧ PartOk I k (part I k) ∧
              WindowOk I (part I k) ∧ MemOk I (part I k) ∧
              (part I k).jm-1<Qs.length ∧ (part I k).clen=(child I (part I k)).q.length := by
  obtain ⟨us,hpos,hlen,hgood,hpre,hout,_⟩ := checkD0a_upsert_all_bounds hk hw h
  refine ⟨us,hpos,hlen,?_⟩
  intro tau u hu
  have hget : (us.map SchedulerUpsertWitness.pre)[tau]?=some u.pre := by
    simp only [List.getElem?_map,hu,Option.map_some]
  obtain ⟨root,hroot,htree⟩ := forestRootAt_exists_of_get 0 0 _ tau u.pre hget
  have hr : traceUpsert root.tree [0,15] u.value=some u.run := by
    simpa only [htree,keyBwState_nibbles] using (hgood u (List.mem_of_getElem? hu)).1.1
  let recordId := pathRecordId (extendedAddresses root.nid root.vid root.depth root.tree [0,15])
  obtain ⟨Qs,he,_⟩ := encodeNativeParts_total recordId hr (nativeSourceBase recordId u.run (base tau))
  refine ⟨root,hroot,Qs,he,?_⟩
  intro k hbound
  exact scheduler_partInputs hgood hpre hout hu hroot (baseI tau) (base tau) he k hbound
end ZkFormal.NearV3.Render.UpsGen
