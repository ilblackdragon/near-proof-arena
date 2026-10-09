import ZkFormal.NearV3.Assembly.SchedulerPartMessages

namespace ZkFormal.NearV3.Assembly
open NearSpec Render Render.UpsGen UpsRows ZkFormal.Air ZkFormal.Near

private def blankPart : TreePart := ⟨.RLP,.hash [],.hash [],0⟩

private theorem indexed_plan (cs : UCase) (start : Nat) (ps : List TreePart) :
    (List.range ps.length).flatMap (fun k=>partDigestUses cs (start+k) (ps.getD k blankPart).kind)=
      planDigestUses cs start (ps.map TreePart.kind) := by
  induction ps generalizing start with
  | nil=>rfl
  | cons p ps ih=>
    simp only [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
      List.getD_cons_zero,List.getD_cons_succ,List.map_cons,planDigestUses,Nat.add_zero]
    rw [←ih (start+1)]
    congr 1
    apply congrArg (fun f=>(List.range ps.length).flatMap f)
    funext k
    simp only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem flat_perm {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀x∈xs,(f x).Perm (g x)) : (xs.flatMap f).Perm (xs.flatMap g) := by
  induction xs with
  | nil=>exact List.Perm.refl []
  | cons x xs ih=>
    simp only [List.flatMap_cons]
    exact (h x (by simp)).append (ih (fun y hy=>h y (by simp [hy])))

/-- All actual serialized child-window payloads match the native SHA jobs
before the final root, with exact multiplicity and no assumed hash identities. -/
theorem nativeInstance_node_messages (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {v : Bytes} {run : TreeRun}
    (hr : traceUpsert root [0,15] v=some run) (hw : root.wf=true)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run (nativeSourceBase recordId run base)=some Qs)
    (hi : InstOk (nativeInstance recordId baseI root run v Qs))
    (hparts : NativePartFamily (nativeInstance recordId baseI root run v Qs)) :
    let I:=nativeInstance recordId baseI root run v Qs
    (((List.range (nQ I)).flatMap (fun k=>(List.range (part I k).q.length).flatMap
      (CompactPhysicalDigests.nodeDigestMsgs I k))).map Msg.toFp).Perm
      ((List.range run.parts.length).map (fun j=>(nativeJobMessage run v I.tau j).toFp)) := by
  let I:=nativeInstance recordId baseI root run v Qs
  have hframe:=nativeInstance_digest_frame recordId baseI hr (nativeSourceBase recordId run base) he
  change (((List.range (nQ I)).flatMap (fun k=>(List.range (part I k).q.length).flatMap
      (CompactPhysicalDigests.nodeDigestMsgs I k))).map Msg.toFp).Perm _
  rw [List.map_flatMap]
  have hh : ((List.range (nQ I)).flatMap (fun k=>
      ((List.range (part I k).q.length).flatMap (CompactPhysicalDigests.nodeDigestMsgs I k)).map Msg.toFp)).Perm
      ((List.range (nQ I)).flatMap (fun k=>
        (partDigestUses run.terminal k (run.parts.getD k blankPart).kind).map
          (fun j=>(nativeJobMessage run v I.tau j).toFp))) := by
    apply flat_perm
    intro k hk
    have hkr:k<run.parts.length:=by rw [←hframe.2.2.1];exact List.mem_range.mp hk
    have hp:run.parts[k]?=some (run.parts.getD k blankPart):=by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hkr,Option.getD_some]
    exact nativeInstance_part_messages recordId baseI hr hw base he hp hi hparts
  have heq : (List.range (nQ I)).flatMap (fun k=>
        (partDigestUses run.terminal k (run.parts.getD k blankPart).kind).map
          (fun j=>(nativeJobMessage run v I.tau j).toFp))=
      (List.range run.parts.length).map (fun j=>(nativeJobMessage run v I.tau j).toFp) := by
    rw [←List.map_flatMap,hframe.2.2.1]
    have hp:=indexed_plan run.terminal 0 run.parts
    simp only [Nat.zero_add] at hp
    rw [hp,planned_digest_uses (traceUpsert_plan root [0,15] v run hr)]
  exact heq ▸ hh

end ZkFormal.NearV3.Assembly
