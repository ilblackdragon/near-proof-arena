import ZkFormal.NearV3.Rcpt.Candidates.NativeForestMetadata
import ZkFormal.NearV3.Render.Node.TLay
namespace ZkFormal.NearV3.Candidates.NativeNodeChildIds
open ZkFormal.Near Render Render.NodeGen3 Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near.Render.NodeGen (F Win layout)

def cid (f : F) : Nat := match f.chw with | some w=>w.cid | none=>0

theorem layout_ids (fs : List F) (h : Nat) :
    (layout fs h).map (fun p=>cid p.1)=fs.flatMap (fun f=>List.replicate (f.len h) (cid f)) := by
  simp [layout,List.map_flatMap,List.map_map,Function.comp_def,List.map_const']

private theorem zip_flat {α β γ : Type} (xs : List α) (ys : List β) (f : α→List γ)
    (h : xs.length≤ys.length) : (xs.zip ys).flatMap (fun p=>f p.1)=xs.flatMap f := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys => simp only [List.zip_cons_cons,List.flatMap_cons];rw [ih ys (by simpa using h)]

/-- Branch layout windows retain exactly the child IDs of the native view. -/
theorem branch_ids (cs : List NKid) :
    (branchWins cs).flatMap (fun f=>List.replicate (f.len 0) (cid f))=cs.flatMap Rcpt.Candidates.NodePostUpdate.kidIds := by
  unfold branchWins
  simp only [List.flatMap_map,cid,F.chw,F.len]
  have hkid : ∀k w l s,(kidWin k w l s).cid=(kidWin k 0 false none).cid := by
    intro k w l s;cases k <;> rfl
  simp only [hkid]
  rw [zip_flat _ _ (fun p : NKid×Nat=>List.replicate 32 (kidWin p.1 0 false none).cid) (by simp)]
  have he : ∀xs : List (NKid×Nat),
      ((xs.filter fun p=>p.1≠.none).flatMap fun p=>List.replicate 32 (kidWin p.1 0 false none).cid)=
      xs.flatMap (fun p=>Rcpt.Candidates.NodePostUpdate.kidIds p.1) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons p xs ih =>
      rcases p with ⟨k,i⟩
      cases k with
      | none => exact ih
      | hash h => exact congrArg (List.append (List.replicate 32 0)) ih
      | node c l r pre post => exact congrArg (List.append (List.replicate 32 c)) ih

  rw [he,zip_flat _ _ Rcpt.Candidates.NodePostUpdate.kidIds (by simp)]
private theorem slot_length (v : NSlot3) (h : v.wf) : (v.bytes false).length=36 := by
  cases v <;> simp_all [NSlot3.wf,NSlot3.bytes]

theorem window_layout (v : NodeV3) (hv : v.wf) :
    (layout (fieldsOf v) (hplenOf v)).map (fun p=>cid p.1)=windowIds v := by
  rw [layout_ids]
  cases v with
  | leaf k sl m =>
    have hs:=slot_length sl hv.2.1
    have hm:=hv.2.2
    simp only [fieldsOf,List.flatMap_cons,List.flatMap_nil,F.len,cid,F.chw,hplenOf,isLE,
      keyOf,ite_true,windowIds,NodeV3.ser,List.length_append,List.length_cons,List.length_nil,
      u32Bytes_length,hpN_len,hs,hm]
    simp only [List.append_nil,List.replicate_append_replicate]
    try congr 1 <;> omega
  | ext k kid m =>
    have hn:=hv.2.1
    simp only [fieldsOf,List.flatMap_cons,List.flatMap_nil,F.len,cid,F.chw,hplenOf,isLE,
      keyOf,ite_true,windowIds,hpN_len]
    have hlen : 1+k.length/2-1=k.length/2 := by omega
    rw [hlen]
    cases kid with
    | none => exact False.elim (hn rfl)
    | hash h =>
      simp only [kidWin,Rcpt.Candidates.NodePostUpdate.kidIds,List.append_nil,←List.append_assoc,List.replicate_append_replicate]
      congr 1 <;> omega
    | node c l r pre post =>
      simp only [kidWin,Rcpt.Candidates.NodePostUpdate.kidIds,List.append_nil,←List.append_assoc,List.replicate_append_replicate]
      rw [show 1+(4+(1+k.length/2))=5+(1+k.length/2) by omega]
  | branch sv cs m =>
    have hb := branch_ids cs
    have hh:=congrArg (fun xs=>List.replicate (if sv.isSome then 39 else 3) 0++xs++List.replicate 8 0) hb
    cases sv <;> simpa [fieldsOf,hplenOf,isLE,windowIds,F.len,cid,F.chw,
      List.flatMap_append,List.flatMap_cons,List.replicate_append_replicate,List.append_assoc] using hh

theorem window_at (v : NodeV3) (hv : v.wf) (p : Nat) :
    (windowIds v).getD p 0=cid ((layout (fieldsOf v) (hplenOf v)).getD p default).1 := by
  rw [←window_layout v hv]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases (layout (fieldsOf v) (hplenOf v))[p]? <;> rfl

/-- Initialized child-ID metadata equals the actual generator column. -/
theorem initialized_cid (vs : List NodeS3) (hw : ∀s∈vs,s.v.wf) (n p : Nat) (hn : n<vs.length) :
    ((initializeList 0 vs).getD n default).ucid.getD p 0=
      cidAt (initializeList 0 vs) n p := by
  have hi : n<(initializeList 0 vs).length := by simpa [initializeList_length] using hn
  have hg:=initializeList_get vs 0 n
  simp only [List.getElem?_eq_getElem hn,List.getElem?_eq_getElem hi,Option.map_some,
    Option.some.injEq,Nat.zero_add] at hg
  have hd : (initializeList 0 vs).getD n default=initializeMetadata n vs[n] := by
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi] using hg
  simp only [cidAt,layN,rec,hd,initializeMetadata]
  rw [window_at vs[n].v (hw vs[n] (List.getElem_mem hn)) p]
  rfl

end ZkFormal.NearV3.Candidates.NativeNodeChildIds
