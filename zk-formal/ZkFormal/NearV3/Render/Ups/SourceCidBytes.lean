import ZkFormal.NearV3.Render.Ups.ForestNativeWalk
import ZkFormal.NearV3.Render.Node.Layout

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near ZkFormal.Near.Render
open NodeGen (F layout)

/-- Serialized source child-ID column, derived from actual occurrence windows. -/
def sourceCidBytes (node : NodeV3) : List Nat :=
  (layout (NodeGen3.fieldsOf node) (NodeGen3.hplenOf node)).map fun fi =>
    match fi.1.chw with | some w => w.cid | none => 0

theorem sourceCidBytes_get (node : NodeV3) (p : Nat) :
    (sourceCidBytes node).getD p 0=
      match ((layout (NodeGen3.fieldsOf node) (NodeGen3.hplenOf node)).getD p default).1.chw with
      | some w => w.cid | none => 0 := by
  simp only [sourceCidBytes,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases (layout (NodeGen3.fieldsOf node) (NodeGen3.hplenOf node))[p]? <;> rfl

/-- The executable source column equals the actual node renderer's cid cell,
including zero outside child windows. No supplied column equality is assumed. -/
theorem sourceCidBytes_provider {nodes : List NodeS3} {n : Nat} {s : NodeS3}
    (hs : nodes[n]?=some s) (p : Nat) :
    (sourceCidBytes s.v).getD p 0=NodeGen3.cidAt nodes n p := by
  rw [sourceCidBytes_get]
  simp [NodeGen3.cidAt,NodeGen3.layN,NodeGen3.rec,List.getD_eq_getElem?_getD,hs]
  rfl

theorem sourceCidBytes_length (node : NodeV3) (hw : node.wf) :
    (sourceCidBytes node).length=(node.ser true).length := by
  simp only [sourceCidBytes,List.length_map]
  exact (NodeGen3.ser_len hw true).symm

/-- Fill source child-ID columns from the native source's actual occurrence address.
The value ID is irrelevant to child windows and may remain a zero seed. -/
def nativeCidBase (recordId : PTrie→Nat) (run : TreeRun) (base : Nat→UpsPartI) (k : Nat) : UpsPartI :=
  match run.parts[k]? with
  | none => base k
  | some p => {base k with pcid:=sourceCidBytes (viewNode (recordId p.source) 0 p.source)}

theorem encodeTreePart_pcid {base Q : UpsPartI} {part : TreePart}
    (he : encodeTreePart base part=some Q) : Q.pcid=base.pcid := by
  unfold encodeTreePart at he
  cases hs : treeNode part.source <;> cases hd : treeNode part.output <;> simp [hs,hd] at he
  subst Q; rfl


theorem sourceCidBytes_valueId (n v1 v2 : Nat) (t : PTrie) :
    sourceCidBytes (viewNode n v1 t)=sourceCidBytes (viewNode n v2 t) := by
  cases t with
  | hash | ext => rfl
  | leaf key slot mem => cases slot <;> rfl
  | branch value kids mem => cases value with
    | none => rfl
    | some slot => cases slot <;> rfl

/-- Native source metadata is the actual global node column at every byte position. -/
theorem forest_nativeCidBase {ts : List PTrie} {tau : Nat} {root : Assembly.OccurrenceAddress}
    (hroot : Assembly.forestRootAt 0 0 ts tau=some root) {key : List Nat} {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree key value=some run) (base : Nat→UpsPartI)
    {k : Nat} {part : TreePart} (hp : run.parts[k]?=some part) (pos : Nat) :
    let recordId := Assembly.pathRecordId
      (Assembly.extendedAddresses root.nid root.vid root.depth root.tree key)
    ((nativeCidBase recordId run base k).pcid).getD pos 0=
      NodeGen3.cidAt (Assembly.forestStoreViews ts).nodes (recordId part.source) pos := by
  obtain ⟨a,ha,he,hid,hget⟩ := Assembly.forest_traceUpsert_extended_provider hroot hr (List.mem_of_getElem? hp)
  dsimp only
  simp only [nativeCidBase,hp,hid]
  rw [sourceCidBytes_valueId a.nid 0 a.vid part.source]
  exact sourceCidBytes_provider hget pos


/-- Positional metadata and canonical serialization preserve the constructed
source column; its entries remain exactly the provider node's UPB child IDs. -/
theorem forest_encoded_pcid {ts : List PTrie} {tau : Nat} {root : Assembly.OccurrenceAddress}
    (hroot : Assembly.forestRootAt 0 0 ts tau=some root) {value : Bytes} {run : TreeRun}
    (hr : traceUpsert root.tree [0,15] value=some run) (base : Nat→UpsPartI)
    {k : Nat} {part : TreePart} (hp : run.parts[k]?=some part) {Q : UpsPartI}
    (he : encodeTreePart
      (nativePartBase (Assembly.pathRecordId
        (Assembly.extendedAddresses root.nid root.vid root.depth root.tree [0,15])) root.tree run
        (nativeCidBase (Assembly.pathRecordId
          (Assembly.extendedAddresses root.nid root.vid root.depth root.tree [0,15])) run base) k) part=some Q)
    (pos : Nat) :
    Q.pcid.getD pos 0=NodeGen3.cidAt (Assembly.forestStoreViews ts).nodes
      (Assembly.pathRecordId (Assembly.extendedAddresses root.nid root.vid root.depth root.tree [0,15])
        part.source) pos := by
  rw [encodeTreePart_pcid he]
  simp only [nativePartBase,hp,positionedPart]
  exact forest_nativeCidBase hroot hr base hp pos
end ZkFormal.NearV3.Render.UpsGen
