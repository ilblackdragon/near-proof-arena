import ZkFormal.NearV3.Render.Ups.FieldFacts
import ZkFormal.NearV3.Render.Node.Layout

/-! A bridge from ordinary serialized `NodeV3` values to the update field cursor.
No AIR evaluations occur in this representation. -/
set_option maxHeartbeats 1000000
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near.Render
open NodeGen (F)

/-- Drop fields that consume no bytes, notably an empty KEY field. -/
def nonemptyFields (sh : List (Nat × Nat)) : List (Nat × Nat) := sh.filter (fun f => 0 < f.2)

/-- Empty fields do not affect the state or index of a live byte. -/
theorem fieldAt_nonempty (sh : List (Nat × Nat)) (p : Nat) :
    ((fieldAt (nonemptyFields sh) p).1,(fieldAt (nonemptyFields sh) p).2.1) =
      ((fieldAt sh p).1,(fieldAt sh p).2.1) := by
  induction sh generalizing p with
  | nil => rfl
  | cons f sh ih =>
    obtain ⟨s,l⟩ := f
    by_cases hz : l=0
    · subst l
      simpa [nonemptyFields,fieldAt] using ih p
    · have hl : 0 < l := by omega
      simp only [nonemptyFields,List.filter_cons,hl,decide_true,ite_true]
      by_cases hp : p < l
      · simp [fieldAt,hp]
      · simpa only [nonemptyFields,fieldAt,hp,ite_false] using ih (p-l)

def fieldLayout {α : Type} (fs : List α) (len : α → Nat) : List (α × Nat) :=
  fs.flatMap (fun f => (List.range (len f)).map (f,·))

/-- The generic byte layout and the update field cursor select the same field/index. -/
theorem fieldAt_layout {α : Type} [Inhabited α] (fs : List α) (state len : α → Nat) (p : Nat)
    (hp : p < (fieldLayout fs len).length) :
    ((fieldAt (fs.map (fun f => (state f,len f))) p).1,
     (fieldAt (fs.map (fun f => (state f,len f))) p).2.1) =
      (state ((fieldLayout fs len).getD p default).1,((fieldLayout fs len).getD p default).2) := by
  induction fs generalizing p with
  | nil => simp [fieldLayout] at hp
  | cons f fs ih =>
    simp only [fieldLayout,List.flatMap_cons,List.length_append,List.length_map,List.length_range] at hp
    by_cases h : p < len f
    · simp [fieldLayout,List.getD_eq_getElem?_getD,List.getElem?_append,h,fieldAt]
    · have hn : p-len f < (fieldLayout fs len).length := by simpa only [fieldLayout] using (show p-len f < (fs.flatMap (fun f => (List.range (len f)).map (f,·))).length by omega)
      have hi := ih (p-len f) hn
      simpa [fieldLayout,List.getD_eq_getElem?_getD,List.getElem?_append,h,fieldAt] using hi

def nodeRawShape (v : NodeV3) : List (Nat × Nat) :=
  (NodeGen3.fieldsOf v).map (fun f => (f.state-14,f.len (NodeGen3.hplenOf v)))

def nodeTypeCode : NodeV3 → Nat
  | .leaf .. => 0
  | .ext .. => 1
  | .branch none .. => 2
  | .branch (some _) .. => 3

/-- An update part's output is an ordinary well-formed serialized trie node, with its
header metadata and field shape. The underlying node is available for deriving byte facts. -/
structure NodeEncoding (Q : UpsPartI) where
  node : NodeV3
  wf : node.wf
  bytes : Q.q = node.ser false
  shape : Q.shape = nonemptyFields (nodeRawShape node)
  ty : Q.ty = nodeTypeCode node
  hplen : Q.qhk = NodeGen3.hplenOf node
  odd : Q.qodd = NodeGen3.oddOf node

/-- The update cursor identifies the same field as the ordinary node serializer. -/
theorem NodeEncoding.cursor {Q : UpsPartI} (e : NodeEncoding Q) {p : Nat} (hp : p < Q.q.length) :
    ((fieldAt Q.shape p).1,(fieldAt Q.shape p).2.1) =
      (((NodeGen.layout (NodeGen3.fieldsOf e.node) (NodeGen3.hplenOf e.node)).getD p default).1.state-14,
       ((NodeGen.layout (NodeGen3.fieldsOf e.node) (NodeGen3.hplenOf e.node)).getD p default).2) := by
  rw [e.shape,fieldAt_nonempty]
  apply fieldAt_layout
  change p < (NodeGen.layout (NodeGen3.fieldsOf e.node) (NodeGen3.hplenOf e.node)).length
  rw [← NodeGen3.ser_len e.wf false,← e.bytes]
  exact hp

end ZkFormal.NearV3.Render.UpsGen
