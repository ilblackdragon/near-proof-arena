import ZkFormal.NearV3.Render.Ups.NodeFieldsBridge
import ZkFormal.NearV3.Render.Ups.MemPosition

/-! Source/output edits described as typed serializer-field insertions. Byte payloads may
change (including MEM); these inputs record the ordinary layout effect of the edit. -/
namespace ZkFormal.NearV3.Render.UpsGen

inductive LayoutEdit : Nat → List (Nat × Nat) → List (Nat × Nat) → Prop
  | preserve (kind : Nat) (h : kind ∈ [0,1,2,3,11]) (shape) : LayoutEdit kind shape shape
  | value (rest) : LayoutEdit 4 ((0,1)::rest) ((0,1)::(4,4)::(5,32)::rest)
  | child (before after) : LayoutEdit 5 (before++after) (before++(7,32)::after)
  | other (kind : Nat) (h : kind ∉ [0,1,2,3,4,5,11]) (src dst) : LayoutEdit kind src dst

structure SourceLayout (Q : UpsPartI) where
  node : NodeV3
  wf : node.wf
  bytes : Q.pb = node.ser true
  edit : LayoutEdit Q.kind (nonemptyFields (nodeRawShape node)) Q.shape

theorem SourceLayout.sourceLength {Q : UpsPartI} (e : SourceLayout Q) :
    Q.pb.length = fieldsLen (nonemptyFields (nodeRawShape e.node)) := by
  rw [e.bytes,fieldsLen_nonempty]
  exact (NodeGen3.ser_len e.wf true).trans (fieldsLen_layout _ _).symm

theorem LayoutEdit.length_preserve {kind src dst} (e : LayoutEdit kind src dst)
    (hk : kind ∈ [0,1,2,3,11]) : fieldsLen dst = fieldsLen src := by
  cases e with
  | preserve => rfl
  | value => simp at hk
  | child => simp at hk
  | other kind h => simp only [List.mem_cons,List.not_mem_nil,or_false] at hk h; omega

theorem LayoutEdit.length_value {kind src dst} (e : LayoutEdit kind src dst)
    (hk : kind=4) : fieldsLen dst = fieldsLen src+36 := by
  cases e with
  | preserve kind h => simp [hk] at h
  | value => simp; omega
  | child => omega
  | other kind h => simp [hk] at h

theorem LayoutEdit.length_child {kind src dst} (e : LayoutEdit kind src dst)
    (hk : kind=5) : fieldsLen dst = fieldsLen src+32 := by
  cases e with
  | preserve kind h => simp [hk] at h
  | value => omega
  | child => simp [fieldsLen_append]; omega
  | other kind h => simp [hk] at h

theorem SourceLayout.length_preserve {Q : UpsPartI} (e : SourceLayout Q) (f : FieldsOk Q)
    (hk : Q.kind ∈ [0,1,2,3,11]) : Q.q.length = Q.pb.length := by
  rw [f.bytes,e.sourceLength]; exact e.edit.length_preserve hk

theorem SourceLayout.length_value {Q : UpsPartI} (e : SourceLayout Q) (f : FieldsOk Q)
    (hk : Q.kind=4) : Q.q.length = Q.pb.length+36 := by
  rw [f.bytes,e.sourceLength]; exact e.edit.length_value hk

theorem SourceLayout.length_child {Q : UpsPartI} (e : SourceLayout Q) (f : FieldsOk Q)
    (hk : Q.kind=5) : Q.q.length = Q.pb.length+32 := by
  rw [f.bytes,e.sourceLength]; exact e.edit.length_child hk

end ZkFormal.NearV3.Render.UpsGen
