import ZkFormal.NearV3.Render.Ups.NodeEncoding

/-! Recover the canonical update field shape from ordinary node serialization. -/
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render
open NodeGen (F)

theorem branch_shape (kids : List NKid) (hk : Nat) :
    (NodeGen3.branchWins kids).map (fun f => (f.state-14,f.len hk)) =
      List.replicate (NodeGen3.branchWins kids).length (7,32) := by
  have allch : ∀ fs : List F, (∀ f ∈ fs, ∃ w, f = .ch w) →
      fs.map (fun f => (f.state-14,f.len hk)) = List.replicate fs.length (7,32) := by
    intro fs
    induction fs with
    | nil => intro _; rfl
    | cons f fs ih =>
      intro h
      obtain ⟨w,rfl⟩ := h f (by simp)
      change (7,32) :: fs.map (fun f => (f.state-14,f.len hk)) = (7,32) :: List.replicate fs.length (7,32)
      rw [ih (fun f hf => h f (by simp [hf]))]
  apply allch
  intro f hf
  obtain ⟨k,w,l,j,_,_,rfl⟩ := NodeGen3.mem_branchWins hf
  exact ⟨_,rfl⟩

def nodeChildren : NodeV3 → Nat
  | .leaf .. => 0
  | .ext .. => 1
  | .branch _ ks _ => (NodeGen3.branchWins ks).length

theorem nonempty_node_shape (v : NodeV3) :
    nonemptyFields (nodeRawShape v) = nodeFields (nodeTypeCode v) (NodeGen3.hplenOf v) (nodeChildren v) := by
  cases v with
  | leaf key val mem =>
    by_cases h : 0 < key.length/2 <;>
      simp [nonemptyFields,nodeRawShape,NodeGen3.fieldsOf,F.state,F.len,
        Node.sTAG,Node.sHPL,Node.sHPF,Node.sKEY,Node.sVLEN,Node.sVH,Node.sMEM,
        nodeFields,nodeTypeCode,nodeChildren,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,h] <;> omega
  | ext key kid mem =>
    by_cases h : 0 < key.length/2 <;>
      simp [nonemptyFields,nodeRawShape,NodeGen3.fieldsOf,F.state,F.len,
        Node.sTAG,Node.sHPL,Node.sHPF,Node.sKEY,Node.sCH,Node.sMEM,
        nodeFields,nodeTypeCode,nodeChildren,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf,h] <;> omega
  | branch val kids mem =>
    cases val <;>
      simp only [nodeRawShape,NodeGen3.fieldsOf,List.map_append,List.map_cons,List.map_nil] <;>
      rw [branch_shape] <;>
      simp [nonemptyFields,
        F.state,F.len,Node.sTAG,Node.sVLEN,Node.sVH,Node.sBM,Node.sMEM,
        nodeFields,nodeTypeCode,nodeChildren,NodeGen3.hplenOf,NodeGen3.isLE,NodeGen3.keyOf]

theorem nodeFields_windows (ty hk n : Nat) : nWin (nodeFields ty hk n) = n := by
  simp [nWin,nodeFields]
  split <;> split <;> split <;> simp_all

theorem NodeEncoding.canonical {Q : UpsPartI} (e : NodeEncoding Q) :
    Q.shape = nodeFields Q.ty Q.qhk (nWin Q.shape) := by
  have hs : Q.shape = nodeFields Q.ty Q.qhk (nodeChildren e.node) := by
    rw [e.shape,nonempty_node_shape,e.ty,e.hplen]
  have hn : nWin Q.shape = nodeChildren e.node := by rw [hs,nodeFields_windows]
  rw [hn]; exact hs

theorem fieldsLen_nonempty (sh : List (Nat × Nat)) : fieldsLen (nonemptyFields sh) = fieldsLen sh := by
  induction sh with
  | nil => rfl
  | cons f fs ih =>
    obtain ⟨s,n⟩ := f
    by_cases h : 0<n <;> simp [nonemptyFields,fieldsLen,List.filter_cons,h] at ih ⊢ <;> omega

theorem fieldsLen_layout (fs : List F) (hk : Nat) :
    fieldsLen (fs.map (fun f => (f.state-14,f.len hk))) = (NodeGen.layout fs hk).length := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [fieldsLen,NodeGen.layout] at ih ⊢; omega

theorem NodeEncoding.fieldsOk {Q : UpsPartI} (e : NodeEncoding Q)
    (hn : Q.nochild = if nodeChildren e.node=0 then 1 else 0) : FieldsOk Q := by
  have hw : nWin Q.shape = nodeChildren e.node := by
    rw [e.shape,nonempty_node_shape,nodeFields_windows]
  refine ⟨?_,?_,?_,?_,e.canonical,?_,?_⟩
  · rw [e.ty]; cases e.node with
    | leaf => simp [nodeTypeCode]
    | ext => simp [nodeTypeCode]
    | branch sv => cases sv <;> simp [nodeTypeCode]
  · rw [e.ty,e.hplen]; cases e.node with
    | leaf => simp [nodeTypeCode,NodeGen3.hplenOf,NodeGen3.isLE]
    | ext => simp [nodeTypeCode,NodeGen3.hplenOf,NodeGen3.isLE]
    | branch sv => cases sv <;> simp [nodeTypeCode]
  · rw [e.ty,hw]; cases e.node with
    | leaf => simp [nodeTypeCode,nodeChildren]
    | ext => simp [nodeTypeCode]
    | branch sv => cases sv <;> simp [nodeTypeCode]
  · rw [e.ty,hw]; cases e.node with
    | leaf => simp [nodeTypeCode]
    | ext => simp [nodeTypeCode,nodeChildren]
    | branch sv => cases sv <;> simp [nodeTypeCode]
  · rw [e.bytes,e.shape,fieldsLen_nonempty]
    exact (NodeGen3.ser_len e.wf false).trans (fieldsLen_layout _ _).symm
  · rw [hw]; exact hn

end ZkFormal.NearV3.Render.UpsGen
