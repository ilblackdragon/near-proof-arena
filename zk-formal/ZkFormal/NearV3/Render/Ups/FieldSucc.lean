import ZkFormal.NearV3.Render.Ups.FieldWindows

/-! Semantic field-kind succession, separately from AIR evaluation. -/
namespace ZkFormal.NearV3.Render.UpsGen

/-- Adjacent entries in a serialized field sequence satisfy a relation. -/
def FieldChain (rel : (Nat × Nat) → (Nat × Nat) → Prop) : List (Nat × Nat) → Prop
  | a :: b :: rest => rel a b ∧ FieldChain rel (b :: rest)
  | _ => True

/-- The cursor crossing a field boundary follows the sequence's adjacency relation. -/
theorem fieldAt_boundary_chain (rel : (Nat × Nat) → (Nat × Nat) → Prop)
    (sh : List (Nat × Nat)) (positive : ∀ f ∈ sh, 0 < f.2) (chain : FieldChain rel sh)
    (p : Nat) (hp : p + 1 < fieldsLen sh)
    (he : (fieldAt sh p).2.1 + 1 = (fieldAt sh p).2.2.1) :
    rel ((fieldAt sh p).1,(fieldAt sh p).2.2.1)
      ((fieldAt sh (p + 1)).1,(fieldAt sh (p + 1)).2.2.1) := by
  induction sh generalizing p with
  | nil => simp at hp
  | cons a sh ih =>
    obtain ⟨s,l⟩ := a
    by_cases h : p < l
    · simp only [fieldAt,h,ite_true] at he ⊢
      cases sh with
      | nil => simp only [fieldsLen_cons,fieldsLen_nil] at hp; omega
      | cons b rest =>
        obtain ⟨t,m⟩ := b
        have hm : 0 < m := positive (t,m) (by simp)
        simp only [he,Nat.lt_irrefl,ite_false,Nat.sub_self,fieldAt,hm,ite_true]
        exact chain.1
    · have hn : ¬ p + 1 < l := by omega
      simp only [fieldAt,h,hn,ite_false] at he ⊢
      rw [show p + 1 - l = (p-l)+1 by omega]
      apply ih (fun f hf => positive f (by simp [hf]))
      · cases sh with
        | nil => trivial
        | cons b rest => exact chain.2
      · simp only [fieldsLen_cons] at hp; omega
      · exact he

/-- Successor states specified by the node serialization grammar. -/
def nextFieldStates (ty hk children s : Nat) : List Nat :=
  if s = 0 then [if ty ≤ 1 then 1 else if ty = 3 then 4 else 6]
  else if s = 1 then [2]
  else if s = 2 then [if 1 < hk then 3 else if ty = 0 then 4 else 7]
  else if s = 3 then [if ty = 0 then 4 else 7]
  else if s = 4 then [5]
  else if s = 5 then [if ty = 0 then 8 else 6]
  else if s = 6 then [if children = 0 then 8 else 7]
  else if s = 7 then [7,8]
  else []

/-- Child windows may continue or end in the memory field. -/
theorem windows_chain (ty hk children n : Nat) :
    FieldChain (fun a b => b.1 ∈ nextFieldStates ty hk children a.1)
      (List.replicate n (7,32) ++ [(8,8)]) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    cases n with
    | zero => simp [List.replicate_succ,FieldChain,nextFieldStates]
    | succ n =>
      simpa only [List.replicate_succ,List.cons_append,FieldChain,nextFieldStates,
        Nat.reduceEqDiff,ite_false,ite_true,List.mem_cons,List.not_mem_nil,or_false,
        true_or,true_and] using ih

/-- Canonical node fields follow the serialization grammar. -/
theorem nodeFields_chain (ty hk children : Nat) (ht : ty < 4)
    (h0 : ty = 0 → children = 0) (h1 : ty = 1 → children = 1) :
    FieldChain (fun a b => b.1 ∈ nextFieldStates ty hk children a.1)
      (nodeFields ty hk children) := by
  rcases (show ty = 0 ∨ ty = 1 ∨ ty = 2 ∨ ty = 3 by omega) with rfl | rfl | rfl | rfl
  · have hc := h0 rfl; subst children
    by_cases hh : 1 < hk <;> simp [nodeFields,FieldChain,nextFieldStates,hh]
  · have hc := h1 rfl; subst children
    by_cases hh : 1 < hk <;> simp [nodeFields,FieldChain,nextFieldStates,hh,List.replicate_succ]
  · cases children with
    | zero => simp [nodeFields,FieldChain,nextFieldStates]
    | succ n =>
      simpa [nodeFields,FieldChain,nextFieldStates,List.replicate_succ] using windows_chain 2 hk (n+1) (n+1)
  · cases children with
    | zero => simp [nodeFields,FieldChain,nextFieldStates]
    | succ n =>
      simpa [nodeFields,FieldChain,nextFieldStates,List.replicate_succ] using windows_chain 3 hk (n+1) (n+1)

/-- Prefix, value and bitmap fields occur only in node types that serialize them. -/
theorem nodeFields_types {ty hk children s l : Nat}
    (h : (s,l) ∈ nodeFields ty hk children) :
    (s = 1 ∨ s = 2 ∨ s = 3 → ty ≤ 1) ∧
    (s = 3 → 1 < hk) ∧ (s = 4 ∨ s = 5 → ty = 0 ∨ ty = 3) ∧
    (s = 6 → 2 ≤ ty) := by
  simp only [nodeFields,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_replicate] at h
  rcases h with ((((h | h) | h) | h) | h) | h
  · cases h; omega
  · split at h
    · simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with (h | h) | h
      · cases h; omega
      · cases h; omega
      · split at h
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
          cases h; omega
        · cases h
    · cases h
  · split at h
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with h | h <;> cases h <;> omega
    · cases h
  · split at h
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      cases h; omega
    · cases h
  · rcases h with ⟨_, h⟩; cases h; omega
  · cases h; omega

/-- The state at the next field boundary is a grammar successor of the current state. -/
theorem FieldsOk.successor {Q : UpsPartI} (ok : FieldsOk Q) {p : Nat}
    (hp : p + 1 < Q.q.length)
    (he : (fieldAt Q.shape p).2.1 + 1 = (fieldAt Q.shape p).2.2.1) :
    (fieldAt Q.shape (p+1)).1 ∈ nextFieldStates Q.ty Q.qhk (nWin Q.shape) (fieldAt Q.shape p).1 := by
  apply fieldAt_boundary_chain (fun a b => b.1 ∈ nextFieldStates Q.ty Q.qhk (nWin Q.shape) a.1)
    Q.shape _ _ p (by rw [← ok.bytes]; exact hp) he
  · intro f hf
    have hn : f ∈ nodeFields Q.ty Q.qhk (nWin Q.shape) := by rw [← ok.shape]; exact hf
    exact (nodeFields_mem hn).2
  · have hn := nodeFields_chain Q.ty Q.qhk (nWin Q.shape) ok.ty ok.leaf ok.extension
    rw [← ok.shape] at hn
    exact hn

end ZkFormal.NearV3.Render.UpsGen
