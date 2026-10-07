import ZkFormal.NearV3.Assembly.NativeUnfold

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

private theorem slot_read_mem {s : Slot} {b : Bytes}
    (h : s.get.map some = some (some b)) : b ∈ NearSpecV3.slotVal s := by
  cases s with
  | ref => cases h
  | val v => cases h; simp [NearSpecV3.slotVal]

mutual
theorem find_value_occ : ∀ t key b, t.find key = some (some b) →
    ∃ o ∈ NearSpecV3.occs t, b ∈ NearSpecV3.ownVals o
  | .hash _, _, _, h => by cases h
  | .leaf k s m, key, b, h => by
    simp only [PTrie.find] at h
    split at h
    · exact ⟨.leaf k s m,by simp [NearSpecV3.occs],slot_read_mem h⟩
    · cases h
  | .ext k c m, key, b, h => by
    simp only [PTrie.find] at h
    split at h
    · obtain ⟨o,ho,hb⟩ := find_value_occ c _ b h
      exact ⟨o,by simp [NearSpecV3.occs,ho],hb⟩
    · cases h
  | .branch v cs m, [], b, h => by
    cases v with
    | none => cases h
    | some s => exact ⟨.branch (some s) cs m,by simp [NearSpecV3.occs],slot_read_mem h⟩
  | .branch v cs m, n::key, b, h => by
    obtain ⟨o,ho,hb⟩ := kids_find_value_occ cs n key b h
    exact ⟨o,by simp [NearSpecV3.occs,ho],hb⟩
theorem kids_find_value_occ : ∀ cs n key b, Kids.find cs n key = some (some b) →
    ∃ o ∈ NearSpecV3.kOccs cs, b ∈ NearSpecV3.ownVals o
  | .nil, _, _, _, h => by cases h
  | .none _, 0, _, _, h => by cases h
  | .some c cs, 0, key, b, h => by
    obtain ⟨o,ho,hb⟩ := find_value_occ c key b h
    exact ⟨o,List.mem_append.mpr (Or.inl ho),hb⟩
  | .none cs, n+1, key, b, h => kids_find_value_occ cs n key b h
  | .some c cs, n+1, key, b, h => by
    obtain ⟨o,ho,hb⟩ := kids_find_value_occ cs n key b h
    exact ⟨o,List.mem_append.mpr (Or.inr ho),hb⟩
end

theorem find_value_mem {t : PTrie} {key : List Nat} {b : Bytes}
    (h : t.find key = some (some b)) : b ∈ NearSpecV3.valsOf t := by
  obtain ⟨o,ho,hb⟩ := find_value_occ t key b h
  exact List.mem_flatMap.mpr ⟨o,ho,hb⟩

theorem find_value_unfolded {t : PTrie} {key : List Nat} {b : Bytes}
    (h : t.find key = some (some b)) : b.length ≤ NearSpecV3.unfoldedBytesT t := by
  have hm := find_value_mem h
  have hb := Link3.le_sum_mem (List.mem_map.mpr ⟨b,hm,rfl⟩ : b.length ∈ (NearSpecV3.valsOf t).map List.length)
  unfold NearSpecV3.unfoldedBytesT
  omega

theorem preBytes_member {trees : List PTrie} {t : PTrie} (ht : t ∈ trees) :
    NearSpecV3.unfoldedBytesT t ≤ preBytes trees :=
  Link3.le_sum_mem (List.mem_map.mpr ⟨t,ht,rfl⟩)

theorem checkD0a_read_bound {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B cb wb = .ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    {t : PTrie} (ht : t ∈ m.pre :: steps.map ImplicitStepV3.pre)
    {key : List Nat} {b : Bytes} (hb : t.find key = some (some b)) : b.length ≤ B :=
  Nat.le_trans (find_value_unfolded hb)
    (Nat.le_trans (preBytes_member ht) (checkD0a_preBytes hk hw h hm hv))

def preValueBytes (trees : List PTrie) : Nat :=
  (trees.map (fun t => ((NearSpecV3.valsOf t).map List.length).sum)).sum

theorem preValueBytes_le (trees : List PTrie) : preValueBytes trees ≤ preBytes trees := by
  induction trees with
  | nil => exact Nat.le_refl _
  | cons t trees ih =>
    simp only [preValueBytes,preBytes,List.map_cons,List.sum_cons,NearSpecV3.unfoldedBytesT] at *
    omega

theorem checkD0a_preValueBytes {B : Nat} {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B cb wb = .ok ())
    (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    preValueBytes (m.pre :: steps.map ImplicitStepV3.pre) ≤ B :=
  Nat.le_trans (preValueBytes_le _) (checkD0a_preBytes hk hw h hm hv)

end ZkFormal.NearV3.Assembly
