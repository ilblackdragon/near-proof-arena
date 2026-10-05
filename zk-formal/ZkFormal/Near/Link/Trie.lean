import ZkFormal.Near.Link.TrieHash

/-!
# ZkFormal.Near.Link.Trie — `trie_ok : TrieStmt`
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem packNibbles_length : ∀ (l : List Nat), (packNibbles l).length = l.length / 2
  | a :: b :: rest => by simp [packNibbles, packNibbles_length rest]; omega
  | [] => rfl
  | [_] => by simp [packNibbles]

theorem key_le_hexPrefix (k : List Nat) (b : Bool) : k.length ≤ 2 * (hexPrefix k b).length := by
  cases k with
  | nil => simp [hexPrefix]
  | cons n rest =>
    unfold hexPrefix
    simp only [List.length_cons]
    split <;> simp_all [packNibbles_length] <;> omega

theorem ser_spec_len (v : NodeV) (hw : v.wf) :
    (ser (zeros 32) (fun _ => zeros 32) v.toRec).length = (v.ser false).length := by
  have hk : ∀ kids : List NKid, (∀ kd ∈ kids, kd.wf) →
      (concatAll ((kids.map NKid.toRec).map (kidBytes fun _ => zeros 32))).length =
        (kids.flatMap (NKid.bytes false)).length := by
    intro kids hkw
    induction kids with
    | nil => rfl
    | cons kd kids ih =>
      have := ih (fun k hk => hkw k (by simp [hk]))
      have hw1 := hkw kd (by simp)
      simp only [List.map_cons, concatAll, List.length_append, List.flatMap_cons, this]
      cases kd <;> simp_all [NKid.toRec, kidBytes, NKid.bytes, NKid.wf, Sound.zeros_length,
        toBytes_length]
  have hs : ∀ s : NSlot, s.wf → (vrefBytes (zeros 32) s.toRec).length = (s.bytes false).length := by
    intro s hsw
    cases s <;> simp_all [NSlot.toRec, vrefBytes, NSlot.bytes, NSlot.wf, u32, leN_length,
      toBytes_length, Sound.zeros_length, u32r]
  cases v with
  | leaf k s m =>
    obtain ⟨-, hsw, hm⟩ := hw
    simp [ser, NodeV.toRec, NodeV.ser, u32, u64, leN_length, hs s hsw, hpN, hm, u32r]; omega
  | ext k kid m =>
    obtain ⟨-, hne, hkw, hm⟩ := hw
    simp only [ser, NodeV.toRec, NodeV.ser, List.length_append, u32, u64, leN_length, hpN,
      List.length_map, hm, u32r, List.length_cons, List.length_nil]
    cases kid <;> simp_all [NKid.toRec, kidBytes, NKid.bytes, NKid.wf, Sound.zeros_length,
      toBytes_length] <;> omega
  | branch sv kids m =>
    obtain ⟨hl, hsv, hkw, hm⟩ := hw
    cases sv with
    | none =>
      simp only [ser, NodeV.toRec, Option.map_none, NodeV.ser, List.length_append, u16, u64,
        leN_length, hm, hk kids hkw, List.length_cons, List.length_nil]
    | some s =>
      simp only [ser, NodeV.toRec, Option.map_some, NodeV.ser, List.length_append, u16, u64,
        leN_length, hm, hk kids hkw, hs s (hsv s rfl), List.length_cons, List.length_nil]
      try omega

theorem touched_toRec (v : NodeV) : v.toRec.touched = v.touched := by
  cases v with
  | leaf k s m => cases s <;> rfl
  | ext => rfl
  | branch sv kids m => cases sv with
    | none => rfl
    | some s => cases s <;> rfl

theorem toRec_wf (v : NodeV) (hw : v.wf) (hb : Bytes8 (v.ser false)) : v.toRec.wf := by
  have hsw : ∀ s : NSlot, s.wf → s.toRec.wf := by
    intro s hs; cases s with
    | ref lenB hh =>
      simp only [NSlot.toRec, VSlot.wf, toBytes_length]
      exact ⟨by have := leN'_lt hs.1; simpa using this, hs.2⟩
    | touched => trivial
  have hkw : ∀ kd : NKid, kd.wf → kd.toRec.wf := by
    intro kd hk; cases kd with
    | none => trivial
    | hash hh => simp only [NKid.toRec, Kid.wf, toBytes_length]; exact hk
    | node => trivial
  have hm : ∀ m : List Nat, m.length = 8 → leN' m < 2 ^ 64 := fun m hm => by
    have := leN'_lt hm; simpa using this
  have hnib : ∀ k : List Nat, (∀ x ∈ k, x < 16) → nibblesOk k = true := by
    intro k hk; simp only [nibblesOk, List.all_eq_true, decide_eq_true_eq]; exact hk
  cases v with
  | leaf k s m =>
    obtain ⟨h1, h2, h3⟩ := hw
    have hL := hpN_len_lt (k := k) (b := true) hb (by simp [NodeV.ser, u32r])
    have := key_le_hexPrefix k true
    exact ⟨hnib k h1, by omega, hsw s h2, hm m h3⟩
  | ext k kid m =>
    obtain ⟨h1, h2, h3, h4⟩ := hw
    have hL := hpN_len_lt (k := k) (b := false) hb (by simp [NodeV.ser, u32r])
    have := key_le_hexPrefix k false
    refine ⟨hnib k h1, by omega, ?_, hkw kid h3, hm m h4⟩
    cases kid with
    | none => exact absurd rfl h2
    | _ => simp [NKid.toRec]
  | branch sv kids m =>
    obtain ⟨h1, h2, h3, h4⟩ := hw
    refine ⟨by simp [h1], fun s hs => ?_, fun kid hk => ?_, hm m h4⟩
    · cases sv with
      | none => cases hs
      | some s' => simp only [Option.map_some, Option.some.injEq] at hs; subst hs; exact hsw s' (h2 s' rfl)
    · obtain ⟨kd, hkd, rfl⟩ := List.mem_map.mp hk; exact hkw kd (h3 kd hkd)

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem node_bytes {n : Nat} (hn : n < vs.length) :
    Bytes8 (vs[n].v.ser false) ∧ Bytes8 (vs[n].v.ser true) := by
  by_cases h0 : n = 0
  · subst h0; obtain ⟨b1, -, b2, -⟩ := root_digest h hn; exact ⟨b1, b2⟩
  · obtain ⟨p, hpc⟩ := has_parent h (Nat.pos_of_ne_zero h0) hn
    obtain ⟨hp, l, r, pre, po, hm⟩ := childOf_iff.mp hpc
    obtain ⟨_, b1, -, b2, -⟩ := child_digest h hp hm
    exact ⟨b1, b2⟩

/-- Touched slots have an acct entry. -/
theorem touched_acct {n : Nat} (hn : n < vs.length) (ht : vs[n].v.touched = true) :
    ∃ a ∈ as, a.k = n := (vslot h).2.2 n hn ht

theorem vals0_eq {a : AcctV} (ha : a ∈ as) : (linkExt vs as rs).vals0 a.k = toBytes a.pre := by
  simp [linkExt, acctOf_eq (vslot h).1 ha]

end Hyp

theorem trie_ok : TrieStmt := by
  intro c vs ws rs as mv ids shaS shaR h
  have hne : 0 < vs.length := List.length_pos_iff.mpr h.node.nonempty
  have hnsget : ∀ k nr, (linkExt vs as rs).ns[k]? = some nr → ∃ hk : k < vs.length, nr = vs[k].v.toRec := by
    intro k nr hk
    simp only [linkExt, List.getElem?_map] at hk
    cases hv : vs[k]? with
    | none => rw [hv] at hk; cases hk
    | some s =>
      rw [hv] at hk; simp only [Option.map_some, Option.some.injEq] at hk
      obtain ⟨hk', he⟩ := List.getElem?_eq_some_iff.mp hv
      exact ⟨hk', by rw [← hk, he]⟩
  -- touched slots ↔ acct entries
  have hacct : ∀ k nr, (linkExt vs as rs).ns[k]? = some nr → nr.touched = true →
      ∃ a ∈ as, a.k = k := by
    intro k nr hk ht
    obtain ⟨hk', rfl⟩ := hnsget k nr hk
    rw [touched_toRec] at ht
    exact touched_acct h hk' ht
  refine ⟨tree_shape h, ?_, ?_, ?_, ?_, ?_⟩
  · intro nr hnr
    simp only [linkExt, List.mem_map] at hnr
    obtain ⟨s, hs, rfl⟩ := hnr
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hs
    exact toRec_wf _ (h.node.wf _ hs) (node_bytes h hn).1
  · intro k nr hk ht
    obtain ⟨a, ha, rfl⟩ := hacct k nr hk ht
    rw [vals0_eq h ha, toBytes_length]; exact (h.acct.len a ha).1
  · intro k nr hk ht
    obtain ⟨a, ha, rfl⟩ := hacct k nr hk ht
    obtain ⟨-, -, -, -, hpre, -⟩ := acct_digests h ha
    rw [vals0_eq h ha, decode_pre (h.acct.len a ha).1 hpre
      (h.acct.notMax a ha (fun i _ => getD_lt_of_bytes8 hpre i))]
    rfl
  · obtain ⟨-, hpre, -, -⟩ := root_digest h hne
    rw [hpre]
    unfold trieOf
    show (treeOf (vs.map (·.v.toRec)) (linkExt vs as rs).vals0 (vs.map (·.v.toRec)).length 0).hashOf = _
    rw [List.length_map, trie_hash h false _ ?_ _ 0 hne (by omega)]
    intro n hn pre po hw
    have ht : vs[n].v.touched = true := by
      revert hw; cases hv : vs[n].v with
      | leaf k s m => cases s <;> simp [NodeV.vwin, NodeV.touched]
      | ext => simp [NodeV.vwin]
      | branch sv kids m => cases sv with
        | none => simp [NodeV.vwin]
        | some s => cases s <;> simp [NodeV.vwin, NodeV.touched]
    obtain ⟨a, ha, rfl⟩ := touched_acct h hn ht
    obtain ⟨_, pre', po', hw', -, hd, -⟩ := acct_digests h ha
    rw [hw] at hw'; simp only [Option.some.injEq, Prod.mk.injEq] at hw'; obtain ⟨rfl, rfl⟩ := hw'
    rw [vals0_eq h ha, toBytes_length, (h.acct.len a ha).1]
    simp only [sel, Bool.false_eq_true, if_false]; rw [hd, toBytes_map_toNat]
  · unfold revealedOf
    simp only [linkExt, List.map_map]
    refine Nat.le_trans (Nat.le_of_eq ?_) h.node.size
    congr 1
    apply List.map_congr_left
    intro s hs
    simp only [Function.comp, nodeSize, touched_toRec]
    rw [ser_spec_len _ (h.node.wf s hs)]

end Link

end ZkFormal.Near
