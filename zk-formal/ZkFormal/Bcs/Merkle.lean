import ZkFormal.Bcs.Commit

/-!
# ZkFormal.Bcs.Merkle — single-height binary Merkle trees with wide digests

Leaf `v`: `WH(LEAF ‖ v)`; node of height `h+1`: `WH(NODE ‖ u8 (h+1) ‖ left ‖ right)`
(the MMCS node format of `Bcs.Mmcs` with no injected rows).  A tree of height
`h` has `2^h` leaves; position `i` descends by the bits of `i` from bit
`h-1` (at the root) down to bit `0`.

`merkle_binding`: the commitment scheme `merkle` is binding in the sense of
`CommitScheme.Binding` — the extraction lemma for single-height trees.
-/

namespace ZkFormal.Bcs

open ArenaCore ArenaCore.Security ZkFormal

/-- The log certifies an opening of position `i` of a height-`h` tree. -/
def merkleOpenIn (tbl : Table) : Bytes → Nat → Nat → Bytes → Prop
  | root, 0, _, v => WHin tbl (leafMsg v) root
  | root, h + 1, i, v => ∃ l r, l.length = 64 ∧ r.length = 64 ∧ WHin tbl (nodeMsg (h + 1) l r []) root ∧
      (if i / 2 ^ h % 2 = 0 then merkleOpenIn tbl l h (i % 2 ^ h) v
       else merkleOpenIn tbl r h (i % 2 ^ h) v)

/-- Extraction: walk down from the root by inverting recorded wide hashes. -/
noncomputable def merkleExt (hist : Table) : Bytes → Nat → Nat → Option Bytes
  | root, 0, _ =>
    match invert hist root with
    | some (t :: v) => if t = tagLeaf then some v else none
    | _ => none
  | root, h + 1, i =>
    match invert hist root with
    | some (t :: rest) =>
      if t = tagNode then
        merkleExt hist (if i / 2 ^ h % 2 = 0 then (rest.drop 1).take 64 else ((rest.drop 1).drop 64).take 64)
          h (i % 2 ^ h)
      else none
    | _ => none

noncomputable def merkle : CommitScheme where
  Shape := Nat
  Pos := Nat
  OpenIn := merkleOpenIn
  ext := merkleExt

theorem merkleOpenIn_rooted {tbl : Table} :
    ∀ {root : Bytes} {h i : Nat} {v : Bytes}, merkleOpenIn tbl root h i v → ∃ m, WHin tbl m root
  | _, 0, _, _, hop => ⟨_, hop⟩
  | _, _ + 1, _, _, ⟨l, r, _, _, hn, _⟩ => ⟨_, hn⟩

theorem merkle_rooted : merkle.Rooted := fun _ _ _ _ _ h => merkleOpenIn_rooted h

/-- **Extraction lemma, single-height Merkle trees.** -/
theorem merkle_binding_aux {pre hist : Table} (wf : TableWF (pre ++ hist))
    (hcol : ¬ WideCollision 2 whq (pre ++ hist)) (hni : NoInv (pre ++ hist)) :
    ∀ (sh : Nat) (root : Bytes) (pos : Nat) (v : Bytes), merkleOpenIn (pre ++ hist) root sh pos v →
      (∃ m, WHin hist m root) → merkleExt hist root sh pos = some v := by
  intro sh root pos v hop hp
  induction sh generalizing root pos with
  | zero =>
    have hop' : WHin (pre ++ hist) (leafMsg v) root := hop
    rw [merkleExt, invert_eq wf hcol hop' hp]
    simp [leafMsg]
  | succ h ih =>
    obtain ⟨l, r, hl, hr, hn, hc⟩ := hop
    rw [merkleExt, invert_eq wf hcol hn hp]
    simp only [nodeMsg, if_true, List.drop_succ_cons, List.drop_zero, List.append_nil]
    have hnh : WHin hist (nodeMsg (h + 1) l r []) root := by
      obtain ⟨m', hm'⟩ := hp
      have := wh_unique wf hcol (WHin.suffix wf.1 hm') hn
      exact this ▸ hm'
    have hsl := slots_nodeMsg (h + 1) l r [] hl hr 0 (by omega)
    split
    · rename_i hb
      rw [if_pos hb] at hc
      rw [List.take_left' hl]
      obtain ⟨mc, hmc⟩ := merkleOpenIn_rooted hc
      exact ih l (pos % 2 ^ h) hc ⟨mc, used_produced wf hni hnh hsl.1 hmc⟩
    · rename_i hb
      rw [if_neg hb] at hc
      rw [List.drop_left' hl, List.take_of_length_le (Nat.le_of_eq hr)]
      obtain ⟨mc, hmc⟩ := merkleOpenIn_rooted hc
      exact ih r (pos % 2 ^ h) hc ⟨mc, used_produced wf hni hnh hsl.2 hmc⟩

theorem merkle_binding : merkle.Binding :=
  fun _ _ wf hcol hni root sh pos v hop hp => merkle_binding_aux wf hcol hni sh root pos v hop hp

end ZkFormal.Bcs
