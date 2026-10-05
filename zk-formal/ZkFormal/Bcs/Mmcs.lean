import ZkFormal.Bcs.Statements

/-!
# ZkFormal.Bcs.Mmcs — extraction lemma for mixed-height MMCS

`mmcs_binding_rooted : MmcsStmt`: the mixed-height Merkle multi-commitment
(`Bcs.MmcsDefs`, lane L4's byte format) is binding and rooted in the sense of
`CommitScheme`, so `accept_imp_event_log`/`bcs_romSound` apply to it.
-/

namespace ZkFormal.Bcs

open ArenaCore ArenaCore.Security ZkFormal

theorem mmcsOpen_rooted {tbl : Table} {n : Nat} :
    ∀ {node : Bytes} {k t i : Nat} {v : Bytes}, mmcsOpen tbl n node k t i v → ∃ m, WHin tbl m node
  | _, k, 0, _, _, hop => by
    unfold mmcsOpen at hop
    split at hop
    · exact ⟨_, hop⟩
    · obtain ⟨l, r, _, _, h⟩ := hop; exact ⟨_, h⟩
  | _, _, _ + 1, _, _, ⟨l, r, raw, _, _, hn, _⟩ => ⟨_, hn⟩

theorem mmcs_binding_aux {pre hist : Table} (wf : TableWF (pre ++ hist))
    (hcol : ¬ WideCollision 2 whq (pre ++ hist)) (hni : NoInv (pre ++ hist)) (n : Nat) :
    ∀ (t : Nat) (node : Bytes) (k i : Nat) (v : Bytes), mmcsOpen (pre ++ hist) n node k t i v →
      (∃ m, WHin hist m node) → mmcsExt hist n node k t i = some v := by
  intro t
  induction t with
  | zero =>
    intro node k i v hop hp
    unfold mmcsOpen at hop
    rw [mmcsExt]
    split at hop
    · rename_i hk
      rw [invert_eq wf hcol hop hp]
      simp [leafMsg, hk]
    · rename_i hk
      obtain ⟨l, r, hl, hr, hn⟩ := hop
      rw [invert_eq wf hcol hn hp]
      have e : (l ++ (r ++ v)).drop 128 = v := by
        rw [← List.append_assoc, List.drop_left' (by simp [hl, hr])]
      simp [nodeMsg, hk, e]
  | succ t ih =>
    intro node k i v hop hp
    obtain ⟨l, r, raw, hl, hr, hn, hc⟩ := hop
    rw [mmcsExt, invert_eq wf hcol hn hp]
    have hnh : WHin hist (nodeMsg (n - k) l r raw) node := by
      obtain ⟨m', hm'⟩ := hp
      have := wh_unique wf hcol (WHin.suffix wf.1 hm') hn
      exact this ▸ hm'
    have hsl := slots_nodeMsg (n - k) l r raw hl hr 0 (by omega)
    have e1 : (((n - k).toUInt8 :: (l ++ r ++ raw)).drop 1).take 64 = l := by
      simp only [List.drop_succ_cons, List.drop_zero, List.append_assoc, List.take_left' hl]
    have e2 : (((n - k).toUInt8 :: (l ++ r ++ raw)).drop 65).take 64 = r := by
      rw [show (65 : Nat) = 64 + 1 by rfl, List.drop_succ_cons, List.append_assoc,
        List.drop_left' hl, List.take_left' hr]
    simp only [nodeMsg, if_true, ite_true, e1, e2]
    split
    · rename_i hb
      rw [if_pos hb] at hc
      obtain ⟨mc, hmc⟩ := mmcsOpen_rooted hc
      exact ih l (k + 1) i v hc ⟨mc, used_produced wf hni hnh hsl.1 hmc⟩
    · rename_i hb
      rw [if_neg hb] at hc
      obtain ⟨mc, hmc⟩ := mmcsOpen_rooted hc
      exact ih r (k + 1) i v hc ⟨mc, used_produced wf hni hnh hsl.2 hmc⟩

/-- **Extraction lemma, mixed-height MMCS.** -/
theorem mmcs_binding_rooted : MmcsStmt := show mmcs.Binding ∧ mmcs.Rooted from
  ⟨fun _ _ wf hcol hni root n p v hop hp => mmcs_binding_aux wf hcol hni n p.1 root 0 p.2 v hop hp,
   fun _ _ _ _ _ h => mmcsOpen_rooted h⟩

end ZkFormal.Bcs
