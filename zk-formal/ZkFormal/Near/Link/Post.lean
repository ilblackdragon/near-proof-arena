import ZkFormal.Near.Link.Trie
import ZkFormal.Near.Link.Run

/-!
# ZkFormal.Near.Link.Post — `post_ok : PostStmt`

After the batch, the value of a touched slot is the `acct` table's post value
(`valsAt_eq`, from the final memory read), whose hash is the post window.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem final_amt {a : AcctV} (ha : a ∈ as) :
    (linkExt vs as rs).amtAt a.k rs.length = leN' a.post := by
  have hl := h.acct.len a ha
  rw [amt_inv h ha _ (Nat.le_refl _)]
  rcases lastW_cases (ksl rs) a.k rs.length with e | ⟨r0, -, -, e⟩
  · rw [e]; simp only [wval, if_true]
    congr 1
    apply ext16 (by simp [hl.1]) hl.2.1
    intro i hi
    have he := (mem_final h ha hi).1 e
    simp only [arMsg, awMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he
    rw [he.2.2.2.1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos hi]
  · rw [e]; simp only [wval, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    obtain ⟨hr0, -, -⟩ := (mem_final h ha (i := 0) (by decide)).2 r0 e
    obtain ⟨_, _, _, w0⟩ := rcpt_wf_at h hr0
    obtain ⟨-, -, -, -, -, -, -, -, l9, -⟩ := w0.lens
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr0, Option.getD_some]
    congr 1
    apply ext16 l9 hl.2.1
    intro i hi
    obtain ⟨_, -, he⟩ := (mem_final h ha hi).2 r0 e
    simp only [arMsg, wrMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he
    exact he.2.2.2.1.symm

theorem valsAt_eq {a : AcctV} (ha : a ∈ as) :
    (linkExt vs as rs).valsAt rs.length a.k = toBytes (a.post ++ a.pre.drop 16) := by
  have hl := h.acct.len a ha
  simp only [Ext.valsAt]
  have hlen : (linkExt vs as rs).rs.length = rs.length := by simp [linkExt]
  rw [acc0_eq h ha, final_amt h ha]
  simp only [accOf, Account.encode, u128, u64]
  rw [leN_leN' hl.2.1, leN_leN' (l := (a.pre.drop 16).take 16) (by simp [hl.1]),
    leN_leN' (l := a.pre.drop 64) (by simp [hl.1])]
  have hsplit : a.pre.drop 16 = (a.pre.drop 16).take 16 ++ ((a.pre.drop 32).take 32 ++ a.pre.drop 64) := by
    have e1 : a.pre.drop 32 = (a.pre.drop 16).drop 16 := by simp [List.drop_drop]
    have e2 : a.pre.drop 64 = ((a.pre.drop 16).drop 16).drop 32 := by simp [List.drop_drop]
    rw [e1, e2, List.take_append_drop, List.take_append_drop]
  conv => rhs; rw [hsplit]
  simp only [toBytes_append, List.append_assoc]

end Hyp

theorem post_ok : PostStmt := by
  intro c vs ws rs as mv ids shaS shaR h
  have hne : 0 < vs.length := List.length_pos_iff.mpr h.node.nonempty
  obtain ⟨-, -, -, hpost⟩ := root_digest h hne
  rw [hpost]
  have hlen : (linkExt vs as rs).rs.length = rs.length := by simp [linkExt]
  rw [hlen]
  unfold trieOf
  show (treeOf (vs.map (·.v.toRec)) ((linkExt vs as rs).valsAt rs.length)
    (vs.map (·.v.toRec)).length 0).hashOf = _
  rw [List.length_map, trie_hash h true _ ?_ _ 0 hne (by omega)]
  intro n hn pre po hw
  have ht : vs[n].v.touched = true := by
    revert hw; cases hv : vs[n].v with
    | leaf k s m => cases s <;> simp [NodeV.vwin, NodeV.touched]
    | ext => simp [NodeV.vwin]
    | branch sv kids m => cases sv with
      | none => simp [NodeV.vwin]
      | some s => cases s <;> simp [NodeV.vwin, NodeV.touched]
  obtain ⟨a, ha, rfl⟩ := touched_acct h hn ht
  obtain ⟨_, pre', po', hw', -, -, -, hd⟩ := acct_digests h ha
  rw [hw] at hw'; simp only [Option.some.injEq, Prod.mk.injEq] at hw'; obtain ⟨rfl, rfl⟩ := hw'
  have hl := h.acct.len a ha
  rw [valsAt_eq h ha, toBytes_length]
  simp only [sel, if_true]; rw [hd, toBytes_map_toNat]
  simp [hl.1, hl.2.1]

end Link

end ZkFormal.Near
