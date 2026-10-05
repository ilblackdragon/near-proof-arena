import ZkFormal.Near.Link.Out

/-!
# ZkFormal.Near.Link.OutMain — `out_ok : OutStmt`
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

/-- The outcome leaves. -/
def leavesOf (c : WfClaim) (e : Ext) : List Bytes := (e.outcomes c.1).map Outcome.leaf

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

/-- What an `MPOS` send at `(j, i)` guarantees. -/
def MGood (c : WfClaim) (vs : List NodeS) (rs : RcptVs) (as : List AcctV) (mv : MrkV) (m : Msg) : Prop :=
  ∃ j i Id len, m = [j, i, Id, len] ∧ len = (encOf (publicOf c) vs rs as mv Id).length ∧ Id < P ∧
    Bytes8 (encOf (publicOf c) vs rs as mv Id) ∧ i < sz rs.length j ∧
    sha256 (toBytes (encOf (publicOf c) vs rs as mv Id)) =
      (lvl (leavesOf c (linkExt vs as rs)) j).getD i []

omit h in
theorem leaves_length : (leavesOf c (linkExt vs as rs)).length = rs.length := by
  simp [leavesOf, Ext.outcomes, linkExt]

theorem sends_good : ∀ j, ∀ m ∈ nearSends (publicOf c) vs ws rs as mv ids B_MPOS,
    m.head? = some j → MGood c vs rs as mv m := by
  have hrl := rs_length_le h
  have hn1 : 1 ≤ rs.length := (h.rcpt.count (fun _ _ => pubNat_lt c _)).2.1
  have hLl := leaves_length (c := c) (vs := vs) (as := as) (rs := rs)
  have hperm := mpos_perm h
  intro j
  induction j with
  | zero =>
    intro m hm hj
    rcases mpos_W_mem.mp hm with ⟨r, hr, rfl⟩ | ⟨q, hq, rfl⟩
    · obtain ⟨hb, hs⟩ := leaf_hash h hr
      have e := encOf_leaf (publicOf c) vs rs as mv r
      rw [List.getElem?_eq_getElem hr] at e; simp only [Option.map_some, Option.getD_some] at e
      obtain ⟨_, _, _, w⟩ := rcpt_wf_at h hr
      refine ⟨0, r, _, 68, rfl, by rw [e, leaf_length w], by unfold msgId K_LEAF P; omega,
        by rw [e]; exact hb, hr, ?_⟩
      rw [e, hs]
      simp only [lvl, leavesOf, Ext.outcomes, List.map_map, List.getD_eq_getElem?_getD]
      rw [List.getElem?_map, List.getElem?_range (by simpa [linkExt] using hr)]
      rfl
    · obtain ⟨d, h1, -⟩ := node_pos h hq
      unfold mrkSend at hj; split at hj <;> simp [h1] at hj
  | succ j ih =>
    intro m hm hj
    rcases mpos_W_mem.mp hm with ⟨r, hr, rfl⟩ | ⟨q, hq, rfl⟩
    · simp at hj
    obtain ⟨d, h1, h2, h3, h4⟩ := node_pos h hq
    have hdj : d = j := by unfold mrkSend at hj; split at hj <;> simp [h1] at hj <;> omega
    subst hdj
    have hsc := mrk_send_canon h hq
    have hlj : (lvl (leavesOf c (linkExt vs as rs)) d).length = sz rs.length d := by
      rw [lvl_length, hLl]
    -- the child at (d, k) is good
    have kid_good : ∀ k Id len, [(mrkPos mv q).1 - 1, k, Id, len] ∈ mrkKids mv mv.nodes[q] q →
        MGood c vs rs as mv [d, k, Id, len] := by
      intro k Id len hk
      have hR := kids_R_mem (c := c) (vs := vs) (ws := ws) (rs := rs) (as := as) (ids := ids) hq hk
      have hW := hperm.mem_iff.mpr hR
      rw [h1, show 1 + d - 1 = d from by omega] at hW
      exact ih _ hW rfl
    -- a consumed window of a good child is its hash
    have win : ∀ k Id len (w : List Nat), MGood c vs rs as mv [d, k, Id, len] →
        digMsg Id len w ∈ nearRecvs (publicOf c) vs ws rs as mv ids B_DIGEST →
        Bytes8 w ∧ toBytes w = (lvl (leavesOf c (linkExt vs as rs)) d).getD k [] := by
      intro k Id len w hg hd
      obtain ⟨_, _, _, _, he, e1, e2, -, -, e5⟩ := hg
      simp only [List.cons.injEq, and_true] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨-, hw⟩ := sha_ok c vs ws rs as mv ids shaS shaR h _ _ w e2 e1 hd
      rw [hw, toBytes_map_toNat, e5]
      refine ⟨fun y hy => ?_, rfl⟩
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hy; exact UInt8.toNat_lt _
    have hmd : ∀ m', m' ∈ (match mv.nodes[q] with
        | .hashed lI lL l rI rL r => [digMsg lI lL l, digMsg rI rL r]
        | _ => []) → m' ∈ nearRecvs (publicOf c) vs ws rs as mv ids B_DIGEST := by
      intro m' hm'
      rw [nearRecvs_digest]; apply List.mem_append_right
      unfold mrkRecvs; dsimp only; rw [if_pos rfl]
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨(mv.nodes[q], q), mem_zip_range.mpr ⟨hq, rfl⟩, hm'⟩)
    have hgetL := merkleLevel_get (lvl (leavesOf c (linkExt vs as rs)) d) (mrkPos mv q).2
      (by rw [hlj]; simpa [sz] using h2)
    rw [hlj] at hgetL
    generalize hnd : mv.nodes[q] = nd at h3 hmd kid_good hsc ⊢
    cases nd with
    | hashed lI lL l rI rL r =>
      have hw := h.mrk.windows _ (List.getElem_mem hq)
      rw [hnd] at hw
      have hk1 := kid_good (2 * (mrkPos mv q).2) lI lL (by simp [mrkKids])
      have hk2 := kid_good (2 * (mrkPos mv q).2 + 1) rI rL (by simp [mrkKids])
      obtain ⟨b1, t1⟩ := win _ _ _ l hk1 (hmd _ (by simp))
      obtain ⟨b2, t2⟩ := win _ _ _ r hk2 (hmd _ (by simp))
      have e := encOf_mrk (publicOf c) vs rs as mv (hashedBefore mv.nodes q)
      rw [mrkMsgs_at mv q hq hnd, Option.getD_some] at e
      have hlt : 2 * (mrkPos mv q).2 + 1 < sz rs.length d := by
        simp only [kindOf] at h3; exact of_decide_eq_true h3.symm
      refine ⟨d + 1, (mrkPos mv q).2, _, 64, ?_, by rw [e]; simp [hw.1, hw.2], hsc _ (by simp [mrkSend]),
        by rw [e]; exact bytes8_append.mpr ⟨b1, b2⟩, h2, ?_⟩
      · simp only [mrkSend, h1, Nat.add_comm]
      · rw [e, toBytes_append, t1, t2]
        simp only [lvl]
        rw [hgetL, if_pos hlt]
    | promoted cId cLen =>
      have hk := kid_good (2 * (mrkPos mv q).2) cId cLen (by simp [mrkKids])
      obtain ⟨_, _, _, _, he, e1, e2, e3, -, e5⟩ := hk
      simp only [List.cons.injEq, and_true] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      have hnlt : ¬ (2 * (mrkPos mv q).2 + 1 < sz rs.length d) := by
        simp only [kindOf] at h3; exact of_decide_eq_false h3.symm
      refine ⟨d + 1, (mrkPos mv q).2, cId, cLen, ?_, e1, e2, e3, h2, ?_⟩
      · simp only [mrkSend, h1, Nat.add_comm]
      · rw [e5]; simp only [lvl]; rw [hgetL, if_neg hnlt]

end Hyp

theorem sz_small (n : Nat) : ∀ j, sz n j + j ≤ n ∨ sz n j ≤ 1
  | 0 => .inl (by simp [sz])
  | j + 1 => by
    rcases sz_small n j with h | h <;> simp only [sz] <;> omega

theorem sz_n_n (n : Nat) (hn : 1 ≤ n) : sz n n = 1 := by
  have := sz_pos n hn n; rcases sz_small n n with h | h <;> omega

theorem out_ok : OutStmt := by
  intro c vs ws rs as mv ids shaS shaR h
  have hrl := rs_length_le h
  have hn1 : 1 ≤ rs.length := (h.rcpt.count (fun _ _ => pubNat_lt c _)).2.1
  have hperm := mpos_perm h
  -- the top level
  obtain ⟨Jt, hJ1, hJn, hJ, hmin⟩ := exists_first (sz rs.length) 1 1 rs.length hn1 (sz_n_n _ hn1)
  obtain ⟨b, hb⟩ := levels_complete (rs.length + 1) 1 rs.length (Jt - 1) (by omega)
    (fun d' hd' => hmin (d' + 1) (by omega) (by omega)) 0
    (by rw [show Jt - 1 + 1 = Jt from by omega, hJ]; decide)
  rw [show 1 + (Jt - 1) = Jt from by omega, ← mrk_n h] at hb
  obtain ⟨hlen, -⟩ := h.mrk.shape
  obtain ⟨q, hqS, hqe⟩ := List.mem_iff_getElem.mp (show (Jt, 0, b) ∈ mrkShape mv.n from hb)
  have hq : q < mv.nodes.length := by rw [hlen]; exact hqS
  have hpos : mrkPos mv q = (Jt, 0) := by
    unfold mrkPos; rw [getD_eq_getElem _ _ hqS, hqe]
  -- its send is the root reference
  have hmW : mrkSend mv mv.nodes[q] q ∈ nearSends (publicOf c) vs ws rs as mv ids B_MPOS :=
    mpos_W_mem.mpr (.inr ⟨q, hq, rfl⟩)
  have hmR := hperm.mem_iff.mp hmW
  rw [nearRecvs_mpos, mrkRecvs_mpos] at hmR
  have hroot : mrkSend mv mv.nodes[q] q = [mv.J, 0, mv.rootId, mv.rootLen] := by
    rcases List.mem_cons.mp hmR with he | hk
    · exact he
    · exfalso
      obtain ⟨⟨nd, q'⟩, hp, hk⟩ := List.mem_flatMap.mp hk
      obtain ⟨hq', rfl⟩ := mem_zip_range.mp hp
      obtain ⟨d', e1, -, -, e4⟩ := node_pos h hq'
      have hhead : (mrkSend mv mv.nodes[q] q).head? = some Jt := by
        unfold mrkSend; split <;> simp [hpos]
      have hkh : ∀ k ∈ mrkKids mv mv.nodes[q'] q', k.head? = some ((mrkPos mv q').1 - 1) := by
        intro k hk'
        unfold mrkKids at hk'; split at hk' <;> simp at hk' <;>
          first | (rcases hk' with rfl | rfl <;> rfl) | (subst hk'; rfl)
      have : (mrkPos mv q').1 - 1 = Jt := by
        have := hkh _ hk; rw [hhead] at this; simpa using this.symm
      rw [e1] at this
      exact e4 (Jt - 1) (by omega) (by rw [show Jt - 1 + 1 = Jt from by omega]; exact hJ)
  have hJJ : mv.J = Jt := by
    have e := congrArg List.head? hroot
    have hh : (mrkSend mv mv.nodes[q] q).head? = some Jt := by unfold mrkSend; split <;> simp [hpos]
    rw [hh] at e; simp at e; exact e.symm
  -- the root digest
  obtain ⟨j, i, Id, len, hm, e1, e2, e3, -, e5⟩ := sends_good h Jt _ hmW (by
    unfold mrkSend; split <;> simp [hpos])
  rw [hroot] at hm
  simp only [List.cons.injEq, and_true] at hm
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hm
  have hd : digMsg mv.rootId mv.rootLen ((List.range 32).map fun j => pubNat (publicOf c) (PV_OUT + j)) ∈
      nearRecvs (publicOf c) vs ws rs as mv ids B_DIGEST := by
    rw [nearRecvs_digest]; apply List.mem_append_right
    unfold mrkRecvs; dsimp only; rw [if_pos rfl]; exact List.mem_cons_self
  obtain ⟨-, hw⟩ := sha_ok c vs ws rs as mv ids shaS shaR h _ _ _ e2 e1 hd
  have hpo : (List.range 32).map (fun j => pubNat (publicOf c) (PV_OUT + j)) =
      c.1.outcomeRoot.map UInt8.toNat := pub_out (hdr_of c h.rcpt)
  rw [hpo, e5, hJJ] at hw
  have hroot' := map_toNat_inj hw
  rw [hroot', show outcomeRoot ((linkExt vs as rs).outcomes c.1) =
    merkleRoot (leavesOf c (linkExt vs as rs)) from rfl,
    merkleRoot_eq _ (by rw [leaves_length]; exact hn1) Jt (by rw [leaves_length]; exact hJ)]

end Link

end ZkFormal.Near
