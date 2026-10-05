import ZkFormal.Near.Render.Proof.Base

/-!
# ZkFormal.Near.Render.Proof.AcctFacts — touched slots of a `Good` batch

`AcctOk I`: between 1 and 256 touched slots, each with 72 pre bytes (bytes,
amount not `u128::MAX`) and 72 post bytes.  The upper bound needs
`TouchedLe e` (at most `maxBatch` touched nodes), which `Good` does not state
(see `docs/zk-formal/REQUESTS-L6.md`, R-L6e-1).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near

/-- At most `maxBatch` touched nodes (missing from `Good`, R-L6e-1). -/
def TouchedLe (e : Ext) : Prop := (e.ns.filter NodeRec.touched).length ≤ Params.maxBatch

/-- What the acct table needs about the touched slots. -/
structure AcctOk (I : Info) : Prop where
  len_pos : 1 ≤ I.touched.length
  len_le : I.touched.length ≤ 256
  pre : ∀ k ∈ I.touched, (I.vpre.getD k []).length = 72 ∧ (∀ b ∈ I.vpre.getD k [], b < 256) ∧
    ∃ j, j < 16 ∧ (I.vpre.getD k []).getD j 0 ≠ 255
  post : ∀ k ∈ I.touched, (I.vpost.getD k []).length = 72

section
variable {c : Claim} {e : Ext}

theorem mkInfo_touched : (mkInfo c e).touched =
    (List.range e.ns.length).filter fun k => (e.ns.toArray.getD k (.branch none [] 0)).touched := by
  simp [mkInfo]

theorem mem_touched {k : Nat} : k ∈ (mkInfo c e).touched ↔ ∃ nr, e.ns[k]? = some nr ∧ nr.touched = true := by
  rw [mkInfo_touched, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hk, ht⟩
    refine ⟨e.ns[k], by simp [hk], ?_⟩
    simpa [Array.getD_eq_getD_getElem?, hk] using ht
  · rintro ⟨nr, h, ht⟩
    have hk : k < e.ns.length := by
      rcases Nat.lt_or_ge k e.ns.length with h' | h'
      · exact h'
      · simp [List.getElem?_eq_none h'] at h
    refine ⟨hk, ?_⟩
    rw [List.getElem?_eq_getElem hk] at h
    simp [Array.getD_eq_getD_getElem?, hk, Option.some.inj h, ht]

theorem vpre_eq {k : Nat} (hk : k ∈ (mkInfo c e).touched) :
    (mkInfo c e).vpre.getD k [] = toNats (e.vals0 k) := by
  have hk' := hk
  rw [mkInfo_touched, List.mem_filter, List.mem_range] at hk'
  have ht : e.ns[k].touched = true := by simpa [Array.getD_eq_getD_getElem?, hk'.1] using hk'.2
  simp [mkInfo, Array.getD_eq_getD_getElem?, hk'.1, ht]

theorem vpost_eq {k : Nat} (hk : k ∈ (mkInfo c e).touched) :
    (mkInfo c e).vpost.getD k [] = toNats (e.valsAt e.rs.length k) := by
  have hk' := hk
  rw [mkInfo_touched, List.mem_filter, List.mem_range] at hk'
  have ht : e.ns[k].touched = true := by simpa [Array.getD_eq_getD_getElem?, hk'.1] using hk'.2
  simp [mkInfo, Array.getD_eq_getD_getElem?, hk'.1, ht]

theorem touched_len : (mkInfo c e).touched.length = (e.ns.filter NodeRec.touched).length := by
  rw [mkInfo_touched]
  have hm : (List.range e.ns.length).map (fun k => e.ns.toArray.getD k (.branch none [] 0)) = e.ns := by
    apply List.ext_getElem (by simp)
    intro i h1 h2; simp [Array.getD_eq_getD_getElem?, List.getElem?_eq_getElem h2]
  conv => rhs; rw [← hm]
  rw [List.filter_map, List.length_map]
  rfl

theorem leNat_255 (b : Bytes) (h : b.length = 16) (h255 : ∀ j, j < 16 → (toNats b).getD j 0 = 255) :
    leNat b = Params.u128Max := by
  have : b = List.replicate 16 255 := by
    apply List.ext_getElem (by simp [h])
    intro j h1 _
    have := h255 j (by omega)
    simp only [toNats, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h1,
      Option.map_some, Option.getD_some] at this
    simp only [List.getElem_replicate]
    exact UInt8.toNat_inj.1 this
  rw [this]; decide

theorem touched_some (hg : Good c e) : ∃ k, k ∈ (mkInfo c e).touched := by
  obtain ⟨s, _, hs⟩ := hg.walks 0 (by rw [hg.len]; exact hg.n_pos)
  refine ⟨e.slot 0, mem_touched.2 ?_⟩
  cases hs with
  | endLeaf h => exact ⟨_, h, rfl⟩
  | endBranch h => exact ⟨_, h, rfl⟩
  | child h hj =>
    have hw := hg.nodes_wf _ (List.mem_of_getElem? h)
    simp only [NodeRec.wf] at hw
    have : SYM_END < 16 := by
      rcases Nat.lt_or_ge SYM_END 16 with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none (by omega)] at hj; cases hj
    exact absurd this (by decide)

theorem acctOk (hg : Good c e) (ht : TouchedLe e) : AcctOk (mkInfo c e) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := touched_some hg
    exact List.length_pos_of_mem hk
  · rw [touched_len]; exact ht
  · intro k hk
    obtain ⟨nr, h1, h2⟩ := mem_touched.1 hk
    rw [vpre_eq hk]
    have hl := hg.vals_len k nr h1 h2
    refine ⟨by simp [toNats, hl], fun b hb => ?_, ?_⟩
    · simp only [toNats, List.mem_map] at hb
      obtain ⟨u, _, rfl⟩ := hb; exact u.toNat_lt
    · apply Classical.byContradiction
      intro hne
      have h255 : ∀ j, j < 16 → (toNats (e.vals0 k)).getD j 0 = 255 := fun j hj =>
        Classical.byContradiction fun h => hne ⟨j, hj, h⟩
      have hv := hg.vals_v1 k nr h1 h2
      have hmax : leNat ((e.vals0 k).take 16) = Params.u128Max := by
        apply leNat_255 _ (by simp [hl])
        intro j hj
        rw [← h255 j hj]
        simp [toNats, List.getD_eq_getElem?_getD, List.getElem?_take, hj]
      simp [Account.decode, hl, hmax] at hv
  · intro k hk
    obtain ⟨nr, h1, h2⟩ := mem_touched.1 hk
    rw [vpost_eq hk]
    have hl := hg.vals_len k nr h1 h2
    have hv := hg.vals_v1 k nr h1 h2
    simp only [Ext.valsAt, Ext.acc0, Account.encode, toNats, List.length_map, List.length_append, u128, u64]
    rcases hd : Account.decode (e.vals0 k) with _ | a
    · simp [hd] at hv
    · simp only [Option.getD_some]
      have : a.codeHash.length = 32 := by
        simp only [Account.decode, hl, if_true] at hd
        split at hd
        · simp at hd
        · simp only [Option.some.injEq] at hd; rw [← hd]; simp [hl]
      simp [leN_length, this]

end

end ZkFormal.Near.Render
