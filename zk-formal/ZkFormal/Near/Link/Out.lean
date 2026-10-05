import ZkFormal.Near.Link.OutBus

/-!
# ZkFormal.Near.Link.Out — `out_ok : OutStmt`

Every `MPOS` send at position `(j, i)` references a message of the right
length whose `sha256` is node `i` of level `j` of `merklize` (`sends_good`, by
induction on `j`); the root reference is the top node (a lower one would be
received twice), whose digest is the claim's outcome root.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

def kindOf (nd : MrkNode) : Bool := match nd with | .hashed .. => true | .promoted .. => false

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem mrk_n : mv.n = rs.length := by
  have hb : ∀ x, x < 4 → pubNat (publicOf c) (PV_N + x) < 256 := fun _ _ => pubNat_lt c _
  obtain ⟨hl, h1, h2⟩ := h.rcpt.count hb
  have hn : nPubNat (publicOf c) = rs.length := by rw [nPubNat_eq _ hb, hl]; rfl
  rw [h.mrk.nfix hb (by rw [hn]; unfold P; omega), hn]

/-- Position facts of mrk node `q`. -/
theorem node_pos {q : Nat} (hq : q < mv.nodes.length) :
    ∃ d, (mrkPos mv q).1 = 1 + d ∧ (mrkPos mv q).2 < sz rs.length (d + 1) ∧
      kindOf mv.nodes[q] = decide (2 * (mrkPos mv q).2 + 1 < sz rs.length d) ∧
      ∀ d', d' < d → sz rs.length (d' + 1) ≠ 1 := by
  obtain ⟨hlen, hkind⟩ := h.mrk.shape
  have hS : q < (mrkShape mv.n).length := by rw [← hlen]; exact hq
  have hmem : (mrkShape mv.n)[q] ∈ mrkShape mv.n := List.getElem_mem hS
  have hget : (mrkShape mv.n).getD q (0, 0, false) = (mrkShape mv.n)[q] := getD_eq_getElem _ _ hS
  have hk := hkind q hq
  rw [hget] at hk
  generalize (mrkShape mv.n)[q] = e at hmem hget hk
  obtain ⟨d, h1, h2, h3, h4⟩ := levels_mem _ _ _ _ _ _ (show (e.1, e.2.1, e.2.2) ∈
    mrkLevels (mv.n + 1) 1 mv.n from hmem)
  rw [mrk_n h] at h2 h3 h4
  have hp : mrkPos mv q = (e.1, e.2.1) := by unfold mrkPos; rw [hget]
  refine ⟨d, by rw [hp]; exact h1, by rw [hp]; exact h2, ?_, h4⟩
  rw [hp]; dsimp only
  rw [← h3, ← hk]
  unfold kindOf; rfl

omit h in
theorem mpos_W_mem {m : Msg} :
    m ∈ nearSends (publicOf c) vs ws rs as mv ids B_MPOS ↔
      (∃ r, r < rs.length ∧ m = [0, r, msgId K_LEAF r, 68]) ∨
      (∃ q, ∃ hq : q < mv.nodes.length, m = mrkSend mv mv.nodes[q] q) := by
  rw [nearSends_mpos, List.mem_append, rcptSends_mpos, mrkSends_mpos]
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro (⟨r, hr, rfl⟩ | ⟨⟨nd, q⟩, hp, rfl⟩)
    · exact .inl ⟨r, hr, rfl⟩
    · obtain ⟨hq, rfl⟩ := mem_zip_range.mp hp; exact .inr ⟨q, hq, rfl⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨q, hq, rfl⟩)
    · exact .inl ⟨r, hr, rfl⟩
    · exact .inr ⟨(mv.nodes[q], q), mem_zip_range.mpr ⟨hq, rfl⟩, rfl⟩

omit h in
theorem kids_R_mem {q : Nat} (hq : q < mv.nodes.length) {m : Msg} (hm : m ∈ mrkKids mv mv.nodes[q] q) :
    m ∈ nearRecvs (publicOf c) vs ws rs as mv ids B_MPOS := by
  rw [nearRecvs_mpos, mrkRecvs_mpos]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨(mv.nodes[q], q), mem_zip_range.mpr ⟨hq, rfl⟩, hm⟩)

theorem mrk_send_canon {q : Nat} (hq : q < mv.nodes.length) : Canon (mrkSend mv mv.nodes[q] q) := by
  have hrl := rs_length_le h
  have hml := mrk_nodes_length h
  have hn1 : 1 ≤ rs.length := (h.rcpt.count (fun _ _ => pubNat_lt c _)).2.1
  obtain ⟨d, h1, h2, -, h4⟩ := node_pos h hq
  have hd := depth_le rs.length hn1 d h4
  have hs := sz_le rs.length (d + 1)
  have hb := hashedBefore_le mv.nodes q
  have hcan := h.mrk.canon.2.2.2 _ (List.getElem_mem hq)
  intro x hx
  unfold mrkSend at hx
  split at hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [h1]; unfold P; omega
    · unfold P; omega
    · unfold msgId K_MRK P; omega
    · unfold P; omega
  · next cId cLen he =>
    rw [he] at hcan
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · rw [h1]; unfold P; omega
    · unfold P; omega
    · exact hcan _ (by simp [MrkNode.raw])
    · exact hcan _ (by simp [MrkNode.raw])

theorem mpos_perm : (nearSends (publicOf c) vs ws rs as mv ids B_MPOS).Perm
    (nearRecvs (publicOf c) vs ws rs as mv ids B_MPOS) := by
  have hrl := rs_length_le h
  apply perm_nat _ _ (perm h (by decide) (by decide))
  · intro m hm
    rcases mpos_W_mem.mp hm with ⟨r, hr, rfl⟩ | ⟨q, hq, rfl⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> (unfold msgId K_LEAF P at *; omega)
    · exact mrk_send_canon h hq
  · intro m hm
    rw [nearRecvs_mpos, mrkRecvs_mpos] at hm
    rcases List.mem_cons.mp hm with rfl | hm
    · obtain ⟨c1, c2, c3, -⟩ := h.mrk.canon
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact c1
      · unfold P; omega
      · exact c2
      · exact c3
    · obtain ⟨⟨nd, q⟩, hp, hm⟩ := List.mem_flatMap.mp hm
      obtain ⟨hq, rfl⟩ := mem_zip_range.mp hp
      have hsc := mrk_send_canon h hq
      have hcan := h.mrk.canon.2.2.2 _ (List.getElem_mem hq)
      have hpos : (mrkPos mv q).1 < P ∧ (mrkPos mv q).2 < P := by
        unfold mrkSend at hsc
        split at hsc <;> exact ⟨hsc _ (by simp), hsc _ (by simp)⟩
      have hml := mrk_nodes_length h
      have hn1 : 1 ≤ rs.length := (h.rcpt.count (fun _ _ => pubNat_lt c _)).2.1
      obtain ⟨d, h1, h2, -, h4⟩ := node_pos h hq
      have hs := sz_le rs.length (d + 1)
      intro x hx
      unfold mrkKids at hm
      split at hm
      · next lI lL l rI rL r he =>
        rw [show mv.nodes[q] = _ from he] at hcan
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;>
          rcases hx with rfl | rfl | rfl | rfl <;>
          first | (unfold P at *; omega) | exact hcan _ (by simp [MrkNode.raw])
      · next cId cLen he =>
        rw [show mv.nodes[q] = _ from he] at hcan
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        subst hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl <;>
          first | (unfold P at *; omega) | exact hcan _ (by simp [MrkNode.raw])

end Hyp

end Link

end ZkFormal.Near
