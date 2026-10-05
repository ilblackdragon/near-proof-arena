import ZkFormal.Near.Link.EncLemmas

/-!
# ZkFormal.Near.Link.Receipts — `receipts_ok : ReceiptsStmt`

The `RC` message is the claim's receipts-commitment preimage
(`u64 shard ‖ u32 n ‖ Σ Receipt.encode`), and every receipt is in the slice.
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

/-- The `RC` digest. -/
theorem rc_digest : Bytes8 (rcMsg (publicOf c) rs) ∧
    c.1.receiptsCommitment = sha256 (toBytes (rcMsg (publicOf c) rs)) := by
  have hmem : digMsg K_RC (rcOffs rs rs.length) (pubBytes (publicOf c) PV_RC 32) ∈
      nearRecvs (publicOf c) vs ws rs as mv ids B_DIGEST := by
    rw [nearRecvs_digest]; apply List.mem_append_left; apply List.mem_append_right
    unfold rcptRecvs; dsimp only; rw [if_pos rfl]; simp
  have hlen : rcOffs rs rs.length = (encOf (publicOf c) vs rs as mv K_RC).length := by
    rw [encOf_rc, rcOffs_eq rs _ (Nat.le_refl _), List.take_length]
    simp [rcMsg, pubBytes_length]; omega
  obtain ⟨hb, hd⟩ := sha_ok c vs ws rs as mv ids shaS shaR h K_RC _ _ (by unfold K_RC P; omega)
    hlen hmem
  rw [encOf_rc] at hb hd
  rw [pub_rc (hdr_of c h.rcpt)] at hd
  exact ⟨hb, map_toNat_inj hd⟩

theorem toBytes_rcMsg (hb : Bytes8 (rcMsg (publicOf c) rs)) :
    toBytes (rcMsg (publicOf c) rs) =
      u64 c.1.shardId ++ encodeReceipts (rs.map RcptV.toReceipt) := by
  have hh := hdr_of c h.rcpt
  have hn := (claim_ok c vs ws rs as mv ids shaS shaR h).2.2.2.2.2.2
  simp only [linkExt, List.length_map] at hn
  rw [rcMsg, toBytes_append, toBytes_append, toBytes_pubBytes (pub_shard hh),
    toBytes_pubBytes (pub_n hh), encodeReceipts, List.length_map, hn, toBytes_flatMap,
    List.map_map, List.append_assoc]
  congr 3
  apply List.map_congr_left
  intro x hx
  obtain ⟨r, a, b, c', w⟩ := rs_wf h x hx
  refine toBytes_enc w (bytes8_of_sub hb (fun y hy => ?_))
  simp only [rcMsg, List.mem_append, List.mem_flatMap]; right; exact ⟨x, hx, hy⟩

end Hyp

theorem receipts_ok : ReceiptsStmt := by
  intro c vs ws rs as mv ids shaS shaR h
  refine ⟨?_, ?_⟩
  · simp only [linkExt, List.all_eq_true, List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨r, a, b, c', w⟩ := rs_wf h x hx
    exact toReceipt_inSlice w
  · obtain ⟨hb, hd⟩ := rc_digest h
    rw [hd, toBytes_rcMsg h hb]; rfl

end Link

end ZkFormal.Near
