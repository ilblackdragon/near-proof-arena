import ZkFormal.Near.Link.Refunds
import ZkFormal.Near.Link.MrkLevels

/-!
# ZkFormal.Near.Link.OutLeaf — the `LEAF(r)` message hashes to the outcome leaf
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem u64_G : u64 Params.G = toBytes G_LEn := by decide
theorem tail5_eq : [2] ++ u32 0 = toBytes [2, 0, 0, 0, 0] := by decide
theorem u32_2_eq : u32 2 = toBytes [2, 0, 0, 0] := by decide
theorem u32_1_eq : u32 1 = toBytes (u32r 1) := by decide
theorem u32_0_eq : u32 0 = toBytes (u32r 0) := by decide

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

theorem refundOf_eq {r : Nat} (hr : r < rs.length) :
    (linkExt vs as rs).refundOf c.1 r = refundG c.1.blockHeight rs[r] := by
  obtain ⟨toks, -, h0, hw, -⟩ := toks_spec h
  have ar := arith_ok h hr (hw r hr)
  obtain ⟨-, -, -, -, -, -, a7, a8, -⟩ := ar
  simp only [Ext.refundOf, surplusOf, burnPrice, rc_eq hr, RcptV.toReceipt, refundG]
  by_cases hhr : rs[r].hr = true
  · rw [if_neg (a7.mp hhr), if_pos hhr, a8 hhr]
  · have : Params.G * (leN' rs[r].gp - min (leN' rs[r].gp) c.1.blockGasPrice) = 0 :=
      Classical.byContradiction fun hc => hhr (a7.mpr hc)
    rw [if_pos this, if_neg hhr]

theorem peo_encode {r : Nat} (hr : r < rs.length) :
    toBytes rs[r].peo = ((linkExt vs as rs).outcomeOf c.1 r).partialEncode := by
  obtain ⟨toks, -, h0, hw, -⟩ := toks_spec h
  obtain ⟨_, _, _, w⟩ := rcpt_wf_at h hr
  obtain ⟨hp, hv, hs⟩ := idLens w
  obtain ⟨-, -, -, -, -, -, -, -, -, l10, -⟩ := w.lens
  have ar := arith_ok h hr (hw r hr)
  have hh := hdr_of c h.rcpt
  simp only [Ext.outcomeOf, Outcome.partialEncode, refundOf_eq h hr, rc_eq hr, burntOf, burnPrice,
    RcptV.toReceipt, refundG]
  rw [← ar.2.2.2.2.2.1, u128, leN_leN' l10, u64_G]
  simp only [RcptV.peo, toBytes_append]
  rw [toBytes_borshN (by omega)]
  by_cases hhr : rs[r].hr = true
  · obtain ⟨-, hrd⟩ := rid_digest h hr hhr
    have hrfid : toBytes rs[r].rfid = receiptIdFrom (toBytes rs[r].rid) c.1.blockHeight 0 := by
      rw [hrd, toBytes_map_toNat, receiptIdFrom, ridMsg, toBytes_append, toBytes_append,
        toBytes_pubBytes (pub_height hh), zeros8_eq]
    simp only [hhr, if_true, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
      gasRefundReceipt, concatAll, List.append_nil]
    rw [← hrfid, u32_1_eq]; simp only [List.append_assoc]; rfl
  · simp only [hhr, Bool.false_eq_true, if_false, List.map_nil, List.length_nil, concatAll,
      List.append_nil, List.nil_append]
    rw [u32_0_eq]; simp only [List.append_assoc]; rfl

theorem leaf_hash {r : Nat} (hr : r < rs.length) :
    Bytes8 rs[r].leaf ∧ sha256 (toBytes rs[r].leaf) = Outcome.leaf ((linkExt vs as rs).outcomeOf c.1 r) := by
  obtain ⟨hrcb, -⟩ := rc_digest h
  have hridb : Bytes8 rs[r].rid := bytes8_of_sub hrcb (fun y hy => by
    simp only [rcMsg, List.mem_append, List.mem_flatMap]; right
    exact ⟨_, List.getElem_mem hr, by simp [RcptV.enc, hy]⟩)
  obtain ⟨-, hpd⟩ := peo_digest h hr
  refine ⟨?_, ?_⟩
  · intro y hy
    simp only [RcptV.leaf, List.mem_append] at hy
    rcases hy with (hy | hy) | hy
    · simp at hy; omega
    · exact hridb y hy
    · rw [hpd] at hy; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hy; exact UInt8.toNat_lt _
  · have hid : ((linkExt vs as rs).outcomeOf c.1 r).id = toBytes rs[r].rid := by
      simp [Ext.outcomeOf, rc_eq hr, RcptV.toReceipt]
    rw [Outcome.leaf, hid]
    simp only [RcptV.leaf, toBytes_append]
    rw [hpd, toBytes_map_toNat, peo_encode h hr, u32_2_eq]

end Hyp

end Link

end ZkFormal.Near
