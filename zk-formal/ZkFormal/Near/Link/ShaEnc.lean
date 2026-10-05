import ZkFormal.Near.Link.Slots

/-!
# ZkFormal.Near.Link.ShaEnc — `encOf` by message kind, offsets of the `RC`/`RF` streams
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false

namespace Link

section
variable (pub : List Fp) (vs : List NodeS) (rs : RcptVs) (as : List AcctV) (mv : MrkV)

theorem msgId_mod (k i : Nat) (hk : k < 16) : msgId k i % 16 = k := by unfold msgId; omega
theorem msgId_div (k i : Nat) (hk : k < 16) : msgId k i / 16 = i := by unfold msgId; omega

theorem encOf_rc : encOf pub vs rs as mv K_RC = rcMsg pub rs := by
  simp [encOf, K_RC]

theorem encOf_rf : encOf pub vs rs as mv K_RF = rfMsg pub rs := by
  simp [encOf, K_RC, K_RF]

theorem encOf_peo (r : Nat) : encOf pub vs rs as mv (msgId K_PEO r) = (rs[r]?.map RcptV.peo).getD [] := by
  simp [encOf, msgId_mod, msgId_div, K_RC, K_RF, K_PEO]

theorem encOf_leaf (r : Nat) :
    encOf pub vs rs as mv (msgId K_LEAF r) = (rs[r]?.map RcptV.leaf).getD [] := by
  simp [encOf, msgId_mod, msgId_div, K_RC, K_RF, K_PEO, K_LEAF]

theorem encOf_rid (r : Nat) :
    encOf pub vs rs as mv (msgId K_RID r) = (rs[r]?.map (ridMsg pub)).getD [] := by
  simp [encOf, msgId_mod, msgId_div, K_RC, K_RF, K_PEO, K_LEAF, K_RID]

theorem encOf_mrk (q : Nat) : encOf pub vs rs as mv (msgId K_MRK q) = ((mrkMsgs mv)[q]?).getD [] := by
  simp [encOf, msgId_mod, msgId_div, K_RC, K_RF, K_PEO, K_LEAF, K_RID, K_MRK]

theorem encOf_npre (n : Nat) :
    encOf pub vs rs as mv (msgId K_NPRE n) = (vs[n]?.map fun s => s.v.ser false).getD [] := by
  simp [encOf, msgId_mod, msgId_div, K_RC, K_RF, K_PEO, K_LEAF, K_RID, K_MRK, K_NPRE]

theorem encOf_npost (n : Nat) :
    encOf pub vs rs as mv (msgId K_NPOST n) = (vs[n]?.map fun s => s.v.ser true).getD [] := by
  simp [encOf, msgId_mod, msgId_div, K_RC, K_RF, K_PEO, K_LEAF, K_RID, K_MRK, K_NPRE, K_NPOST]

theorem encOf_vpre (k : Nat) :
    encOf pub vs rs as mv (msgId K_VPRE k) = ((acctOf as k).map (·.pre)).getD [] := by
  simp [encOf, msgId_mod, msgId_div, K_RC, K_RF, K_PEO, K_LEAF, K_RID, K_MRK, K_NPRE, K_NPOST,
    K_VPRE]

theorem encOf_vpost (k : Nat) :
    encOf pub vs rs as mv (msgId K_VPOST k) =
      ((acctOf as k).map fun a => a.post ++ a.pre.drop 16).getD [] := by
  simp [encOf, msgId_mod, msgId_div, K_RC, K_RF, K_PEO, K_LEAF, K_RID, K_MRK, K_NPRE, K_NPOST,
    K_VPRE, K_VPOST]

end

end Link

end ZkFormal.Near
