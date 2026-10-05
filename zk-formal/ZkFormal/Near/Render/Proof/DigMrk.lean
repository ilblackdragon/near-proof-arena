import ZkFormal.Near.Render.Proof.DigNode
import ZkFormal.Near.Render.Proof.BusMpos
import ZkFormal.Near.Render.Proof.RcptD
import ZkFormal.Near.Link.MrkLevels

/-!
# ZkFormal.Near.Render.Proof.DigMrk — the merkle levels are `merklize`

The digests of the generator's merkle levels (`MrkGen.levels`) are those of
nearcore's `merklize` over the outcome leaves (`levels_dig_eq`): level 0 holds
`sha256 (LEAF r)` = `Outcome.leaf` of receipt `r`, a hashed node the digest of
its children, a promoted node its child.  Hence the top node's digest is the
claim's `outcomeRoot` (`root_dig`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

namespace BusDigest
open MrkGen

theorem size_sz (n : Nat) : ∀ j, size n j = Link.sz n j
  | 0 => rfl
  | j + 1 => by simp only [size, Link.sz, size_sz n j]

theorem ofNats_append (a b : List Nat) : ofNats (a ++ b) = ofNats a ++ ofNats b := by
  simp [ofNats]

theorem shaN_toNats (a b : Bytes) : shaN (toNats a ++ toNats b) = toNats (sha256 (a ++ b)) := by
  rw [shaN, ofNats_append, NodeInfo.ofNats_toNats, NodeInfo.ofNats_toNats]

/-- The merkle leaves of the claim. -/
def leavesL (c : Claim) (e : Ext) : List Bytes := (e.outcomes c).map Outcome.leaf

theorem leavesL_len (c : Claim) (e : Ext) : (leavesL c e).length = (mkInfo c e).nRcpt := by
  simp [leavesL, Ext.outcomes, Info.nRcpt, mkInfo_e]

theorem leaf_dig (c : Claim) (e : Ext) (r : Nat) :
    shaN (leafBytes (mkInfo c e) r) = toNats (Outcome.leaf (e.outcomeOf c r)) := by
  simp only [leafBytes, peoBytes, mkInfo_e, mkInfo_c, leBytes, Outcome.leaf]
  rw [shaN, ofNats_append, ofNats_append, NodeInfo.ofNats_toNats, NodeInfo.ofNats_toNats,
    show shaN (toNats (e.outcomeOf c r).partialEncode) = toNats (sha256 (e.outcomeOf c r).partialEncode) by
      rw [shaN, NodeInfo.ofNats_toNats]]
  rw [NodeInfo.ofNats_toNats]
  rfl

theorem levels_dig_eq (c : Claim) (e : Ext) : ∀ j i, i < size (mkInfo c e).nRcpt j →
    ((levels (mkInfo c e) j).getD i default).dig = toNats ((Link.lvl (leavesL c e) j).getD i [])
  | 0, i, hi => by
    simp only [size] at hi
    simp only [levels, Link.lvl, leavesL, Ext.outcomes]
    simp only [Info.nRcpt, mkInfo_e] at hi ⊢
    simp [List.getD_eq_getElem?_getD, hi, leaf_dig]
  | j + 1, i, hi => by
    rw [BusMpos.levels_succ_getD _ j i hi]
    have hl : (Link.lvl (leavesL c e) j).length = size (mkInfo c e).nRcpt j := by
      rw [Link.lvl_length, leavesL_len, size_sz]
    have hi' : i < ((Link.lvl (leavesL c e) j).length + 1) / 2 := by rw [hl]; exact hi
    rw [Link.lvl, Link.merkleLevel_get _ i hi', hl]
    split
    · rename_i h
      simp only
      rw [levels_dig_eq c e j (2 * i) (by omega), levels_dig_eq c e j (2 * i + 1) h, shaN_toNats]
    · exact levels_dig_eq c e j (2 * i) (by simp only [size] at hi; omega)

theorem size_topJ {n : Nat} (hn : 1 ≤ n) : size n (topJ n) = 1 := by
  obtain ⟨_, _, _, r, _, h1, _, _, h2⟩ := recs_facts n hn
  rw [← h2]; exact h1

/-- **The top merkle node's digest is the claim's outcome root.** -/
theorem root_dig {c : Claim} {e : Ext} (hg : Good c e) :
    ((levels (mkInfo c e) (topJ (mkInfo c e).nRcpt)).getD 0 default).dig = toNats c.outcomeRoot := by
  have hn : 1 ≤ (mkInfo c e).nRcpt := by
    show 1 ≤ e.rs.length; rw [hg.len]; exact hg.n_pos
  have hs := size_topJ hn
  rw [levels_dig_eq c e _ 0 (by omega), ← hg.outRoot, outcomeRoot,
    show (e.outcomes c).map Outcome.leaf = leavesL c e from rfl,
    Link.merkleRoot_eq _ (by rw [leavesL_len]; exact hn) (topJ (mkInfo c e).nRcpt)
      (by rw [leavesL_len, ← size_sz]; exact hs)]

end BusDigest

end ZkFormal.Near.Render
