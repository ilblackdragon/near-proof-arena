import ZkFormal.Near.Link.OutLeaf

/-!
# ZkFormal.Near.Link.OutBus — the `MPOS` bus

Sends: receipt leaves `(0, r, LEAF(r), 68)` and mrk nodes at their shape
positions; receives: the root reference and the children of each mrk node.
Both are canonical; sends have distinct positions.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

/-- The send of mrk node `q`. -/
def mrkSend (v : MrkV) (nd : MrkNode) (q : Nat) : Msg := match nd with
  | .hashed .. => [(mrkPos v q).1, (mrkPos v q).2, msgId K_MRK (hashedBefore v.nodes q), 64]
  | .promoted cId cLen => [(mrkPos v q).1, (mrkPos v q).2, cId, cLen]

def mrkKids (v : MrkV) (nd : MrkNode) (q : Nat) : List Msg := match nd with
  | .hashed lI lL _ rI rL _ =>
    [[(mrkPos v q).1 - 1, 2 * (mrkPos v q).2, lI, lL], [(mrkPos v q).1 - 1, 2 * (mrkPos v q).2 + 1, rI, rL]]
  | .promoted cId cLen => [[(mrkPos v q).1 - 1, 2 * (mrkPos v q).2, cId, cLen]]

theorem mrkSends_mpos (pub : List Fp) (v : MrkV) :
    mrkSends pub v B_MPOS = (v.nodes.zip (List.range v.nodes.length)).map fun p => mrkSend v p.1 p.2 := by
  simp only [mrkSends, B_MPOS, B_BYTES]
  simp only [show (9:Nat) ≠ 0 from by decide, if_false, if_true]
  try (apply List.map_congr_left; intro p _; rcases p with ⟨nd, q⟩; cases nd <;> rfl)

theorem mrkRecvs_mpos (pub : List Fp) (v : MrkV) :
    mrkRecvs pub v B_MPOS = [v.J, 0, v.rootId, v.rootLen] ::
      (v.nodes.zip (List.range v.nodes.length)).flatMap fun p => mrkKids v p.1 p.2 := by
  simp only [mrkRecvs, B_MPOS, B_DIGEST]
  simp only [show (9:Nat) ≠ 1 from by decide, if_false, if_true]
  rfl

theorem rcptSends_mpos (pub : List Fp) (rs : RcptVs) :
    rcptSends pub rs B_MPOS = (List.range rs.length).map fun r => [0, r, msgId K_LEAF r, 68] := by
  simp [rcptSends, B_MPOS, B_BYTES, B_KEYNIB, B_MEM, B_RIDS]
  conv => rhs; rw [← map_snd_zip_range rs, List.map_map]
  rfl

theorem sz_pos (n : Nat) (hn : 1 ≤ n) : ∀ j, 1 ≤ sz n j
  | 0 => hn
  | j + 1 => by have := sz_pos n hn j; simp only [sz]; omega

theorem sz_le (n : Nat) : ∀ j, sz n j ≤ n
  | 0 => Nat.le_refl _
  | j + 1 => by have := sz_le n j; simp only [sz]; omega

/-- Levels that exist are at most `n`. -/
theorem depth_le (n : Nat) (hn : 1 ≤ n) : ∀ d, (∀ d', d' < d → sz n (d' + 1) ≠ 1) → sz n d + d ≤ n
  | 0, _ => by simp [sz]
  | d + 1, hd => by
    have ih := depth_le n hn d (fun d' h => hd d' (by omega))
    have h1 := hd d (by omega)
    have := sz_pos n hn (d + 1)
    simp only [sz] at h1 this ⊢
    omega

end Link

end ZkFormal.Near
