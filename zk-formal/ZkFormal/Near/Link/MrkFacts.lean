import ZkFormal.Near.Link.RcptFacts

/-!
# ZkFormal.Near.Link.MrkFacts — `mrk` view: shape size, hashed-node messages
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false

namespace Link

theorem mrkLevels_length : ∀ (f j sp : Nat), (mrkLevels f j sp).length ≤ f * sp
  | 0, _, _ => by simp [mrkLevels]
  | f + 1, j, sp => by
    have ih := mrkLevels_length f (j + 1) ((sp + 1) / 2)
    have hs : (sp + 1) / 2 ≤ sp := by omega
    have : f * ((sp + 1) / 2) ≤ f * sp := Nat.mul_le_mul_left _ hs
    simp only [mrkLevels, List.length_append, List.length_map, List.length_range]
    split <;> simp [Nat.succ_mul] <;> omega

theorem mrkShape_length (n : Nat) (hn : n ≤ 256) : (mrkShape n).length ≤ 257 * 256 := by
  have := mrkLevels_length (n + 1) 1 n
  have : (n + 1) * n ≤ 257 * 256 := Nat.mul_le_mul (by omega) hn
  unfold mrkShape; omega

theorem nPubNat_eq (pub : List Fp) (h : ∀ x, x < 4 → pubNat pub (PV_N + x) < 256) :
    nPubNat pub = leN' (pubBytes pub PV_N 4) := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide)
  have h2 := h 2 (by decide); have h3 := h 3 (by decide)
  have e : ∀ n, n < 256 → (UInt8.ofNat n).toNat = n := fun n hn => by rw [UInt8.toNat_ofNat']; omega
  simp only [nPubNat, leN', pubBytes, List.range, List.range.loop, List.foldr, List.map, leNat]
  simp only [Nat.add_zero] at *
  rw [e _ h0, e _ h1, e _ h2, e _ h3]

def isHashed (nd : MrkNode) : Bool := match nd with | .hashed .. => true | _ => false

def hashedMsg (nd : MrkNode) : Option (List Nat) := match nd with
  | .hashed _ _ l _ _ r => some (l ++ r)
  | _ => none

theorem hashedBefore_eq (nodes : List MrkNode) (q : Nat) :
    hashedBefore nodes q = ((nodes.take q).filter isHashed).length := rfl

theorem length_filterMap_hashed : ∀ (l : List MrkNode),
    (l.filterMap hashedMsg).length = (l.filter isHashed).length
  | [] => rfl
  | nd :: l => by
    have := length_filterMap_hashed l
    cases nd <;> simp [List.filterMap_cons, List.filter_cons, hashedMsg, isHashed, this]

theorem mrkMsgs_eq (mv : MrkV) : mrkMsgs mv = mv.nodes.filterMap hashedMsg := by
  unfold mrkMsgs hashedMsg; rfl

theorem mrkMsgs_at (mv : MrkV) (q : Nat) (hq : q < mv.nodes.length) {lI lL rI rL : Nat}
    {l r : List Nat} (he : mv.nodes[q] = .hashed lI lL l rI rL r) :
    (mrkMsgs mv)[hashedBefore mv.nodes q]? = some (l ++ r) := by
  have e : mv.nodes.filterMap hashedMsg = (mv.nodes.take q).filterMap hashedMsg ++
      (l ++ r) :: (mv.nodes.drop (q + 1)).filterMap hashedMsg := by
    conv => lhs; rw [← List.take_append_drop q mv.nodes]
    rw [List.filterMap_append, List.drop_eq_getElem_cons hq, he]; simp [hashedMsg]
  rw [mrkMsgs_eq, e, hashedBefore_eq, ← length_filterMap_hashed,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem hashedBefore_le (nodes : List MrkNode) (q : Nat) : hashedBefore nodes q ≤ q := by
  rw [hashedBefore_eq]
  exact Nat.le_trans (List.length_filter_le _ _) (by simp; omega)

end Link

end ZkFormal.Near
