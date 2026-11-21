import StateM5a.Merkle

/-!
# StateM5a.TmplMerkle — B-T1: the depth-24 working-set root from the circuit's depth-`D` root

`WSX` (`Tmpl.lean`) extends the depth-`D` root of the circuit's working-set tree to the depth lane
E's state view commits to (`Enc.wsDepth = 24`): `x_{d+1} = H(x_d, Z_d)` for `d = D … 23`, with
the zero-subtree digests `Z_0 = z`, `Z_{d+1} = H(Z_d, Z_d)`.  `root_pad`: for any node hash `H`,
that is exactly the depth-`(D + k)` root of the leaves padded with `z` (the `wsLeaves` of
`StateView`: the entries' digests, then zero digests up to `2^depth`).  No hash assumption is
needed for this direction; `ext_inj` gives the converse under collision resistance (two depth-`D`
roots with the same extension are equal), which is what lets a verifier compare only depth-24
roots at a template boundary.
-/

namespace StateM5a.Merkle

variable {α : Type} (H : α → α → α)

/-- The zero-subtree digests. -/
def zd (z : α) : Nat → α
  | 0 => z
  | d + 1 => H (zd z d) (zd z d)

/-- Extend a depth-`D` root by `k` levels with zero right siblings. -/
def extUp (z : α) (D : Nat) : Nat → α → α
  | 0, x => x
  | k + 1, x => H (extUp z D k x) (zd H z (D + k))

theorem up_replicate (z : α) : ∀ n : Nat, up H (List.replicate (2 * n) z) = List.replicate n (H z z)
  | 0 => by simp [up]
  | n + 1 => by
    have e : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
    rw [e, List.replicate_succ, List.replicate_succ, up, up_replicate z n, List.replicate_succ]

/-- The root of `2^d` copies of `z` is `zd z d`. -/
theorem root_replicate : ∀ (d : Nat) (z : α), root H d (List.replicate (2 ^ d) z) = some (zd H z d)
  | 0, z => by simp [root, zd]
  | d + 1, z => by
    have e : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; omega
    show root H d (up H (List.replicate (2 ^ (d + 1)) z)) = some (zd H z (d + 1))
    rw [e, up_replicate]
    -- `root d (replicate (2^d) (H z z))`, and `zd z (d+1) = zd (H z z) d`
    have h2 : ∀ (d : Nat) (z : α), zd H z (d + 1) = zd H (H z z) d := by
      intro d
      induction d with
      | zero => intro z; rfl
      | succ d ih => intro z; simp only [zd] at ih ⊢; rw [ih z]
    rw [h2, root_replicate d (H z z)]

/-- **The padded root.**  The depth-`(D + k)` root of `l` (`2^D` leaves) followed by zero digests is
the depth-`D` root extended by `k` levels. -/
theorem root_pad (z : α) (D : Nat) : ∀ (k : Nat) (l : List α), l.length = 2 ^ D →
    root H (D + k) (l ++ List.replicate (2 ^ (D + k) - 2 ^ D) z) = (root H D l).map (extUp H z D k)
  | 0, l, hl => by simp [extUp]
  | k + 1, l, hl => by
    have hp : 2 ^ D ≤ 2 ^ (D + k) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [show D + (k + 1) = D + k + 1 by omega]
    have hlen : (l ++ List.replicate (2 ^ (D + k + 1) - 2 ^ D) z).length = 2 ^ (D + k + 1) := by
      simp only [List.length_append, List.length_replicate, hl, Nat.pow_succ]
      have : 2 ^ D ≤ 2 ^ (D + k) * 2 := by omega
      omega
    rw [root_succ_split H (D + k) _ hlen]
    have ht : (l ++ List.replicate (2 ^ (D + k + 1) - 2 ^ D) z).take (2 ^ (D + k)) =
        l ++ List.replicate (2 ^ (D + k) - 2 ^ D) z := by
      rw [List.take_append, hl, List.take_of_length_le (by omega), List.take_replicate]
      congr 2
      rw [Nat.pow_succ]; omega
    have hd : (l ++ List.replicate (2 ^ (D + k + 1) - 2 ^ D) z).drop (2 ^ (D + k)) =
        List.replicate (2 ^ (D + k)) z := by
      rw [List.drop_append, hl, List.drop_of_length_le (by omega), List.nil_append, List.drop_replicate]
      congr 1
      rw [Nat.pow_succ]; omega
    rw [ht, hd, root_pad z D k l hl, root_replicate]
    cases root H D l <;> simp [extUp]

/-- **Collision resistance carries over:** with an injective node hash, the extension is injective. -/
theorem ext_inj (hinj : ∀ a b c d, H a b = H c d → a = c ∧ b = d) (z : α) (D : Nat) :
    ∀ (k : Nat) (x y : α), extUp H z D k x = extUp H z D k y → x = y
  | 0, _, _, h => h
  | k + 1, x, y, h => ext_inj hinj z D k x y (hinj _ _ _ _ h).1

end StateM5a.Merkle
