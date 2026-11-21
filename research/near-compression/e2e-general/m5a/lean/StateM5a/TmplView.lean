import StateM5a.TmplMerkle
import StateM5a.Tmpl

/-!
# StateM5a.TmplView — B-T1: the committed working-set root is the extended depth-`D` root

`StateView.wsRoot P es` (the `ws` field of the state commitment `StCommit`, at lane E's depth
`P.depth = 24`) is the depth-`D` root of the circuit's tree (the entries' leaf digests padded with
zero digests to `2^D`, as `WSB`/`WSN` build it) extended to depth 24 with the zero-subtree chain —
the computation `WSX` performs (`Tmpl.Wsx`).  The zero-subtree constants `Tmpl.zeroDig` are
`Merkle.zd nodeH zero48`.
-/

namespace StateM5a.TmplView

open NearSpec StateM5a.Merkle StateM5a.StateView

/-- `Tmpl.zeroDig` is the zero-subtree chain of `nodeH` from the zero leaf. -/
theorem zeroDig_eq : ∀ d : Nat, StateM5a.zeroDig d = zd nodeH zero48 d
  | 0 => rfl
  | d + 1 => by simp only [StateM5a.zeroDig, zd, zeroDig_eq d]

/-- The circuit's `2^D` leaf digests of an entry list (zero-padded). -/
def leavesD (P : StViewParams) (D : Nat) (es : List Entry) : List Bytes :=
  es.map (leafD P) ++ List.replicate (2 ^ D - es.length) zero48

theorem leavesD_length (P : StViewParams) (D : Nat) (es : List Entry) (h : es.length ≤ 2 ^ D) :
    (leavesD P D es).length = 2 ^ D := by
  simp only [leavesD, List.length_append, List.length_map, List.length_replicate]; omega

/-- **The committed working-set root** of `es` (at most `2^D` entries, `D ≤ depth`) is the depth-`D`
root extended by `depth − D` zero-sibling levels. -/
theorem wsRoot_ext (P : StViewParams) (D : Nat) (hD : D ≤ P.depth) (es : List Entry)
    (h : es.length ≤ 2 ^ D) :
    wsRoot P es = ((root nodeH D (leavesD P D es)).map (extUp nodeH zero48 D (P.depth - D))).getD [] := by
  have hp : 2 ^ D ≤ 2 ^ P.depth := Nat.pow_le_pow_right (by omega) hD
  have e : wsLeaves P es = leavesD P D es ++ List.replicate (2 ^ (D + (P.depth - D)) - 2 ^ D) zero48 := by
    simp only [wsLeaves, leavesD, List.append_assoc, List.replicate_append_replicate]
    congr 2
    rw [show D + (P.depth - D) = P.depth by omega]; omega
  have r := root_pad nodeH zero48 D (P.depth - D) _ (leavesD_length P D es h)
  rw [show D + (P.depth - D) = P.depth by omega] at r
  rw [wsRoot, e, show D + (P.depth - D) = P.depth by omega, r]

end StateM5a.TmplView
