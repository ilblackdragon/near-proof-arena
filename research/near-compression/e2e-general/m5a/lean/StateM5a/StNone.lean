import StateM5a.TmplView
import StateM5a.StateViewParams

/-!
# StateM5a.StNone — B-T4: the state commitment of `StV.none` (the `stRoot` at `init` / `done`)

`B_0` (`init cb wb`) and the final record (`done H o`) carry `stRoot = stD .none` (lane E's
`ViewE.viewE`; lane G's INIT / FINAL wrappers take it as a constant). For lane B's instance
`stViewParams_B E` the component `.none` has no overlay, so it is in the circuit form
(`fitsB_none'`) with an empty working set; its commitment is the record

    tag 0 ‖ ws = zd nodeH zero48 depth (the empty depth-`depth` tree) ‖ u64 0 ‖ trie = hashOf (.hash 0³²)
          ‖ u64 (idxOf .none) ‖ bdigest (encRestB E (strip .none, none))

(`stD_none_eq`). For lane E's `stViewE` (`join/StViewE.lean`) the value is a 42-byte constant,
evaluated by the kernel in `join-check/StNoneE.lean` (`stD_none_viewE`); `t1/chain.py` uses it at
`c0` / `c10` (`ST_NONE`).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace StateM5a.StNone

open NearSpec NearSpecV3 NearSpecV3.E2E StateM5a.Merkle StateM5a.StateView StateM5a.StateViewParams
open NearSpecV3.E2E.Bnd (StV bdigest)

variable (E : StViewE)

theorem extUp_zero (z : Bytes) : ∀ k, extUp nodeH z 0 k z = zd nodeH z k
  | 0 => rfl
  | k + 1 => by simp only [extUp, extUp_zero z k, zd, Nat.zero_add]

theorem wsOfB_none : wsOfB E StV.none = [] := rfl

theorem trieOfB_none : trieOfB StV.none = .hash zero32 := rfl

theorem fitsB_none' (hi : E.idxOf StV.none < 2 ^ 64) : fitsB E StV.none = true := by
  apply fitsB_of
  · simp [wsOfB_none]
  · simp [wsOfB_none]
  · rw [trieOfB_none]; decide +kernel
  · exact hi
  · rfl

/-- The empty working set's root is the zero-subtree digest at the view's depth. -/
theorem wsRoot_nil : wsRoot (stViewParams_B E) [] = zd nodeH zero48 E.depth := by
  rw [TmplView.wsRoot_ext (stViewParams_B E) 0 (Nat.zero_le _) [] (by simp)]
  show ((root nodeH 0 [zero48]).map (extUp nodeH zero48 0 (E.depth - 0))).getD [] = _
  simp only [root, Option.map_some, Option.getD_some, Nat.sub_zero, extUp_zero]

/-- **The state commitment of `.none`** for lane B's instance. -/
def noneCommit : StCommit where
  tag := 0
  ws := zd nodeH zero48 E.depth
  wsLen := 0
  trie := (PTrie.hash zero32).hashOf
  idx := E.idxOf StV.none
  rest := bdigest (encRestB E (restOfB StV.none))

theorem stD_none_eq (hi : E.idxOf StV.none < 2 ^ 64) :
    stD (stViewParams_B E) StV.none = bdigest (noneCommit E).ser := by
  have hf : (stViewParams_B E).fits StV.none = true := fitsB_none' E hi
  simp only [stD, hf, ↓reduceIte]
  congr 2
  simp only [commitOf, noneCommit, tagOf]
  show StCommit.mk 0 (wsRoot (stViewParams_B E) (wsOfB E StV.none)) (wsOfB E StV.none).length
    (trieOfB StV.none).hashOf (E.idxOf StV.none) (bdigest (encRestB E (restOfB StV.none))) = _
  rw [wsOfB_none, wsRoot_nil]
  rfl

end StateM5a.StNone
