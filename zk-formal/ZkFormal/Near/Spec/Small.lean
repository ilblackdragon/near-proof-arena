import ZkFormal.Near.Spec.Good

/-!
# ZkFormal.Near.Spec.Small — size side condition of completeness (R-L6e-1)

`Good c e` bounds the revealed bytes (`revealedOf e.ns ≤ 3 MB`) but not the
number of *terminal* nodes: touched slots (the `acct` table holds at most
`maxBatch = 256` of them) and dead branches (no value, no child: `11`
serialized bytes, the only records under `43` bytes, so they are the ones that
can blow up the `sha` table, `~3` rows per revealed byte).

Completeness only needs `Good` of the *pruned* records `extOf c w`, where
every terminal node ends the walk of a receiver key, so there are at most
`|receipts| ≤ maxBatch` of them (`Spec/SmallComplete.lean`: `small_complete`).
`RenderStmt` assumes `Good c e ∧ Small e`; soundness (which produces `Good`)
is unaffected.

The name `Small` and its field `terminals` are stable (used by sub-lanes).
-/

namespace ZkFormal.Near

open NearSpec

/-- A branch with no value and no child (a dead end). -/
def NodeRec.dead : NodeRec → Bool
  | .branch none kids _ => kids.all (· == .none)
  | _ => false

/-- Touched slot or dead branch. -/
def NodeRec.terminal (nr : NodeRec) : Bool := nr.touched || nr.dead

/-- **The size side condition** of completeness. -/
structure Small (e : Ext) : Prop where
  /-- at most `maxBatch` touched slots and dead branches -/
  terminals : (e.ns.filter NodeRec.terminal).length ≤ Params.maxBatch

theorem filter_length_mono {α : Type} {p q : α → Bool} (h : ∀ a, p a = true → q a = true) :
    ∀ l : List α, (l.filter p).length ≤ (l.filter q).length
  | [] => Nat.le_refl _
  | a :: l => by
    have ih := filter_length_mono h l
    by_cases hp : p a = true
    · simp [hp, h a hp]; omega
    · simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]
      split <;> simp <;> omega

/-- At most `maxBatch` touched slots. -/
theorem Small.touched {e : Ext} (h : Small e) :
    (e.ns.filter NodeRec.touched).length ≤ Params.maxBatch :=
  Nat.le_trans (filter_length_mono (fun a ha => by simp [NodeRec.terminal, ha]) _) h.terminals

/-- At most `maxBatch` dead branches. -/
theorem Small.dead {e : Ext} (h : Small e) :
    (e.ns.filter NodeRec.dead).length ≤ Params.maxBatch :=
  Nat.le_trans (filter_length_mono (fun a ha => by simp [NodeRec.terminal, ha]) _) h.terminals

end ZkFormal.Near
