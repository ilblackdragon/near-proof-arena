import ZkFormal.Near.Render.Proof.NodeBytes

/-!
# ZkFormal.Near.Render.Proof.NodeWin0 — facts about the hash windows of a node row
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl EvI

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NodeRow
open NodeGen NodeCells NodeTr NodeSeq NodeInfo

/-- The windows of a record's fields: a window that is not looked up has equal pre/post bytes;
a value window is looked up iff the slot is touched; the extension's child window. -/
theorem win_shape (I : Info) (n : Nat) (nr : NodeRec) (w : Win) :
    (F.ch w ∈ fieldsOf I n nr → w.look = false → w.pre = w.post) ∧
    (F.vh w ∈ fieldsOf I n nr → w.look = nr.touched ∧ (w.look = false → w.pre = w.post) ∧ w.slot = none) := by
  have hk : ∀ k ww l sl, (kidWin I k ww l sl).look = false → (kidWin I k ww l sl).pre = (kidWin I k ww l sl).post := by
    intro k ww l sl h; cases k <;> simp_all [kidWin]
  have hv : ∀ v, (valWin I n v).look = false → (valWin I n v).pre = (valWin I n v).post := by
    intro v h; cases v <;> simp_all [valWin]
  constructor
  · intro hf hl
    cases nr with
    | leaf k v m => simp [fieldsOf] at hf
    | ext k kid m =>
      simp [fieldsOf] at hf; subst hf; exact hk _ _ _ _ hl
    | branch v kids m =>
      have : F.ch w ∈ branchWins I kids := by cases v <;> simpa [fieldsOf] using hf
      obtain ⟨k, ww, l, j, _, _, he⟩ := NodeLay.mem_branchWins this
      cases he; exact hk _ _ _ _ hl
  · intro hf
    cases nr with
    | leaf k v m =>
      simp [fieldsOf] at hf; subst hf
      refine ⟨by cases v <;> rfl, hv v, by cases v <;> rfl⟩
    | ext k kid m => simp [fieldsOf] at hf
    | branch v kids m =>
      cases v with
      | none =>
        simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
        rcases hf with h | h | h | h
        · cases h
        · cases h
        · obtain ⟨_, _, _, _, _, _, he⟩ := NodeLay.mem_branchWins (by simpa using h); cases he
        · cases h
      | some sv =>
        simp only [fieldsOf, List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hf
        rcases hf with h | h | h | h | h | h
        · cases h
        · cases h
        · cases h; exact ⟨by cases sv <;> rfl, hv sv, by cases sv <;> rfl⟩
        · cases h
        · obtain ⟨_, _, _, _, _, _, he⟩ := NodeLay.mem_branchWins (by simpa using h); cases he
        · cases h

end NodeRow

end ZkFormal.Near.Render
