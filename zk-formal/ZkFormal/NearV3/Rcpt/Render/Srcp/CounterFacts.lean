import ZkFormal.NearV3.Rcpt.Render.Srcp.RowWindow

namespace ZkFormal.NearV3.Render.SrcpGen

/-- Counter facts already required by `SrcpWf`, isolated for row arithmetic. -/
structure CounterFacts (B : SrcpB) : Prop where
  qpos : 0 < B.ql
  item_q : ∀ i (hi : i < B.path.length), B.path[i].q = B.ql + 1 + i
  item_pl : ∀ i (hi : i < B.path.length), B.path[i].pl = if i = 0 then 32 else 64
  qe : B.qe = B.lastQ
  le : B.le = if B.path = [] then 32 else 64

theorem counter_facts {bs : List SrcpB} (h : SrcpWf bs) (i : Nat) (hi : i < bs.length) :
    CounterFacts (bs.getD i default) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hm := List.getElem_mem hi
  exact ⟨ql_pos h i hi, fun k hk => (h.items _ hm k hk).1,
    fun k hk => (h.items _ hm k hk).2.2, (h.root _ hm).1, (h.root _ hm).2⟩

theorem terminal_q (B : SrcpB) (h : CounterFacts B) (z : Nat) :
    (frame B z (lastKind B)).q = B.lastQ := by
  by_cases hp : B.path.length = 0
  · simp [lastKind, hp, frame, leafFrame, SrcpB.lastQ]
  · have hi : B.path.length - 1 < B.path.length := by omega
    simp only [lastKind, hp, ite_false, frame, pathFrame]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simp only [Option.getD_some]
    rw [h.item_q _ hi]
    simp only [SrcpB.lastQ]
    omega

theorem terminal_qe (B : SrcpB) (h : CounterFacts B) (z : Nat) :
    (frame B z (lastKind B)).q = (frame B z (lastKind B)).qe := by
  rw [terminal_q B h]
  by_cases hp : B.path.length = 0 <;> simp [lastKind, hp, frame, leafFrame, pathFrame, h.qe]

theorem terminal_length (B : SrcpB) (h : CounterFacts B) (z : Nat) :
    (frame B z (lastKind B)).le = 64 - 32 * (frame B z (lastKind B)).lf.toNat := by
  cases hp : B.path with
  | nil => simp [lastKind, hp, frame, leafFrame, h.le]
  | cons a xs => simp [lastKind, hp, frame, pathFrame, h.le]

end ZkFormal.NearV3.Render.SrcpGen
