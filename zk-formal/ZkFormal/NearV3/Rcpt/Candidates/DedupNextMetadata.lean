import ZkFormal.NearV3.Rcpt.Candidates.DedupDuplicateLocal

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupRender
open ZkFormal.Near ZkFormal.Near.Render.EvI ZkFormal.Air Render.SrcpGen

@[simp] theorem leaf_metadata (B : SrcpB) (z p : Nat) (g rep : Bool) :
    localCells B z (.leaf p) g rep = localCells B z (.leaf p) g false := by
  funext x
  simp [localCells]

@[simp] theorem path_metadata (B : SrcpB) (z i o : Nat) (g rep : Bool) :
    localCells B z (.path i o) g rep = localCells B z (.path i o) g false := by
  funext x
  simp [localCells]

private def nextBound : Expr → Nat
  | .col x nx => if nx then x + 1 else 0
  | .add a b | .mul a b => max (nextBound a) (nextBound b)
  | .neg a => nextBound a
  | _ => 0

private theorem ev_next_congr (e : Expr) (C D E : Nat → Int)
    (fst lst trn : Int) (pub : Nat → Int) (W : Nat)
    (h : nextBound e ≤ W) (he : ∀ x, x < W → D x = E x) :
    ev C D fst lst trn pub e = ev C E fst lst trn pub e := by
  induction e with
  | const v => rfl
  | col x nx =>
    cases nx <;> simp_all [nextBound, ev]
    exact he x (by omega)
  | pub i => rfl
  | isFirst => rfl
  | isLast => rfl
  | isTransition => rfl
  | neg a ih => simp only [ev]; rw [ih h]
  | add a b ia ib =>
    simp only [nextBound, Nat.max_le] at h
    simp only [ev]; rw [ia h.1, ib h.2]
  | mul a b ia ib =>
    simp only [nextBound, Nat.max_le] at h
    simp only [ev]; rw [ia h.1, ib h.2]

private theorem frame_gz_low (f : Frame) (a b : Bool) (x : Nat) (hx : x < 55) :
    ({f with gz := a}).cell x = ({f with gz := b}).cell x := by
  simp only [Frame.cell]
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  split <;> simp_all <;> omega

private theorem local_metadata_low (B : SrcpB) (z : Nat) (k : Kind)
    (ga gb ra rb : Bool) (x : Nat) (hx : x < 55) :
    localCells B z k ga ra x = localCells B z k gb rb x := by
  have hn : x ≠ 56 := by omega
  simp only [localCells, hn, ite_false]
  exact frame_gz_low _ _ _ _ hx

set_option maxRecDepth 16384 in
private theorem next_bounds : DedupTable.constraints.all
    (fun ex => decide (nextBound ex ≤ 55)) = true := by decide +kernel

/-- No source polynomial reads successor terminal/repetition metadata. This permits
uniform local transition lemmas to compose at the actual final row. -/
theorem next_metadata (B : SrcpB) (z : Nat) (k : Kind) (g rep : Bool)
    (C : Nat → Int) (fst lst trn : Int) (pub : Nat → Int)
    (ex : Expr) (hex : ex ∈ DedupTable.constraints) :
    ev C (fun x => (localCells B z k g rep x : Int)) fst lst trn pub ex =
      ev C (fun x => (localCells B z k false false x : Int)) fst lst trn pub ex := by
  apply ev_next_congr ex _ _ _ _ _ _ _ 55
  · exact of_decide_eq_true (List.all_eq_true.mp next_bounds ex hex)
  · intro x hx
    rw [local_metadata_low B z k g false rep false x hx]

end ZkFormal.NearV3.Rcpt.Candidates.DedupRender
