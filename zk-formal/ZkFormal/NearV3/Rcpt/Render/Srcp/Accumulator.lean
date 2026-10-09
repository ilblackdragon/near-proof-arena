import ZkFormal.NearV3.Rcpt.Render.Srcp.Adjacency

namespace ZkFormal.NearV3.Render.SrcpGen

/-- Natural SIZE accounting commutes with concatenation, without a field-bound premise. -/
theorem size_append (xs ys : List SrcpB) : srcpSize (xs ++ ys) = srcpSize xs + srcpSize ys := by
  simp [srcpSize, List.sum_append]

private theorem take_next {α : Type} (xs : List α) (i : Nat) (hi : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs[i]] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => simp
    | succ i => simpa using congrArg (List.cons a) (ih i (by simpa using hi))

theorem before_zero (bs : List SrcpB) : before bs 0 = 0 := by simp [before, srcpSize]

theorem before_next {bs : List SrcpB} (i : Nat) (hi : i < bs.length) :
    before bs (i + 1) = before bs i + bs[i].L + 33 * bs[i].path.length := by
  simp only [before, take_next bs i hi, size_append]
  simp [srcpSize, Nat.add_assoc]

theorem before_end (bs : List SrcpB) : before bs bs.length = srcpSize bs := by
  simp [before]

/-- The last segment carries the whole list's contribution. -/
theorem last_size (B : SrcpB) (z : Nat) :
    (frame B z (lastKind B)).sz = z + B.L + 33 * B.path.length := by
  by_cases hp : B.path.length = 0
  · simp [lastKind, hp, frame, leafFrame]
  · simp only [lastKind, hp, if_false, frame, pathFrame]
    congr 2
    omega

/-- The next root adds exactly its receipt-list serialization length. -/
theorem next_root_size {bs : List SrcpB} (i : Nat) (hi : i + 1 < bs.length) :
    (rootFrame bs[i + 1] (before bs (i + 1))).sz =
      (frame bs[i] (before bs i) (lastKind bs[i])).sz + bs[i + 1].L := by
  rw [last_size, show (rootFrame bs[i + 1] (before bs (i + 1))).sz =
    before bs (i + 1) + bs[i + 1].L from rfl, before_next i (by omega)]

def chargeKind (B : SrcpB) : Kind → Nat
  | .root => B.L
  | .leaf _ => 0
  | .path _ o => if o = 0 then 33 else 0

/-- Internal successor accounting adds 33 exactly at each path start. -/
theorem internal_size (B : SrcpB) (z : Nat) (a b : Kind)
    (hn : nextKind B a = some b) :
    (frame B z b).sz = (frame B z a).sz + chargeKind B b := by
  cases a with
  | root =>
    simp only [nextKind, Option.some.injEq] at hn
    subst b
    simp [frame, rootFrame, leafFrame, chargeKind]
  | leaf p =>
    simp only [nextKind] at hn
    split at hn
    · cases hn
      simp [frame, leafFrame, chargeKind]
    · split at hn
      · cases hn
        simp [frame, leafFrame, pathFrame, chargeKind]
      · contradiction
  | path i o =>
    simp only [nextKind] at hn
    split at hn
    · cases hn
      simp [frame, pathFrame, chargeKind]
    · split at hn
      · cases hn
        simp [frame, pathFrame, chargeKind, Nat.mul_add, Nat.add_assoc]
      · contradiction

/-- Semantic row charges are precisely the table's gated SIZE increments. -/
theorem charge_gate (B : SrcpB) (z : Nat) (k : Kind) :
    chargeKind B k =
      (frame B z k).rt.toNat * (frame B z k).L +
        33 * ((frame B z k).sf.toNat * (frame B z k).sg.toNat *
          (1 - (frame B z k).lf.toNat)) := by
  cases k with
  | root => simp [chargeKind, frame, rootFrame]
  | leaf p => simp [chargeKind, frame, leafFrame]
  | path i o =>
    by_cases ho : o = 0 <;> simp [chargeKind, frame, pathFrame, ho]

end ZkFormal.NearV3.Render.SrcpGen
