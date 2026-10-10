import ZkFormal.NearV3.Assembly.NearAir

/-!
# ZkFormal.NearV3.Assembly.NearAirBus — the `busCount` decomposition of `nearAirV3`

`nearTablesFull` is a literal list, so `busCount nearAirV3` decomposes by `rfl`
into the sum of the per-table `tableBusCount`s — the v3 analogue of v1's
`busCount_near` (`Near/Extract/Compose.lean`).  The `RenderV3Stmt` composition
(`docs/zk-formal/STATUS-V3-ASSEMBLY.md` §3.2) uses this to turn the per-table
traffic into the `HoldsP.balance` obligation.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra

/-- `mapIdx` is congruent under pointwise-equal functions. -/
theorem mapIdx_congr {α β : Type} {f g : Nat → α → β} :
    ∀ (l : List α), (∀ i a, f i a = g i a) → List.mapIdx f l = List.mapIdx g l
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.mapIdx_cons]
    rw [mapIdx_congr l (fun i a' => h (i + 1) a'), h 0 a]

/-- The recursive `busCount.go` equals the indexed sum over the table list. -/
theorem busCount_go_eq {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]
    (tr : Trace F) (pub : List F) (b : Nat) (send : Bool) (m : List F) :
    ∀ (l : List ZkFormal.Air.Table) (t : Nat),
      busCount.go tr pub b send m l t =
        (l.mapIdx fun (i : Nat) (T : ZkFormal.Air.Table) => tableBusCount T.interactions tr (t + i) pub b send m).sum := by
  intro l
  induction l with
  | nil => intro t; rfl
  | cons T Ts ih =>
    intro t
    show tableBusCount T.interactions tr t pub b send m +
        busCount.go tr pub b send m Ts (t + 1) = _
    rw [ih (t + 1), List.mapIdx_cons, List.sum_cons]
    have hm : List.mapIdx (fun (i : Nat) (T' : ZkFormal.Air.Table) =>
          tableBusCount T'.interactions tr (t + 1 + i) pub b send m) Ts =
        List.mapIdx (fun (i : Nat) (T' : ZkFormal.Air.Table) =>
          tableBusCount T'.interactions tr (t + (i + 1)) pub b send m) Ts :=
      mapIdx_congr Ts (fun (i : Nat) (T' : ZkFormal.Air.Table) => by congr 1; omega)
    rw [hm, Nat.add_zero]

/-- **`busCount` of `nearAirV3`** is the index-annotated sum of its 25 tables. -/
theorem busCount_nearAirV3 (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) :
    busCount nearAirV3.toAir tr pub b s m =
      (nearTablesFull.mapIdx fun (t : Nat) (T : ZkFormal.Air.Table) =>
        tableBusCount T.interactions tr t pub b s m).sum := by
  rw [busCount]
  simp only [nearAirV3_toAir, nearAirV3Air]
  rw [busCount_go_eq]
  rw [mapIdx_congr nearTablesFull (fun (i : Nat) (T : ZkFormal.Air.Table) => by rw [Nat.zero_add])]

end ZkFormal.NearV3.Assembly
