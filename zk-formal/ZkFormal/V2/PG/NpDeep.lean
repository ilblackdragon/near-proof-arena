import ZkFormal.V2.PG.NpBus4

/-!
# ZkFormal.V2.PG.NpDeep (P2 copy of `Prover.NpDeep` at `dp = pg g`) — the batched DEEP value as a function of the domain point

`deepZ c m ξ M Aux Q`: `Stark.deepAt` with the class rows given as extension values
(`deepAt_eq_deepZ`); it only reads the rows of the class tables (`deepZ_congr`).
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

def dotK (e row : List Fp8) : Fp8 := (e.zip row).foldl (fun s (x : Fp8 × Fp8) => s + x.1 * x.2) 0

/-- The DEEP step on one class table. -/
def deepStep (M Aux Q : Nat → List Fp8) (acc : Fp8 × Fp8) (q : (TLayout × TDeep Fp8) × Nat) : Fp8 × Fp8 :=
  (acc.1 + dotK q.1.2.eMz (M q.2) + dotK q.1.2.eAz (Aux q.2) + dotK q.1.2.eQ (Q q.2) - q.1.2.vz,
   acc.2 + dotK q.1.2.eMg (M q.2) + dotK q.1.2.eAg (Aux q.2) - q.1.2.vg)

def classRows (c : Ctx Fp8) (m : Nat) : List ((TLayout × TDeep Fp8) × Nat) :=
  ((c.lay.zip c.deep).zipIdx).filter (·.1.1.lde == m)

/-- `deepAt` with extension-valued class rows. -/
def deepZ (c : Ctx Fp8) (m : Nat) (ξ : Fp8) (M Aux Q : Nat → List Fp8) : Fp8 :=
  match classRows c m with
  | [] => 0
  | ((L0, _), _) :: _ =>
    let r := (classRows c m).foldl (deepStep M Aux Q) (0, 0)
    r.1 / (ξ - c.z) + r.2 / (ξ - Fp8.ofBase (Fp.twoAdicGen L0.log) * c.z)

theorem dotF_eq (e : List Fp8) (row : List Fp) :
    (e.zip row).foldl (fun s (x : Fp8 × Fp) => s + x.1 * StarkField.embed x.2) 0 = dotK e (row.map Fp8.ofBase) := by
  unfold dotK
  generalize (0 : Fp8) = a
  induction e generalizing row a with
  | nil => rfl
  | cons u e ih =>
    cases row with
    | nil => rfl
    | cons v row => simp only [List.zip_cons_cons, List.foldl_cons, List.map_cons]; exact ih row _

theorem foldl_ext {α β : Type} (f g : α → β → α) (h : ∀ a b, f a b = g a b) :
    ∀ (l : List β) (a : α), l.foldl f a = l.foldl g a
  | [], _ => rfl
  | b :: l, a => by rw [List.foldl_cons, List.foldl_cons, h, foldl_ext f g h l]

theorem dotF_ext (f : Fp8 → Fp8 × Fp → Fp8) (hf : ∀ s x, f s x = s + x.1 * Fp8.ofBase x.2)
    (e : List Fp8) (row : List Fp) : (e.zip row).foldl f 0 = dotK e (row.map Fp8.ofBase) := by
  rw [foldl_ext f _ hf]
  have := dotF_eq e row
  exact this

theorem dotK_ext (f : Fp8 → Fp8 × Fp8 → Fp8) (hf : ∀ s x, f s x = s + x.1 * x.2)
    (e row : List Fp8) : (e.zip row).foldl f 0 = dotK e row := by
  rw [foldl_ext f _ hf]; rfl

theorem deepAt_eq_deepZ (c : Ctx Fp8) (op : List (List (List Fp))) (m x : Nat) :
    deepAt (F := Fp) c op m x = deepZ c m (Fp8.ofBase (domPoint (K := Fp8) c.n0 m (x >>> (c.n0 - m))))
      (fun t => ((op.getD 0 []).getD t []).map Fp8.ofBase) (fun t => ksOfRow (F := Fp) ((op.getD 1 []).getD t []))
      (fun t => ksOfRow (F := Fp) ((op.getD 2 []).getD t [])) := by
  unfold deepAt deepZ
  simp only [classRows]
  generalize List.filter (fun x => x.fst.fst.lde == m) (c.lay.zip c.deep).zipIdx = rows
  cases rows with
  | nil => rfl
  | cons q rest =>
    obtain ⟨⟨L0, d0⟩, t0⟩ := q
    dsimp only
    rw [foldl_ext _ (deepStep (fun t => ((op.getD 0 []).getD t []).map Fp8.ofBase)
      (fun t => ksOfRow (F := Fp) ((op.getD 1 []).getD t []))
      (fun t => ksOfRow (F := Fp) ((op.getD 2 []).getD t []))) ?h]
    case h =>
      intro a q
      obtain ⟨⟨L, d⟩, t⟩ := q
      simp only [deepStep]
      rw [dotF_eq, dotF_eq]
      rfl
    generalize List.foldl (deepStep (fun t => ((op.getD 0 []).getD t []).map Fp8.ofBase)
      (fun t => ksOfRow (F := Fp) ((op.getD 1 []).getD t []))
      (fun t => ksOfRow (F := Fp) ((op.getD 2 []).getD t []))) ((0 : Fp8), (0 : Fp8))
      (((L0, d0), t0) :: rest) = r
    obtain ⟨r1, r2⟩ := r
    rfl

end ZkFormal.Prover.Np.G
