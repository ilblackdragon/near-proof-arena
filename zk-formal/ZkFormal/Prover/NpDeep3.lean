import ZkFormal.Prover.NpDeep2

/-!
# ZkFormal.Prover.NpDeep3 — the DEEP batch context of the honest transcript

`myDeep`: the `deep` field of `prep` (`prepCore_deep`); each entry's claimed sums `vz, vg`
are the batched OOD values of its table (`myDeep_vz`).
-/

namespace ZkFormal.Prover.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

/-- The DEEP-context fold step of `prep`. -/
def deepAcc (eqs : List Fp8) (acc : List (TDeep Fp8) × List (Nat × Nat)) (x : TLayout × TOod Fp8) :
    List (TDeep Fp8) × List (Nat × Nat) :=
  match x with
  | (Lt, o) =>
    let off := (acc.2.lookup Lt.lde).getD 0
    let e := eqs.drop off
    let eMz := e.take Lt.width; let e := e.drop Lt.width
    let eMg := e.take Lt.width; let e := e.drop Lt.width
    let eAz := e.take Lt.aux; let e := e.drop Lt.aux
    let eAg := e.take Lt.aux; let e := e.drop Lt.aux
    let eQ := e.take Lt.quot
    let dot (a b : List Fp8) : Fp8 := (a.zip b).foldl (fun s (u, v) => s + u * v) 0
    let td : TDeep Fp8 := ⟨eMz, eMg, eAz, eAg, eQ,
      dot eMz o.mainZ + dot eAz o.auxZ + dot eQ o.quotZ, dot eMg o.mainG + dot eAg o.auxG⟩
    let cnt := 2 * Lt.width + 2 * Lt.aux + Lt.quot
    (acc.1 ++ [td], (Lt.lde, off + cnt) :: acc.2.filter (·.1 != Lt.lde))

theorem prepCore_deep (A : Air) (cb : Bytes) (hdr : List Nat) (αfp γ αc z : Fp8)
    (rest finals ood fp : List Fp8) (oods : List (TOod Fp8)) (r : List Fp8)
    (hs : splitOod (layout A dp hdr) ood = (oods, r)) :
    (prepCore A cb hdr αfp γ αc z rest finals ood fp).deep =
      (((layout A dp hdr).zip oods).foldl (deepAcc (eqTable (rest.take (batchRounds (layout A dp hdr)))))
        ([], [])).1 ∧
    (prepCore A cb hdr αfp γ αc z rest finals ood fp).z = z ∧
    (prepCore A cb hdr αfp γ αc z rest finals ood fp).lay = layout A dp hdr := by
  unfold prepCore
  dsimp only
  rw [hs]
  exact ⟨rfl, rfl, rfl⟩

/-- The claimed sums of a DEEP entry match its table's OOD values. -/
def VZ (o : TOod Fp8) (d : TDeep Fp8) : Prop :=
  d.vz = dotK d.eMz o.mainZ + dotK d.eAz o.auxZ + dotK d.eQ o.quotZ ∧
  d.vg = dotK d.eMg o.mainG + dotK d.eAg o.auxG

theorem deepAcc_vz (eqs : List Fp8) (acc : List (TDeep Fp8) × List (Nat × Nat)) (x : TLayout × TOod Fp8) :
    ∃ d, (deepAcc eqs acc x).1 = acc.1 ++ [d] ∧ VZ x.2 d := by
  obtain ⟨Lt, o⟩ := x
  exact ⟨_, rfl, rfl, rfl⟩

def tdDflt : TDeep Fp8 := ⟨[], [], [], [], [], 0, 0⟩

theorem fold_deep_vz (eqs : List Fp8) : ∀ (l : List (TLayout × TOod Fp8)) (acc : List (TDeep Fp8) × List (Nat × Nat)),
    ∃ ds : List (TDeep Fp8), (l.foldl (deepAcc eqs) acc).1 = acc.1 ++ ds ∧ ds.length = l.length ∧
      ∀ k (hk : k < l.length), VZ l[k].2 (ds.getD k tdDflt)
  | [], acc => ⟨[], by simp, rfl, fun k hk => by simp at hk⟩
  | x :: l, acc => by
    obtain ⟨d, hd, hv⟩ := deepAcc_vz eqs acc x
    obtain ⟨ds, h1, h2, h3⟩ := fold_deep_vz eqs l (deepAcc eqs acc x)
    refine ⟨d :: ds, ?_, by simp [h2], fun k hk => ?_⟩
    · rw [List.foldl_cons, h1, hd]; simp
    · cases k with
      | zero => exact hv
      | succ k => exact h3 k (by simpa using hk)

end ZkFormal.Prover.Np
