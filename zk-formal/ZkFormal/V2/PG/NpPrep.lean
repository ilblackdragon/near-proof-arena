import ZkFormal.V2.PG.NpHon

/-!
# ZkFormal.V2.PG.NpPrep (P2 copy of `Prover.NpPrep` at `dp = pg g`) — the verifier's context on a transcript of the expected shape
-/

namespace ZkFormal.Prover.Np.G

variable [AuxG]

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

section
variable (A : Air)

/-- `prep` on a transcript with header `hdr`, challenges `αfp :: γ :: αc :: z :: rest` and
clear-text parts `[finals, ood, fp]`. -/
def prepCore (cb : Bytes) (hdr : List Nat) (αfp γ αc z : Fp8) (rest finals ood fp : List Fp8) :
    Ctx Fp8 :=
  let prm := dp
  let lay := layout A prm hdr
  let pub : List Fp := cb.map fun b => ofNatF b.toNat
  let L := batchRounds lay
  let rs := rest.take L
  let fri := rest.drop L
  let kinds := friChalKinds A prm hdr
  let betas := ((kinds.zip fri).filter (! ·.1.1)).map (·.2)
  let gammas := ((kinds.zip fri).filter (·.1.1)).map fun (k, c) => (k.2, c)
  let (oods, _) := splitOod lay ood
  let eqs := eqTable rs
  let deep := ((lay.zip oods).foldl (fun (acc : List (TDeep Fp8) × List (Nat × Nat)) (Lt, o) =>
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
    (acc.1 ++ [td], (Lt.lde, off + cnt) :: acc.2.filter (·.1 != Lt.lde))) ([], [])).1
  let okLens := decide (rest.length = L + kinds.length) && decide (fp.length = 2) &&
    decide (finals.length = (lay.map fun L => L.sendG + L.recvG).sum) &&
    decide (ood.length = (lay.map fun L => 2 * L.width + 2 * L.aux + L.quot).sum)
  { ok := okLens, hdr, lay, n0 := queryLog A prm hdr, ℓ := finalLayer A prm hdr, z
    ood := oods, deep, commits := friCommits A prm hdr, betas, gammas, finalPoly := fp
    globalOk := okLens && globalChecks (F := Fp) A prm pub lay oods finals αfp γ αc z }

theorem prep_eq (τ : PT Fp8 Unit) {hdr : List Nat} {αfp γ αc z : Fp8} {rest finals ood fp : List Fp8}
    (h1 : τ.header? = some hdr) (h2 : τ.chals = αfp :: γ :: αc :: z :: rest)
    (h3 : τ.elems = [finals, ood, fp]) :
    prep (F := Fp) A dp τ = prepCore A τ.cb hdr αfp γ αc z rest finals ood fp := by
  unfold prep
  rw [h1]
  simp only
  rw [h2, h3]
  rfl

end

end ZkFormal.Prover.Np.G
