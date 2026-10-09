import ZkFormal.NearV3.Render.Ups.Ok

/-! Semantic part-plan conditions recovered from helper commit 1d8b2f12.
These remain separate obligations on the constructed parts; the already-proved
UpsOk groups are not silently strengthened. -/
namespace ZkFormal.NearV3.Render.UpsGen

/-- The part plan and the part header of part `k` (`Q_{k+1}`), bottom-up (UPSV3-DESIGN §3.2,
§3.3): kinds by `termPlan` for the terminal parts and `RDB`/`RDE`/`PT` above them; depth,
descend counter and source level; the node type and the hex-prefix facts each kind fixes; the
`MEMD` child. -/
structure PartOk (I : UpsInst) (k : Nat) (Q : UpsPartI) : Prop where
  kind : Q.kind < 12
  kindT : k < UpsRows.nTof I.ci I.ti →
    Q.kind = ((UpsRows.termPlan (UpsRows.UCase.all.getD I.ci .LP) I.ti).getD k .RLP).ix
  kindU : UpsRows.nTof I.ci I.ti ≤ k → Q.kind = 0 ∨ Q.kind = 1 ∨ Q.kind = 11
  /-- terminal parts: depth `dep_D`, descend counter `D`; upper parts: one level up per part -/
  pdepT : k < UpsRows.nTof I.ci I.ti → Q.pdep = I.dep.getD I.D 0
  pdepU : UpsRows.nTof I.ci I.ti ≤ k → Q.pdep + (k + 1 - UpsRows.nTof I.ci I.ti) = I.dep.getD I.D 0
  rcT : k < UpsRows.nTof I.ci I.ti → Q.rc = I.D
  /-- the source level: `rc − 1` for a descend, `D` otherwise (pass-through: chained by `cid`) -/
  sd : Q.sd < 3
  sdRD : Q.kind = 0 ∨ Q.kind = 1 → Q.sd + 1 = Q.rc
  sdT : 2 ≤ Q.kind → Q.kind ≠ 11 → Q.sd = I.D
  sN : Q.kind ≠ 11 → Q.sN = I.N.getD Q.sd 0
  pdepS : Q.kind ≠ 11 → Q.pdep = I.dep.getD Q.sd 0
  /-- the node type of `Q` by kind -/
  ty : Q.ty < 4
  tyBr : Q.kind = 0 ∨ Q.kind = 3 ∨ Q.kind = 5 ∨ Q.kind = 10 → 2 ≤ Q.ty
  tyBV : Q.kind = 3 ∨ Q.kind = 4 → Q.ty = 3
  tyExt : Q.kind = 1 ∨ Q.kind = 7 ∨ Q.kind = 9 ∨ Q.kind = 11 → Q.ty = 1
  tyLeaf : Q.kind = 2 ∨ Q.kind = 6 ∨ Q.kind = 8 → Q.ty = 0
  tySpb : Q.kind = 10 → (Q.ty = 3 ↔ I.ci = 4 ∨ I.ci = 5 ∨ I.ci = 7 ∨ I.ci = 8)
  /-- hex-prefix facts: pass-through `[]`, new leaf `[15]`/`[]`, wrapping extension, moved key -/
  pt : Q.kind = 11 → Q.qhk = 1 ∧ Q.qodd = 0
  spbKids : Q.kind = 10 → Q.nochild = 0
  nlf : Q.kind = 8 → Q.qhk = 1 ∧ Q.qodd = (if I.ts = 1 then 1 else 0)
  wex : Q.kind = 9 → Q.qhk = 1 + (if I.ts = 3 ∧ I.ti = 2 then 1 else 0) ∧ Q.qodd = (if I.ti = 1 then 1 else 0)
  mv : Q.kind = 6 ∨ Q.kind = 7 → 2 * Q.qhk + Q.qodd + I.ti + 1 = 2 * Q.phk + Q.podd
  mveOdd : Q.kind = 7 → Q.ty ≤ 1 → Q.qhk = 1 → Q.qodd = 1
  xcp : Q.kind = 10 → (I.ci = 8 ∨ I.ci = 10) → 2 * Q.phk + Q.podd = I.ti + 3
  /-- the `MEMD` child: the part below, or the moved node (`jm = 1`) -/
  jmD : Q.kind = 0 ∨ Q.kind = 1 ∨ Q.kind = 9 ∨ Q.kind = 11 → Q.jm = k
  jmS : Q.kind = 10 → (I.ci = 5 ∨ I.ci = 6 ∨ I.ci = 7 ∨ I.ci = 9) → Q.jm = 1


end ZkFormal.NearV3.Render.UpsGen
