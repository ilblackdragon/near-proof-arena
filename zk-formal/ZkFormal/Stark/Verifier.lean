import ZkFormal.Stark.Protocol

/-!
# ZkFormal.Stark.Verifier — the decision functions of `np-udr-stark-v1`

`Iop.verifier A prm : IopSpec F K` (schedule from `Protocol`, plus the
clear-text checks `global` and the per-position checks `check`), and the
deployed verifier model `verifier A prm : TreeVerifier`, its BCS compilation.

* **global** (DESIGN.md §4 step 4): for every table, the ALI identity at the
  out-of-domain point `z`,
  `Σ_j α_c^j · c_j(z) = (z^T - 1) · Σ_j z^{jT} · Q_j(z)`,
  where `c_j` ranges over `Table.allConstraints` and then the generated aux
  (grand-product) constraints, evaluated from the claimed OOD values; and the
  bus equation `∏ send finals = ∏ receive finals`.
* **check** at position `x`: the batched DEEP functions of every height class
  from the opened rows, then FRI: layer-0 and committed-layer leaf
  consistency, the folds `f' = (u₀+u₁)/2 + β·(u₀-u₁)/(2y)`, roll-ins
  `f ← f + γ_i·B_class`, and the final polynomial `p₀ + p₁·X`.

Selectors at `z` (table height `T`, trace generator `ω`):
`isFirst = (z^T-1)/(T(z-1))`, `isLast = (z^T-1)/(T(ωz-1))`,
`isTransition = 1 - isLast`.
-/

namespace ZkFormal.Stark

open ArenaCore Lean.Grind ZkFormal.Air

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K]

attribute [local instance] Semiring.natCast

/-- Extension elements from a row of base limbs (8 per element). -/
def ksOfRow (row : List F) : List K :=
  (chunksOf 8 row).map StarkField.ofLimbs

/-- `x^n` by repeated squaring (`n` given by its bits). -/
def powK (x : K) (n : Nat) : K := x ^ n

/-- Evaluation environment at the OOD point for one table. -/
def oodEnv (pub : List F) (log : Nat) (z : K) (cur nxt : List K) : Env K :=
  let T : K := ((2 ^ log : Nat) : K)
  let ω : K := StarkField.embed (StarkField.twoAdicGen (K := K) log : F)
  let zT := z ^ (2 ^ log)
  let isLast := (zT - 1) / (T * (ω * z - 1))
  { ofNat := fun n => (n : K)
    add := (· + ·), mul := (· * ·), neg := (- ·)
    col := fun c nx => (if nx then nxt else cur).getD c 0
    pub := fun i => StarkField.embed (pub.getD i 0)
    isFirst := (zT - 1) / (T * (z - 1))
    isLast := isLast
    isTransition := 1 - isLast }

/-- Message fingerprint `(bus+1)·α^len + Σ_k msg_k·α^k`. -/
def fingerprint (env : Env K) (α : K) (i : Interaction) : K :=
  let r := i.msg.foldl (fun (acc : K × K) e => (acc.1 + e.evalWith env * acc.2, acc.2 * α)) (0, 1)
  r.1 + ((i.bus + 1 : Nat) : K) * r.2

/-- Constraints of one interaction's multiplicity chain and its factor `φ_i`;
consumes `2(k-1)` aux values (powers then partial products). -/
def interactionAux (env : Env K) (α γ : K) (i : Interaction) (aux : List K) :
    List K × K × List K :=
  let p0 := γ - fingerprint env α i
  let bits := i.mult.map (·.evalWith env)
  match bits with
  | [] => ([], 1, aux)
  | [b] => ([], 1 + b * (p0 - 1), aux)
  | b0 :: bs =>
    let k := bs.length
    let ps := aux.take k
    let pis := (aux.drop k).take k
    let rest := aux.drop (2 * k)
    -- powers: P_j - P_{j-1}^2
    let prevP := p0 :: ps
    let cP := (ps.zip prevP).map fun (pj, pj1) => pj - pj1 * pj1
    -- partial products: Π_1 = (1+b0(P0-1))(1+b1(P1-1)), Π_j = Π_{j-1}(1+bj(Pj-1))
    let fac := (bs.zip ps).map fun (b, pj) => 1 + b * (pj - 1)
    let prevPi := (1 + b0 * (p0 - 1)) :: pis
    let cPi := ((pis.zip prevPi).zip fac).map fun ((pij, pij1), f) => pij - pij1 * f
    (cP ++ cPi, pis.getLastD 1, rest)

/-- All aux constraints of a table at `z` (order: per interaction chains, then
send groups, then receive groups; per group: first, transition, last). -/
def auxConstraints (T : Air.Table) (g : Nat) (env : Env K) (α γ : K)
    (auxZ auxG : List K) (fins : List K) : List K :=
  -- interaction chains
  let step := fun (acc : List K × List (Interaction × K) × List K) (i : Interaction) =>
    let (cs, phi, rest) := interactionAux env α γ i acc.2.2
    (acc.1 ++ cs, acc.2.1 ++ [(i, phi)], rest)
  let (cs, phis, rest) := T.interactions.foldl step ([], [], auxZ)
  let nChain := auxZ.length - rest.length
  let groups := (chunksOf (max g 1) (phis.filter (·.1.send))) ++
                (chunksOf (max g 1) (phis.filter (! ·.1.send)))
  let accs := (rest.zip (auxG.drop nChain))
  let gc := ((groups.zip accs).zip fins).flatMap fun ((grp, (a, an)), fin) =>
    let Φ := (grp.map (·.2)).foldl (· * ·) 1
    [env.isFirst * (a - 1), env.isTransition * (an - a * Φ), env.isLast * (a * Φ - fin)]
  cs ++ gc

/-- `Σ_j α^j c_j`. -/
def combine (α : K) (cs : List K) : K := cs.foldr (fun c acc => c + α * acc) 0

/-- Multilinear (monomial) batching coefficients `∏_k r_k^{bit_k(i)}`,
`i < 2^|r|` (bit `k` ↔ `r_k`): round `k` combines pairs as `u₀ + r_k·u₁`,
a line. -/
def eqTable (rs : List K) : List K :=
  rs.foldl (fun eqs r => eqs ++ eqs.map (· * r)) [1]

/-- Per-table OOD values. -/
structure TOod (K : Type) where
  mainZ : List K
  mainG : List K
  auxZ : List K
  auxG : List K
  quotZ : List K

def splitOod (lay : List TLayout) (ood : List K) : List (TOod K) × List K :=
  lay.foldl (fun (acc : List (TOod K) × List K) L =>
    let o := acc.2
    let a := o.take L.width; let o := o.drop L.width
    let b := o.take L.width; let o := o.drop L.width
    let c := o.take L.aux; let o := o.drop L.aux
    let d := o.take L.aux; let o := o.drop L.aux
    let e := o.take L.quot; let o := o.drop L.quot
    (acc.1 ++ [⟨a, b, c, d, e⟩], o)) ([], ood)

/-- Precomputed data for one table in the DEEP batch. -/
structure TDeep (K : Type) where
  /-- batching coefficients for main@z, main@gz, aux@z, aux@gz, quot@z -/
  eMz : List K
  eMg : List K
  eAz : List K
  eAg : List K
  eQ : List K
  /-- `Σ eq·v` over the `z` group and over the `gz` group -/
  vz : K
  vg : K

/-- Verification context: everything that does not depend on the position. -/
structure Ctx (K : Type) where
  ok : Bool
  hdr : List Nat
  lay : List TLayout
  n0 : Nat
  ℓ : Nat
  z : K
  /-- per table -/
  ood : List (TOod K)
  deep : List (TDeep K)
  /-- FRI: committed layers with arities, β per layer, γ per roll-in layer -/
  commits : List (Nat × Nat)
  betas : List K
  gammas : List (Nat × K)
  finalPoly : List K
  /-- global-check result -/
  globalOk : Bool

/-- Default (rejecting) context. -/
def Ctx.bad : Ctx K := ⟨false, [], [], 0, 0, 0, [], [], [], [], [], [], false⟩


/-- Kinds of the FRI challenges in schedule order: `(true, i)` = roll-in `γ_i`,
`(false, i)` = fold `β_i`. -/
def friChalKinds (A : Air) (prm : Params) (hdr : List Nat) : List (Bool × Nat) :=
  let ℓ := finalLayer A prm hdr
  ((List.range ℓ).flatMap fun i =>
    (if rollInAt A prm hdr i then [(true, i)] else []) ++ [(false, i)]) ++
  (if rollInAt A prm hdr ℓ then [(true, ℓ)] else [])

/-- The global ALI and bus checks. -/
def globalChecks (A : Air) (prm : Params) (pub : List F) (lay : List TLayout) (ood : List (TOod K))
    (finals : List K) (αfp γ αc z : K) : Bool :=
  let perTable := (A.tables.zip (lay.zip ood))
  let r := perTable.foldl (fun (acc : Bool × List K) (T, L, o) =>
    let fins := acc.2.take (L.sendG + L.recvG)
    let env := oodEnv pub L.log z o.mainZ o.mainG
    let cs := (T.allConstraints.map (·.evalWith env)) ++
      auxConstraints T prm.auxGroup env αfp γ o.auxZ o.auxG fins
    let zT := z ^ (2 ^ L.log)
    let qz := combine zT o.quotZ
    (acc.1 && decide (combine αc cs = (zT - 1) * qz), acc.2.drop (L.sendG + L.recvG)))
    (true, finals)
  let fins := (lay.foldl (fun (acc : List (List K) × List K) L =>
      (acc.1 ++ [acc.2.take (L.sendG + L.recvG)], acc.2.drop (L.sendG + L.recvG))) ([], finals)).1
  let sends : List K := (fins.zip lay).map fun (f, L) => (f.take L.sendG).foldl (· * ·) 1
  let recvs : List K := (fins.zip lay).map fun (f, L) => (f.drop L.sendG).foldl (· * ·) 1
  r.1 && decide (sends.foldl (fun a b => a * b) (1 : K) = recvs.foldl (fun a b => a * b) (1 : K))

/-- Build the context from an erased complete transcript. -/
def prep (A : Air) (prm : Params) (τ : PT K Unit) : Ctx K :=
  match τ.header? with
  | none => .bad
  | some hdr =>
    let lay := layout A prm hdr
    let pub : List F := τ.cb.map fun b => ofNatF b.toNat
    match τ.chals, τ.elems with
    | αfp :: γ :: αc :: z :: rest, [finals, ood, fp] =>
      let L := batchRounds lay
      let rs := rest.take L
      let fri := rest.drop L
      let kinds := friChalKinds A prm hdr
      let betas := ((kinds.zip fri).filter (! ·.1.1)).map (·.2)
      let gammas := ((kinds.zip fri).filter (·.1.1)).map fun (k, c) => (k.2, c)
      let (oods, _) := splitOod lay ood
      let eqs := eqTable rs
      -- class offsets: functions of a class are numbered across its tables in order
      let deep := ((lay.zip oods).foldl (fun (acc : List (TDeep K) × List (Nat × Nat)) (Lt, o) =>
        let off := (acc.2.lookup Lt.lde).getD 0
        let e := eqs.drop off
        let eMz := e.take Lt.width; let e := e.drop Lt.width
        let eMg := e.take Lt.width; let e := e.drop Lt.width
        let eAz := e.take Lt.aux; let e := e.drop Lt.aux
        let eAg := e.take Lt.aux; let e := e.drop Lt.aux
        let eQ := e.take Lt.quot
        let dot (a b : List K) : K := (a.zip b).foldl (fun s (u, v) => s + u * v) 0
        let td : TDeep K := ⟨eMz, eMg, eAz, eAg, eQ,
          dot eMz o.mainZ + dot eAz o.auxZ + dot eQ o.quotZ, dot eMg o.mainG + dot eAg o.auxG⟩
        let cnt := 2 * Lt.width + 2 * Lt.aux + Lt.quot
        (acc.1 ++ [td], (Lt.lde, off + cnt) :: acc.2.filter (·.1 != Lt.lde))) ([], [])).1
      let okLens := decide (rest.length = L + kinds.length) && decide (fp.length = 2) &&
        decide (finals.length = (lay.map fun L => L.sendG + L.recvG).sum) &&
        decide (ood.length = (lay.map fun L => 2 * L.width + 2 * L.aux + L.quot).sum)
      { ok := okLens, hdr, lay, n0 := queryLog A prm hdr, ℓ := finalLayer A prm hdr, z
        ood := oods, deep, commits := friCommits A prm hdr, betas, gammas, finalPoly := fp
        globalOk := okLens && globalChecks (F := F) A prm pub lay oods finals αfp γ αc z }
    | _, _ => .bad

/-- The batched DEEP value of class `m` at its position `p` from the openings
`op = [main, aux, quot, …]` (rows of each table at `p`). -/
def deepAt (c : Ctx K) (op : List (List (List F))) (m x : Nat) : K :=
  let p := x >>> (c.n0 - m)
  let ξ : K := StarkField.embed (domPoint (K := K) c.n0 m p : F)
  let main := op.getD 0 []; let aux := op.getD 1 []; let quot := op.getD 2 []
  let rows := ((c.lay.zip c.deep).zipIdx).filter (·.1.1.lde == m)
  match rows with
  | [] => 0
  | ((L0, _), _) :: _ =>
    let ω : K := StarkField.embed (StarkField.twoAdicGen (K := K) L0.log : F)
    let dotF (e : List K) (row : List F) : K :=
      (e.zip row).foldl (fun s (u, v) => s + u * StarkField.embed v) 0
    let dotK (e : List K) (row : List K) : K := (e.zip row).foldl (fun s (u, v) => s + u * v) 0
    let (sz, sg) := rows.foldl (fun (acc : K × K) ((_, d), t) =>
      let mr := main.getD t []; let ar : List K := ksOfRow (aux.getD t [])
      let qr : List K := ksOfRow (quot.getD t [])
      (acc.1 + dotF d.eMz mr + dotK d.eAz ar + dotK d.eQ qr - d.vz,
       acc.2 + dotF d.eMg mr + dotK d.eAg ar - d.vg)) (0, 0)
    sz / (ξ - c.z) + sg / (ξ - ω * c.z)

/-- One fold step at layer `i`: pairs `(u_{2k}, u_{2k+1})` at absolute
positions `base + 2k` of layer `i` (domain log `n0 - i`). -/
def foldOnce (c : Ctx K) (i base : Nat) (β : K) (us : List K) : List K :=
  let inv2 : K := (2 : K)⁻¹
  (chunksOf 2 us).zipIdx.map fun (pr, k) =>
    let u0 := pr.getD 0 0; let u1 := pr.getD 1 0
    let y : F := domPoint (K := K) c.n0 (c.n0 - i) (base + 2 * k)
    let iy : K := StarkField.embed ((2 * y)⁻¹ : F)
    inv2 * (u0 + u1) + β * (u0 - u1) * iy

/-- Fold a committed leaf (`2^a` values at layer `c0`, leaf index `j`) down
to a single value at layer `c0 + a`. -/
def foldLeaf (c : Ctx K) (c0 a j : Nat) (us : List K) : K :=
  ((List.range a).foldl (fun (acc : List K) s =>
    let i := c0 + s
    foldOnce (F := F) c i ((j <<< (a - s))) (c.betas.getD i 0) acc) us).getD 0 0

/-- Per-position check: DEEP batch, FRI consistency, final polynomial. -/
def checkAt (c : Ctx K) (x : Nat) (op : List (List (List F))) : Bool :=
  let rollIn (i : Nat) (v : K) : K :=
    match c.gammas.lookup i with
    | some γ => v + γ * deepAt (F := F) c op (c.n0 - i) x
    | none => v
  let v0 := deepAt (F := F) c op c.n0 x
  let fri := op.drop 3
  let r := (c.commits.zip fri).foldl (fun (acc : Bool × K) ((c0, a), o) =>
    let v := if c0 = 0 then acc.2 else rollIn c0 acc.2
    let p := x >>> c0
    let us : List K := ksOfRow ((o.getD 0 []))
    let ok := decide (us.getD (p % 2 ^ a) 0 = v) && decide (us.length = 2 ^ a)
    (acc.1 && ok, foldLeaf (F := F) c c0 a (p >>> a) us)) (true, v0)
  let vℓ := if c.ℓ = 0 then r.2 else rollIn c.ℓ r.2
  let ξ : K := StarkField.embed (domPoint (K := K) c.n0 (c.n0 - c.ℓ) (x >>> c.ℓ) : F)
  c.ok && r.1 && decide (fri.length = c.commits.length) &&
    decide (vℓ = c.finalPoly.getD 0 0 + c.finalPoly.getD 1 0 * ξ)

end

/-- **The IOP verifier of `np-udr-stark-v1`** for the AIR `A`. -/
def Iop.verifier (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K]
    (A : Air) (prm : Params) : IopSpec F K where
  numTables := A.tables.length
  headerOk := headerOk A prm
  schedule := schedule A prm
  queryLog := queryLog A prm
  numChunks := prm.numChunks
  posPerChunk := prm.posPerChunk
  posBits := prm.posBits
  maxProofBytes := prm.maxProofBytes
  Ctx := Ctx K
  prep := prep (F := F) A prm
  global := fun c => c.globalOk
  check := checkAt (F := F)

/-- **The deployed verifier model**: the BCS compilation of `Iop.verifier`. -/
def verifier (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K]
    (A : Air) (prm : Params) : ZkFormal.TreeVerifier :=
  ⟨fun pub cb pb => Bcs.compile (F := F) (Iop.verifier F K A prm) pub cb pb⟩

theorem verifier_eq_compile (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F]
    [DecidableEq K] (A : Air) (prm : Params) (pub cb pb : Bytes) :
    (verifier F K A prm).tree pub cb pb = Bcs.compile (F := F) (Iop.verifier F K A prm) pub cb pb :=
  rfl

end ZkFormal.Stark
