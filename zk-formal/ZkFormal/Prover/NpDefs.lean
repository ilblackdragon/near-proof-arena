import ZkFormal.Prover.NpPoly
import ZkFormal.Prover.Statements

/-!
# ZkFormal.Prover.NpDefs — the honest np-udr-stark IOP prover (lane L7)

`npProver A cb tr : IopProver Fp Fp8` — a mathematical definition (never executed;
the Rust prover of lane L8 is the executed one, and
`zk-L4-test/…/Stark/RefProver.lean` is the same computation written imperatively).
Message `j` (`next τ = npMsg (τ.chals) (|τ.entries| / 2)`) along the schedule of
`Stark.Protocol` (header `hdr = trHdr A tr`, LDE logs `m_t = log_t + 4`):

| `j` | message | from challenges |
|---|---|---|
| 0 | header, main oracle: column `c` of table `t` is the interpolant of `tr.cell t · c` on `⟨ω_t⟩` (degree `< T_t`), evaluated at `domPoint n0 m_t p` | – |
| 1 | – | |
| 2 | aux oracle (8 limbs per K column), finals | `α_fp = cs[0]`, `γ = cs[1]` |
| 3 | quotient oracle: chunks `Q_j` of `Q = C/(X^T - 1)`, `C = combine α_c (all constraints)` | `α_c = cs[2]` |
| 4 | OOD values at `z`, `ωz` | `z = cs[3]` |
| 5 … 3+L | – (batching rounds) | |
| 4+L+q | FRI kind `q`: roll-in `[]`, or the committed layer `i` (its `2^a`-leaves) | `r_k`, `β_i`, `γ_i` |
| 4+L+#kinds | final polynomial `p₀ + p₁X` | |

Aux columns (per row `r`, values in `Fp8`): per interaction with `k ≥ 2` multiplicity
bits the powers `p₀^(2^j)` and partial products of `∏ (1 + b_j (p₀^(2^j) - 1))`,
`p₀ = γ - fingerprint`; then one running product per group (`auxGroup = 1`):
`a(r) = ∏_{r' < r} Φ(r')`; the final is `a(T)`.

FRI words are positional (as the verifier recomputes them): layer 0 is the batched
DEEP value of the largest class at each position, layer `i+1` the fold of layer `i`
with `β_i` plus the roll-in `γ_{i+1}·B_{n0-i-1}`; the committed oracle of layer `i`
with arity `2^a` has `2^a` consecutive positions per leaf.  The polynomials behind
these words exist only in the proofs.
-/

namespace ZkFormal.Prover.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np

attribute [local instance] Semiring.natCast

/-- The deployed parameters. -/
abbrev dp : Params := Params.default

/-! ## Aux-column building blocks (any environment) -/

/-- Chain columns (powers, then partial products) and the factor `φ` of one interaction. -/
def chainOf (env : Env Fp8) (α γ : Fp8) (i : Interaction) : List Fp8 × Fp8 :=
  let p0 := γ - fingerprint env α i
  match i.mult.map (·.evalWith env) with
  | [] => ([], 1)
  | [b] => ([], 1 + b * (p0 - 1))
  | b0 :: bs =>
    let ps := (List.range bs.length).map fun j => p0 ^ (2 ^ (j + 1))
    let fac := (bs.zip ps).map fun (b, pj) => 1 + b * (pj - 1)
    let pis := (fac.scanl (· * ·) (1 + b0 * (p0 - 1))).tail
    (ps ++ pis, pis.getLastD 1)

/-- All chain columns of a table's interactions. -/
def chainsOf (env : Env Fp8) (α γ : Fp8) (is : List Interaction) : List Fp8 :=
  is.flatMap fun i => (chainOf env α γ i).1

/-- `(interaction, φ)` for every interaction. -/
def phisOf (env : Env Fp8) (α γ : Fp8) (is : List Interaction) : List (Interaction × Fp8) :=
  is.map fun i => (i, (chainOf env α γ i).2)

/-- Running-product groups (sends, then receives), as the verifier forms them. -/
def groupsOf (env : Env Fp8) (α γ : Fp8) (is : List Interaction) : List (List (Interaction × Fp8)) :=
  chunksOf (max dp.auxGroup 1) ((phisOf env α γ is).filter (·.1.send)) ++
    chunksOf (max dp.auxGroup 1) ((phisOf env α γ is).filter (! ·.1.send))

/-- The factor `Φ` of group `j`. -/
def phiG (env : Env Fp8) (α γ : Fp8) (is : List Interaction) (j : Nat) : Fp8 :=
  (((groupsOf env α γ is).getD j []).map (·.2)).foldl (· * ·) 1

section
variable (A : Air) (cb : Bytes) (tr : Trace Fp)

/-! ## Layout of the honest transcript -/

/-- Table `t` (`tableOf`). -/
abbrev tb (t : Nat) : Air.Table := tableOf A t

/-- Trace height log of table `t`. -/
abbrev lg (t : Nat) : Nat := tr.log t

/-- Number of running-product groups of table `t`. -/
def nG (t : Nat) : Nat :=
  numGroups ((tb A t).numSide true) dp.auxGroup + numGroups ((tb A t).numSide false) dp.auxGroup

def hdr : List Nat := trHdr A tr
def n0 : Nat := queryLog A dp (hdr A tr)
def ell : Nat := finalLayer A dp (hdr A tr)
def nB : Nat := batchRounds (layout A dp (hdr A tr))
def kinds : List (Bool × Nat) := friChalKinds A dp (hdr A tr)
def commits : List (Nat × Nat) := friCommits A dp (hdr A tr)

/-! ## Main trace -/

/-- Coefficients of column `c` of table `t` (interpolant on `⟨ω_t⟩`). -/
noncomputable def mainC (t c : Nat) : Nat → Fp :=
  pick fun co => ∀ r, r < 2 ^ lg tr t →
    ev (2 ^ lg tr t) co (Fp.twoAdicGen (lg tr t) ^ r) = tr.cell t r c

/-- The main row of table `t` at a base point `y`. -/
noncomputable def mainRow (t : Nat) (y : Fp) : List Fp :=
  (List.range (tb A t).width).map fun c => ev (2 ^ lg tr t) (mainC tr t c) y

/-- The main values of table `t` at an extension point `x`. -/
noncomputable def mainV (t : Nat) (x : Fp8) : List Fp8 :=
  (List.range (tb A t).width).map fun c => ev (2 ^ lg tr t) (fun k => Fp8.ofBase (mainC tr t c k)) x

noncomputable def mainMat (t : Nat) : Mat Fp :=
  ⟨lg tr t + 4, (tb A t).width, fun p => mainRow A tr t (domPoint (K := Fp8) (n0 A tr) (lg tr t + 4) p)⟩

noncomputable def mainO : Oracle Fp := (List.range A.tables.length).map (mainMat A tr)

/-! ## The polynomial environment of a table -/

/-- Expressions of table `t` evaluated on the column polynomials at `x`
(polynomial selectors). -/
noncomputable def pEnv (t : Nat) (x : Fp8) : Env Fp8 where
  ofNat := fun n => (n : Fp8)
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  col := fun c nx => (mainV A tr t (if nx then omg (lg tr t) * x else x)).getD c 0
  pub := fun i => Fp8.ofBase ((pubOf Fp cb).getD i 0)
  isFirst := selSum (2 ^ lg tr t) x
  isLast := selSum (2 ^ lg tr t) (omg (lg tr t) * x)
  isTransition := 1 - selSum (2 ^ lg tr t) (omg (lg tr t) * x)

/-- The environment of row `r` (`x = ω^r`). -/
noncomputable def rEnv (t r : Nat) : Env Fp8 := pEnv A cb tr t (omg (lg tr t) ^ r)

/-! ## Aux columns -/

/-- Running product of group `j` before row `r`. -/
noncomputable def accAt (α γ : Fp8) (t r j : Nat) : Fp8 :=
  (List.range r).foldl (fun a r' => a * phiG (rEnv A cb tr t r') α γ (tb A t).interactions j) 1

/-- Aux values of row `r`. -/
noncomputable def auxRow (α γ : Fp8) (t r : Nat) : List Fp8 :=
  chainsOf (rEnv A cb tr t r) α γ (tb A t).interactions ++
    (List.range (nG A t)).map (accAt A cb tr α γ t r)

/-- The finals of table `t` (one per group). -/
noncomputable def finsT (α γ : Fp8) (t : Nat) : List Fp8 :=
  (List.range (nG A t)).map (accAt A cb tr α γ t (2 ^ lg tr t))

noncomputable def auxC (α γ : Fp8) (t a : Nat) : Nat → Fp8 :=
  pick fun co => ∀ r, r < 2 ^ lg tr t → ev (2 ^ lg tr t) co (omg (lg tr t) ^ r) =
    (auxRow A cb tr α γ t r).getD a 0

noncomputable def auxV (α γ : Fp8) (t : Nat) (x : Fp8) : List Fp8 :=
  (List.range ((tb A t).auxCount dp.auxGroup)).map fun a => ev (2 ^ lg tr t) (auxC A cb tr α γ t a) x

/-- `8` base limbs per extension element. -/
def limbsL (xs : List Fp8) : List Fp := xs.flatMap fun x => StarkField.limbs (F := Fp) x

noncomputable def auxMat (α γ : Fp8) (t : Nat) : Mat Fp :=
  ⟨lg tr t + 4, 8 * (tb A t).auxCount dp.auxGroup,
    fun p => limbsL (auxV A cb tr α γ t (pt (n0 A tr) (lg tr t + 4) p))⟩

noncomputable def auxO (α γ : Fp8) : Oracle Fp := (List.range A.tables.length).map (auxMat A cb tr α γ)

noncomputable def finalsAll (α γ : Fp8) : List Fp8 :=
  (List.range A.tables.length).flatMap (finsT A cb tr α γ)

/-! ## Composition and quotient -/

/-- All constraint values of table `t` at `x` (the verifier's order). -/
noncomputable def csX (α γ : Fp8) (t : Nat) (x : Fp8) : List Fp8 :=
  ((tb A t).allConstraints.map (·.evalWith (pEnv A cb tr t x))) ++
    auxConstraints (tb A t) dp.auxGroup (pEnv A cb tr t x) α γ (auxV A cb tr α γ t x)
      (auxV A cb tr α γ t (omg (lg tr t) * x)) (finsT A cb tr α γ t)

/-- The composition polynomial `C_t` (as a function). -/
noncomputable def compX (α γ αc : Fp8) (t : Nat) (x : Fp8) : Fp8 := combine αc (csX A cb tr α γ t x)

/-- Coefficients of the quotient `C_t / (X^T - 1)` (length `quot·T`). -/
noncomputable def qC (α γ αc : Fp8) (t : Nat) : Nat → Fp8 :=
  pick fun co => ∀ x, compX A cb tr α γ αc t x =
    (x ^ (2 ^ lg tr t) - 1) * ev ((tb A t).quotCount dp.auxGroup * 2 ^ lg tr t) co x

noncomputable def quotV (α γ αc : Fp8) (t : Nat) (x : Fp8) : List Fp8 :=
  (List.range ((tb A t).quotCount dp.auxGroup)).map fun j =>
    ev (2 ^ lg tr t) (fun k => qC A cb tr α γ αc t (j * 2 ^ lg tr t + k)) x

noncomputable def quotMat (α γ αc : Fp8) (t : Nat) : Mat Fp :=
  ⟨lg tr t + 4, 8 * (tb A t).quotCount dp.auxGroup,
    fun p => limbsL (quotV A cb tr α γ αc t (pt (n0 A tr) (lg tr t + 4) p))⟩

noncomputable def quotO (α γ αc : Fp8) : Oracle Fp :=
  (List.range A.tables.length).map (quotMat A cb tr α γ αc)

/-! ## Out-of-domain values -/

noncomputable def oodT (α γ αc z : Fp8) (t : Nat) : List Fp8 :=
  mainV A tr t z ++ mainV A tr t (omg (lg tr t) * z) ++ auxV A cb tr α γ t z ++
    auxV A cb tr α γ t (omg (lg tr t) * z) ++ quotV A cb tr α γ αc t z

noncomputable def oodAll (α γ αc z : Fp8) : List Fp8 :=
  (List.range A.tables.length).flatMap (oodT A cb tr α γ αc z)

/-! ## Challenges from the challenge list -/

section
variable (cs : List Fp8)

abbrev cAfp : Fp8 := cs.getD 0 0
abbrev cGam : Fp8 := cs.getD 1 0
abbrev cAc : Fp8 := cs.getD 2 0
abbrev cZ : Fp8 := cs.getD 3 0

noncomputable def auxOc : Oracle Fp := auxO A cb tr (cAfp cs) (cGam cs)
noncomputable def finalsC : List Fp8 := finalsAll A cb tr (cAfp cs) (cGam cs)
noncomputable def quotOc : Oracle Fp := quotO A cb tr (cAfp cs) (cGam cs) (cAc cs)
noncomputable def oodC : List Fp8 := oodAll A cb tr (cAfp cs) (cGam cs) (cAc cs) (cZ cs)

/-- A stand-in erased transcript carrying everything the DEEP batch reads. -/
noncomputable def standin : PT Fp8 Unit :=
  ⟨cb, [.msg [.header (hdr A tr)]] ++
    ((cs.take (4 + nB A tr)) ++ List.replicate (kinds A tr).length 0).map .chal ++
    [.msg [.elems (finalsC A cb tr cs), .elems (oodC A cb tr cs), .elems [0, 0]]]⟩

/-- The DEEP context (batching coefficients, OOD sums, `z`). -/
noncomputable def ctx0 : Ctx Fp8 := prep (F := Fp) A dp (standin A cb tr cs)

/-- Openings of the main, aux and quotient oracles at position `x`. -/
noncomputable def opAt (x : Nat) : List (List (List Fp)) :=
  [mainO A tr, auxOc A cb tr cs, quotOc A cb tr cs].map fun o =>
    o.map fun M => M.row (x >>> (n0 A tr - M.log))

/-- Batched DEEP value of class `m` at its position `p`. -/
noncomputable def Bw (m p : Nat) : Fp8 :=
  deepAt (F := Fp) (ctx0 A cb tr cs) (opAt A cb tr cs (p <<< (n0 A tr - m))) m (p <<< (n0 A tr - m))

/-- FRI challenges with their kinds. -/
def friCs : List ((Bool × Nat) × Fp8) := (kinds A tr).zip (cs.drop (4 + nB A tr))

def betaL : List Fp8 := ((friCs A tr cs).filter (! ·.1.1)).map (·.2)
def gammaL : List (Nat × Fp8) := ((friCs A tr cs).filter (·.1.1)).map fun (k, c) => (k.2, c)

/-- The FRI layer words (layer `i`, position `p` of the size-`2^(n0-i)` domain). -/
noncomputable def word : Nat → Nat → Fp8
  | 0, p => Bw A cb tr cs (n0 A tr) p
  | i + 1, q =>
    let u0 := word i (2 * q)
    let u1 := word i (2 * q + 1)
    let y : Fp := domPoint (K := Fp8) (n0 A tr) (n0 A tr - i) (2 * q)
    let f := (2 : Fp8)⁻¹ * (u0 + u1) + (betaL A tr cs).getD i 0 * (u0 - u1) * Fp8.ofBase ((2 * y)⁻¹)
    match (gammaL A tr cs).lookup (i + 1) with
    | some g => f + g * Bw A cb tr cs (n0 A tr - (i + 1)) q
    | none => f

/-- The committed FRI oracle of layer `c` with arity `2^a`. -/
noncomputable def friMat (c a : Nat) : Mat Fp :=
  ⟨n0 A tr - c - a, 8 * 2 ^ a, fun j =>
    limbsL ((List.range (2 ^ a)).map fun s => word A cb tr cs c (j * 2 ^ a + s))⟩

/-- The final polynomial `[p₀, p₁]` (from positions `0, 1` = points `y, -y`). -/
noncomputable def finalPoly : List Fp8 :=
  let w := word A cb tr cs (ell A tr)
  let y0 : Fp := domPoint (K := Fp8) (n0 A tr) (n0 A tr - ell A tr) 0
  [(2 : Fp8)⁻¹ * (w 0 + w 1), (w 0 - w 1) * Fp8.ofBase ((2 * y0)⁻¹)]

/-- Prover message number `j` (slot `2j`) given the challenges so far. -/
noncomputable def npMsg (j : Nat) : List (PartV Fp8 (Oracle Fp)) :=
  if j = 0 then [.header (hdr A tr), .oracle (mainO A tr)]
  else if j = 1 then []
  else if j = 2 then [.oracle (auxOc A cb tr cs), .elems (finalsC A cb tr cs)]
  else if j = 3 then [.oracle (quotOc A cb tr cs)]
  else if j = 4 then [.elems (oodC A cb tr cs)]
  else if j < 4 + nB A tr then []
  else match (kinds A tr)[j - (4 + nB A tr)]? with
    | some (true, _) => []
    | some (false, i) =>
      match (commits A tr).lookup i with
      | some a => [.oracle [friMat A cb tr cs i a]]
      | none => []
    | none => [.elems (finalPoly A cb tr cs)]

end

/-- **The honest np-udr-stark IOP prover** for the trace `tr`. -/
noncomputable def npProver : IopProver Fp Fp8 :=
  ⟨hdr A tr, fun τ => npMsg A cb tr τ.chals (τ.entries.length / 2)⟩

end

end ZkFormal.Prover.Np
