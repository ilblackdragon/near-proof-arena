import ZkFormal.Udr.Rbr
import ZkFormal.Udr.Deep
import ZkFormal.Udr.Fri
import ZkFormal.Stark.Instance

/-!
# ZkFormal.Udr.Np.Sem — semantic reading of an np-udr-stark transcript

Concrete fields `F = Fp`, `K = Fp8` (lane L1).  From a (shaped) partial
transcript `τ : PT Fp8 (Oracle Fp)` of `Iop.verifier Fp Fp8 A prm` we read:

* the column words of every table (main, aux, quotient) on its LDE domain,
  in the verifier's (bit-reversed) position order;
* their unique decodings (when close) — polynomials of length `T + 1`,
  `T = 2^log` the trace height (one more than the trace degree: the DEEP
  preimage `v + (X - z)·g` of a degree-`< T` codeword has length `T + 1`);
* the decoded trace, the semantic constraint polynomials `C_t` and quotients
  `Q_t` (same functions as the verifier's `globalChecks`, at any point `x`,
  with polynomial selectors);
* the DEEP words of each height class and their multilinear batches;
* the FRI run.

Radii: `eRad m = (2^m - 2^(m - logBlowup))/2 - 1` on a domain of size `2^m`
(see REQUESTS R-L3-2).
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

abbrev PTn := PT Fp8 (Oracle Fp)

section
variable (A : Air) (prm : Params)

/-! ## Shape of the transcript -/

def hdrOf (τ : PTn) : List Nat := τ.header?.getD []
def layOf (τ : PTn) : List TLayout := layout A prm (hdrOf τ)
def n0Of (τ : PTn) : Nat := queryLog A prm (hdrOf τ)

/-- The `k`-th committed oracle (0 main, 1 aux, 2 quotient, 3… FRI). -/
def oracleOf (τ : PTn) (k : Nat) : Oracle Fp := τ.oracles.getD k []

def matOf (o : Oracle Fp) (t : Nat) : Mat Fp := o.getD t ⟨0, 0, fun _ => []⟩

/-- Domain point of position `p` of the size-`2^m` domain. -/
def pt (n0 m p : Nat) : Fp8 := Fp8.ofBase (domPoint (K := Fp8) n0 m p)

/-- Trace-domain generator of a table of height `2^log`. -/
def omg (log : Nat) : Fp8 := Fp8.ofBase (Fp.twoAdicGen log)

/-- Unique-decoding radius on a domain of size `2^m`. -/
def eRad (m : Nat) : Nat := (2 ^ m - 2 ^ (m - prm.logBlowup)) / 2 - 1

/-! ## Columns -/

/-- A column: table `t`, kind (`0` main, `1` aux, `2` quotient), index `c`. -/
structure Col where
  t : Nat
  kind : Nat
  c : Nat
  deriving DecidableEq, Repr

/-- Value of a column at position `p` of its table's LDE domain. -/
def colVal (τ : PTn) (d : Col) (p : Nat) : Fp8 :=
  let row := (matOf (oracleOf τ d.kind) d.t).row p
  if d.kind = 0 then Fp8.ofBase (row.getD d.c 0) else (ksOfRow (F := Fp) row).getD d.c 0

/-- Table layout of table `t` (default if out of range). -/
def tl (τ : PTn) (t : Nat) : TLayout := (layOf A prm τ).getD t default

/-- Is `w` within `e` of the length-`D` evaluations at `xs` on `[0, n)`? -/
def CloseRS {ι : Type} (xs : Nat → Fp8) (n D e : Nat) (W : Word ι Fp8) : Prop :=
  ∃ P : ι → Nat → Fp8, dist n W (fun p j => ev D (P j) (xs p)) ≤ e

/-- The columns of a table of the given kinds (`k` = number of kinds present:
1 main, 2 main+aux, 3 all). -/
def tableCols (L : TLayout) (t k : Nat) : List Col :=
  (List.range L.width).map (fun c => ⟨t, 0, c⟩) ++
  (if 2 ≤ k then (List.range L.aux).map (fun c => ⟨t, 1, c⟩) else []) ++
  (if 3 ≤ k then (List.range L.quot).map (fun c => ⟨t, 2, c⟩) else [])

/-- The columns of height class `m` (all tables with LDE log `m`), in table order. -/
def classCols (lay : List TLayout) (m k : Nat) : List Col :=
  (lay.zipIdx.filter fun (L, _) => L.lde == m).flatMap fun (L, t) => tableCols L t k

/-- The interleaved word of class `m`. -/
def classWord (τ : PTn) (m k : Nat) : Word Nat Fp8 :=
  fun p j => match (classCols (layOf A prm τ) m k)[j]? with
    | some d => colVal τ d p
    | none => 0

/-- Every class is within its radius of the interleaved code `RS[T + 1]`. -/
def AllClose (τ : PTn) (k : Nat) : Prop :=
  ∀ L ∈ layOf A prm τ, CloseRS (pt (n0Of A prm τ) L.lde) (2 ^ L.lde) (2 ^ L.log + 1)
    (eRad prm L.lde) (classWord A prm τ L.lde k)

/-- Unique decoding of one column (length `T + 1`), `0` if not close. -/
noncomputable def colP (τ : PTn) (d : Col) : Nat → Fp8 :=
  let L := tl A prm τ d.t
  open Classical in
  if h : ∃ P : Nat → Fp8, dist (2 ^ L.lde) (fun p (_ : Unit) => colVal τ d p)
      (fun p _ => ev (2 ^ L.log + 1) P (pt (n0Of A prm τ) L.lde p)) ≤ eRad prm L.lde
  then Classical.choose h else fun _ => 0

/-- Decoded column polynomial evaluated at `x`. -/
noncomputable def colAt (τ : PTn) (d : Col) (x : Fp8) : Fp8 :=
  ev (2 ^ (tl A prm τ d.t).log + 1) (colP A prm τ d) x

/-! ## Decoded trace and semantic constraints -/

/-- The decoded trace (base-field coordinate of the decoded values on the
trace domain). -/
noncomputable def decTrace (τ : PTn) : Air.Trace Fp where
  log t := (hdrOf τ).getD t 0
  cell t r c := (colAt A prm τ ⟨t, 0, c⟩ (omg ((hdrOf τ).getD t 0) ^ r)).c0

/-- `Σ_{k<T} x^k / T` — the polynomial first-row selector. -/
def selSum (T : Nat) (x : Fp8) : Fp8 := ((T : Nat) : Fp8)⁻¹ * ev T (fun _ => 1) x

/-- Polynomial environment of table `t` at `x` (decoded columns, polynomial selectors). -/
noncomputable def polyEnv (τ : PTn) (t : Nat) (x : Fp8) : Env Fp8 :=
  let log := (tl A prm τ t).log
  let ω := omg log
  { ofNat := fun n => (n : Fp8)
    add := (· + ·), mul := (· * ·), neg := (- ·)
    col := fun c nx => colAt A prm τ ⟨t, 0, c⟩ (if nx then ω * x else x)
    pub := fun i => Fp8.ofBase ((pubOf Fp τ.cb).getD i 0)
    isFirst := selSum (2 ^ log) x
    isLast := selSum (2 ^ log) (ω * x)
    isTransition := 1 - selSum (2 ^ log) (ω * x) }

/-- Clear-text finals (first elems part). -/
def finalsOf (τ : PTn) : List Fp8 := τ.elems.getD 0 []

/-- The finals of table `t` (same slicing as `globalChecks`). -/
def finsOf (τ : PTn) (t : Nat) : List Fp8 :=
  let lay := layOf A prm τ
  let off := ((lay.take t).map fun L => L.sendG + L.recvG).sum
  ((finalsOf τ).drop off).take ((tl A prm τ t).sendG + (tl A prm τ t).recvG)

def tableOf (t : Nat) : Air.Table := A.tables.getD t ⟨0, [], [], 0⟩

/-- All constraint values of table `t` at `x` (verifier order). -/
noncomputable def csAt (τ : PTn) (t : Nat) (αfp γ x : Fp8) : List Fp8 :=
  let L := tl A prm τ t
  let env := polyEnv A prm τ t x
  let ω := omg L.log
  ((tableOf A t).allConstraints.map (·.evalWith env)) ++
    auxConstraints (tableOf A t) prm.auxGroup env αfp γ
      ((List.range L.aux).map fun a => colAt A prm τ ⟨t, 1, a⟩ x)
      ((List.range L.aux).map fun a => colAt A prm τ ⟨t, 1, a⟩ (ω * x)) (finsOf A prm τ t)

/-- The combined constraint polynomial of table `t`. -/
noncomputable def Ct (τ : PTn) (t : Nat) (αfp γ αc x : Fp8) : Fp8 :=
  combine αc (csAt A prm τ t αfp γ x)

/-- The decoded quotient `Σ_j x^{jT} Q_j(x)`. -/
noncomputable def Qt (τ : PTn) (t : Nat) (x : Fp8) : Fp8 :=
  let L := tl A prm τ t
  combine (x ^ (2 ^ L.log)) ((List.range L.quot).map fun q => colAt A prm τ ⟨t, 2, q⟩ x)

/-- The bus equation on the clear-text finals fails. -/
def BusFinalsFail (τ : PTn) : Prop :=
  let lay := layOf A prm τ
  let fins := (lay.foldl (fun (acc : List (List Fp8) × List Fp8) L =>
      (acc.1 ++ [acc.2.take (L.sendG + L.recvG)], acc.2.drop (L.sendG + L.recvG))) ([], finalsOf τ)).1
  let sends : List Fp8 := (fins.zip lay).map fun (f, L) => (f.take L.sendG).foldl (· * ·) 1
  let recvs : List Fp8 := (fins.zip lay).map fun (f, L) => (f.drop L.sendG).foldl (· * ·) 1
  sends.foldl (· * ·) 1 ≠ recvs.foldl (· * ·) 1

/-- The clear-text checks (`globalChecks`) fail on the claimed OOD values. -/
def GlobalFail (τ : PTn) : Prop :=
  match τ.chals, τ.elems with
  | αfp :: γ :: αc :: z :: _, finals :: ood :: _ =>
    globalChecks (F := Fp) A prm (pubOf Fp τ.cb) (layOf A prm τ)
      (splitOod (layOf A prm τ) ood).1 finals αfp γ αc z = false
  | _, _ => False

/-! ## Bus semantics (for the `α_fp` and `γ` rounds) -/

/-- All `(row, interaction)` contributions of one side of a bus, with
natural multiplicities, as fingerprint coefficient lists
`msg ++ [bus + 1]` (decoded trace). -/
noncomputable def busMsgs (τ : PTn) (send : Bool) : List (List Fp8 × Nat) :=
  let tr := decTrace A prm τ
  let pub := pubOf Fp τ.cb
  (List.range A.tables.length).flatMap fun t =>
    (List.range (tr.height t)).flatMap fun r =>
      ((tableOf A t).interactions.filter (·.send == send)).map fun i =>
        ((i.msgVal tr t r pub).map Fp8.ofBase ++ [((i.bus + 1 : Nat) : Fp8)], i.multNat tr t r pub)

/-- Expand multiplicities. -/
def expand (l : List (List Fp8 × Nat)) : List (List Fp8) :=
  l.flatMap fun (m, k) => List.replicate k m

/-- Local constraints (incl. booleanity) fail on the decoded trace. -/
def LocalFail (τ : PTn) : Prop :=
  ∃ t, t < A.tables.length ∧ ∃ r, r < (decTrace A prm τ).height t ∧
    ∃ e ∈ (tableOf A t).allConstraints, e.eval (decTrace A prm τ) t r (pubOf Fp τ.cb) ≠ 0

/-- Fingerprint (L4's convention: `Σ_k m_k α^k`, the bus tag last). -/
def fpL (α : Fp8) (m : List Fp8) : Fp8 := combine α m

/-- The fingerprint multisets of the two sides differ. -/
noncomputable def FpDiffer (τ : PTn) (α : Fp8) : Prop :=
  ¬ ((expand (busMsgs A prm τ true)).map (fpL α)).Perm ((expand (busMsgs A prm τ false)).map (fpL α))

/-- The grand products of the two sides differ. -/
noncomputable def GpDiffer (τ : PTn) (α γ : Fp8) : Prop :=
  ((expand (busMsgs A prm τ true)).map fun m => γ - fpL α m).prod ≠
    ((expand (busMsgs A prm τ false)).map fun m => γ - fpL α m).prod

end
end ZkFormal.Udr.Np
