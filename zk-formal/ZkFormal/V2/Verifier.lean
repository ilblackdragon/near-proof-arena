import ZkFormal.Stark.Verifier
import ZkFormal.Stark.Instance
import ZkFormal.V2.Air

/-!
# ZkFormal.V2.Verifier — the verifier of `np-udr-stark-v2` (lane L4)

`Iop.verifierP F K AP prm` is v1's `Iop.verifier F K AP.toAir prm` with **one**
change.  Header admissibility, schedule, query rule and the per-position checks
(`checkAt`) are v1's, field by field.  Only the clear-text check `global` differs:

* v1: per-table ALI identities, and `∏ send finals = ∏ receive finals`;
* v2: the same ALI identities, every public segment fits (`pubFit`), and
  `∏ send finals · Π_pub(send) = ∏ receive finals · Π_pub(recv)`, where
  `Π_pub(s) = ∏_{public messages (b, s, m)} (γ − fp_α(m ‖ b+1))` with v1's fingerprint
  convention `fp_α(x) = Σ_k x_k α^k`.

`prepP` duplicates v1's `prep` and computes the new `globalOk`.  It is a copy rather than
`{ prep … with globalOk := … }` so that the deployed verifier evaluates the ALI checks
once.  `prepP_eq` shows that it agrees with `prep` on every other field.  So
`ChecksPass` of v2 is that of v1 (`checksPass_eq`), and v1's query-phase
analysis applies unchanged.

With no public segments, `globalChecksP = globalChecks` (`globalChecksP_nil`): the
v2 verifier of `AirP.ofAir A` accepts exactly what v1's verifier of `A` accepts,
except that its `global` also checks the (trivially true) `pubFit`.

Proof bytes are those of v1: the prover's messages do not change.
The public products are recomputed by the verifier from the claim.
-/

namespace ZkFormal.V2

open ArenaCore Lean.Grind ZkFormal.Air ZkFormal.Stark

/-- BabyBear elements read as naturals: the canonical representative. -/
instance : PubVal ZkFormal.Algebra.Fp := ⟨ZkFormal.Algebra.Fp.toNat⟩

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K] [PubVal F]

attribute [local instance] Semiring.natCast

/-- Fingerprint of a public message: `fp_α(m ‖ (bus+1))`, v1's convention. -/
def pubFp (α : K) (b : Nat) (m : List F) : K :=
  combine α (m.map StarkField.embed ++ [((b + 1 : Nat) : K)])

/-- `Π_pub(s)`: the product of `γ − fp` over the public messages of side `s`. -/
def pubProd (AP : AirP) (pub : List F) (α γ : K) (s : Bool) : K :=
  ((pubMsgs AP pub).filter fun x => x.2.1 == s).foldl
    (fun acc x => acc * (γ - pubFp α x.1 x.2.2)) 1

/-- The global ALI and bus checks of v2 (v1's `globalChecks` with the public products). -/
def globalChecksP (AP : AirP) (prm : Params) (pub : List F) (lay : List TLayout)
    (ood : List (TOod K)) (finals : List K) (αfp γ αc z : K) : Bool :=
  let perTable := (AP.tables.zip (lay.zip ood))
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
  r.1 && decide (sends.foldl (fun a b => a * b) (1 : K) * pubProd AP pub αfp γ true =
    recvs.foldl (fun a b => a * b) (1 : K) * pubProd AP pub αfp γ false)

/-- Build the v2 context from an erased complete transcript (v1's `prep`, new `globalOk`). -/
def prepP (AP : AirP) (prm : Params) (τ : PT K Unit) : Ctx K :=
  match τ.header? with
  | none => .bad
  | some hdr =>
    let A := AP.toAir
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
        globalOk := okLens && pubFit AP pub &&
          globalChecksP (F := F) AP prm pub lay oods finals αfp γ αc z }
    | _, _ => .bad

/-- The v2 `globalOk` as a function of the transcript (`false` on malformed ones). -/
def globalOkP (AP : AirP) (prm : Params) (τ : PT K Unit) : Bool :=
  match τ.header? with
  | none => false
  | some hdr =>
    let pub : List F := τ.cb.map fun b => ofNatF b.toNat
    let lay := layout AP.toAir prm hdr
    match τ.chals, τ.elems with
    | αfp :: γ :: αc :: z :: rest, [finals, ood, fp] =>
      let okLens := decide (rest.length = batchRounds lay + (friChalKinds AP.toAir prm hdr).length) &&
        decide (fp.length = 2) &&
        decide (finals.length = (lay.map fun L => L.sendG + L.recvG).sum) &&
        decide (ood.length = (lay.map fun L => 2 * L.width + 2 * L.aux + L.quot).sum)
      okLens && pubFit AP pub &&
        globalChecksP (F := F) AP prm pub lay (splitOod lay ood).1 finals αfp γ αc z
    | _, _ => false

/-- `prepP` is v1's `prep` with `globalOk := globalOkP`. -/
theorem prepP_eq (AP : AirP) (prm : Params) (τ : PT K Unit) :
    prepP (F := F) AP prm τ = { prep (F := F) AP.toAir prm τ with globalOk := globalOkP (F := F) AP prm τ } := by
  unfold prepP prep globalOkP
  generalize τ.header? = oh
  generalize τ.chals = cs
  generalize τ.elems = es
  rcases oh with _ | hdr
  · rfl
  · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
    rcases es with _ | ⟨e1, _ | ⟨e2, _ | ⟨e3, _ | ⟨e4, es'⟩⟩⟩⟩ <;>
    first
    | rfl
    | (dsimp only
       generalize splitOod (layout AP.toAir prm hdr) e2 = so
       rcases so with ⟨oods, r⟩
       rfl)

end

/-- **The IOP verifier of `np-udr-stark-v2`**: v1's, with v2's clear-text checks. -/
def Iop.verifierP (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K]
    [PubVal F] (AP : AirP) (prm : Params) : IopSpec F K :=
  { Iop.verifier F K AP.toAir prm with
    prep := prepP (F := F) AP prm
    global := fun c => c.globalOk }

/-- **The deployed verifier model of `np-udr-stark-v2`**: the BCS compilation of `Iop.verifierP`. -/
def verifierP (F K : Type) [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K]
    [PubVal F] (AP : AirP) (prm : Params) : ZkFormal.TreeVerifier :=
  ⟨fun pub cb pb => Bcs.compile (F := F) (Iop.verifierP F K AP prm) pub cb pb⟩

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K] [PubVal F]
variable (AP : AirP) (prm : Params)

theorem verifierP_eq_compile (pub cb pb : Bytes) :
    (verifierP F K AP prm).tree pub cb pb = Bcs.compile (F := F) (Iop.verifierP F K AP prm) pub cb pb :=
  rfl

/-- The local (per-position) checks of v2 are v1's. -/
theorem checksPass_eq {O : Type} (τ : PT K O) (x : Nat) (op : List (List (List F))) :
    (Iop.verifierP F K AP prm).ChecksPass τ x op ↔ (Iop.verifier F K AP.toAir prm).ChecksPass τ x op := by
  unfold IopSpec.ChecksPass
  show checkAt (F := F) (prepP (F := F) AP prm τ.erase) x op = true ↔
    checkAt (F := F) (prep (F := F) AP.toAir prm τ.erase) x op = true
  rw [prepP_eq]
  rfl

/-- Same header admissibility, schedule, query rule, position encoding and size cap as v1. -/
theorem headerOk_eq : (Iop.verifierP F K AP prm).headerOk = (Iop.verifier F K AP.toAir prm).headerOk := rfl
theorem schedule_eq : (Iop.verifierP F K AP prm).schedule = (Iop.verifier F K AP.toAir prm).schedule := rfl
theorem queryLog_eq : (Iop.verifierP F K AP prm).queryLog = (Iop.verifier F K AP.toAir prm).queryLog := rfl

end

/-! ## No public segments: v2's bus check is v1's -/

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F] [DecidableEq K] [PubVal F]

theorem pubProd_nil {AP : AirP} (h : AP.pubSegs = []) (pub : List F) (α γ : K) (s : Bool) :
    pubProd AP pub α γ s = 1 := by
  simp [pubProd, pubMsgs_nil h]

theorem globalChecksP_nil {AP : AirP} (h : AP.pubSegs = []) (prm : Params) (pub : List F)
    (lay : List TLayout) (ood : List (TOod K)) (finals : List K) (αfp γ αc z : K) :
    globalChecksP AP prm pub lay ood finals αfp γ αc z =
      globalChecks AP.toAir prm pub lay ood finals αfp γ αc z := by
  unfold globalChecksP globalChecks
  simp only [pubProd_nil h, Semiring.mul_one]

end

end ZkFormal.V2
