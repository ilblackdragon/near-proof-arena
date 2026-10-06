import ZkFormal.NearV3.Sched.Link.ProcPush

/-!
# ZkFormal.NearV3.Sched.Link.ProcSim — replaying the recorded rounds (`hsim`, abstract part)

* **`simR_map`**: `simR` of rounds `R 0 … R (m−1)` is `some (S m, pr 0 ++ … ++ pr (m−1))` when
  each round shuffles its entries from `S i`'s generator to `(sh i, rg i)` and `runL` of the
  shuffled list from `{S i with rng := rg i}` at time `t i` gives `(S (i+1), pr i)` (times
  chained).
* The spec's state along the AIR's rounds: `specSt` (shuffled order = the AIR's shuffle outputs
  `eoutsOf`, generator `rngAt key kend_i`), its pushes `specPush`.
* **`simR_spec`**: if every round's shuffle is `shuffle (ins) (rngAt key kq_i) =
  some (eoutsOf i, rngAt key kend_i)` (the shuffle link, `Link/ProcShuf`) and the start state's
  generator is `rngAt key 0`, then `simR … (roundsOf …) T0 st = some (specSt … m, specPushes …)`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open NearSpecV3 NearSpecV3.Scheduler

section
variable (n : Nat) (allowed : Array Bool) (reqs : List Req)

/-- **Replay of rounds given by functions.** -/
theorem simR_map (R : Nat → RoundD) (sh : Nat → List Nat) (rg : Nat → Rng) (S : Nat → St)
    (pr : Nat → List PM) (t : Nat → Nat) (m : Nat)
    (hsh : ∀ i, i < m → shuffle ((R i).ents.map Prod.snd) (S i).rng = some (sh i, rg i))
    (hrun : ∀ i, i < m →
      runL n allowed reqs (R i).key (R i).z (sh i) (t i) { S i with rng := rg i } = (S (i + 1), pr i))
    (ht : ∀ i, i + 1 < m → t (i + 1) = t i + (R i).ents.length) :
    simR n allowed reqs ((List.range m).map R) (t 0) (S 0) =
      some (S m, (List.range m).flatMap pr) := by
  have key : ∀ d k, k + d = m →
      simR n allowed reqs ((List.range' k d).map R) (t k) (S k) =
        some (S m, (List.range' k d).flatMap pr) := by
    intro d
    induction d with
    | zero => intro k hk; subst hk; simp [simR]
    | succ d ih =>
      intro k hk
      rw [List.range'_succ, List.map_cons, List.flatMap_cons]
      have hk' : k < m := by omega
      unfold simR
      rw [hsh k hk']
      simp only
      rw [hrun k hk']
      simp only
      cases d with
      | zero =>
        have : k + 1 = m := by omega
        subst this; simp [simR]
      | succ d =>
        rw [← ht k (by omega), ih (k + 1) (by omega)]
  have := key m 0 (by omega)
  rwa [← List.range_eq_range'] at this

end

/-! ## The spec's state along the recorded rounds -/

/-- The ChaCha key words of the instance with key block `f` (`w_j = L_{2j} + 2^16·L_{2j+1}`, limbs
`L_q = lo_q + 256·hi_q` of the public key records). -/
def limbOf (tr : Trace Fp) (tp f q : Nat) : Nat :=
  (cv tr tp (f + q) Proc.sbIn + 256 * cv tr tp (f + q) Proc.sbOut) % 2013265921

def procKey (tr : Trace Fp) (tp f : Nat) : List Nat :=
  (List.range 8).map fun j => limbOf tr tp f (2 * j) + 65536 * limbOf tr tp f (2 * j + 1)

/-- The shuffle outputs of round `i`. -/
def eoutsOf (tr : Trace Fp) (tp f i : Nat) : List Nat :=
  (List.range (cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr)).map fun j =>
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout

/-- The recorded re-pushes of round `i`. -/
def recPush (tr : Trace Fp) (tp f i : Nat) : List PM :=
  let h := Proc.hdrAt tr tp f i
  ((List.range (cv tr tp h Proc.Lr)).filter fun j => cv tr tp (h + 1 + j) Proc.pm == 1).map fun j =>
    ⟨cv tr tp (h + 1 + j) Proc.alOut,
      (if cv tr tp (h + 1 + j) Proc.alOut = 0 then cv tr tp h Proc.z + 1 else 0),
      cv tr tp h Proc.T + j, (cv tr tp (h + 1 + j) Proc.eout + 1) % 2013265921⟩

theorem pushRec_eq (tr : Trace Fp) (tp f m : Nat) :
    pushRec tr tp f m = (List.range m).flatMap (recPush tr tp f) := rfl

section
variable (n : Nat) (allowed : Array Bool) (reqs : List Req) (tr : Trace Fp) (tp f : Nat)

/-- One spec round on the AIR's shuffled order, from state `S` (generator `rngAt key kend_i`). -/
def specRound (i : Nat) (S : St) : St × List PM :=
  runL n allowed reqs (rOf tr tp f i).key (rOf tr tp f i).z (eoutsOf tr tp f i)
    (cv tr tp (Proc.hdrAt tr tp f i) Proc.T)
    { S with rng := rngAt (procKey tr tp f) (cv tr tp (Proc.hdrAt tr tp f i) Proc.kend) }

/-- The spec's state before round `i`. -/
def specSt (st : St) : Nat → St
  | 0 => st
  | i + 1 => (specRound n allowed reqs tr tp f i (specSt st i)).1

/-- The spec's re-pushes of round `i`. -/
def specPush (st : St) (i : Nat) : List PM := (specRound n allowed reqs tr tp f i (specSt n allowed reqs tr tp f st i)).2

end

variable {tr : Trace Fp} {tp f m : Nat}

/-- **`hsim` from the round shuffles.** -/
theorem simR_spec (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hR : ∀ q ∈ reqs, q.incs.length < 64) (I : Proc.Inst tr tp f m)
    (hshuf : ∀ i, i < m →
      shuffle ((rOf tr tp f i).ents.map Prod.snd)
          (rngAt (procKey tr tp f) (cv tr tp (Proc.hdrAt tr tp f i) Proc.kq)) =
        some (eoutsOf tr tp f i, rngAt (procKey tr tp f) (cv tr tp (Proc.hdrAt tr tp f i) Proc.kend)))
    (st : St) (hst : st.rng = rngAt (procKey tr tp f) 0) :
    simR n allowed reqs (roundsOf tr tp f m) T0 st =
      some (specSt n allowed reqs tr tp f st m, (List.range m).flatMap (specPush n allowed reqs tr tp f st)) := by
  -- the generator before round `i`
  have hrng : ∀ i, i < m → (specSt n allowed reqs tr tp f st i).rng =
      rngAt (procKey tr tp f) (cv tr tp (Proc.hdrAt tr tp f i) Proc.kq) := by
    intro i
    induction i with
    | zero => intro hm; rw [(I.first hm).2.1]; exact hst
    | succ i ih =>
      intro hi
      simp only [specSt, specRound]
      rw [(runL_facts n allowed reqs hR _ _ _ _ _).1, (I.chain i hi).2.1]
  have := simR_map n allowed reqs (rOf tr tp f) (eoutsOf tr tp f)
    (fun i => rngAt (procKey tr tp f) (cv tr tp (Proc.hdrAt tr tp f i) Proc.kend))
    (specSt n allowed reqs tr tp f st) (specPush n allowed reqs tr tp f st)
    (fun i => cv tr tp (Proc.hdrAt tr tp f i) Proc.T) m
    (fun i hi => by rw [hrng i hi]; exact hshuf i hi)
    (fun i _ => rfl)
    (fun i hi => by rw [(I.chain i hi).1]; simp [rOf])
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp [roundsOf, simR, specSt]
  · rw [(I.first hpos).1] at this
    exact this

end ZkFormal.NearV3.Sched
