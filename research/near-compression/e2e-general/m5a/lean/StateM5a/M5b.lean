import StateM5a.St
import StateM5a.SnResp
import StateM5a.WsEntries

/-!
# StateM5a.M5b — the M5a theorems apply to the M5b AIR the prover runs

The M5b prover AIR (`m5a-tool airb`, `prover/` with `htape.json`) is, in table order,
`fullAir D (m5bX host prev post n)` followed by the native SHA-512 chip (`ChipStub`):

* the 12 `m5aAir` tables;
* the M5a public tape with **no writes**, `tapeTable (m5aTape [] prev post n)` (only the root
  chain's ends `TCH(0, prev)`, `TCH(n, post)`): the writes now come from `STW` rows;
* `m5bExtra` = `SHAS` (a second instance of the unchanged SHA-256 table on buses `SB2`/`SD2`),
  `STB`, `STW` (`St.lean`);
* the execution side's public messages `tapeTable host` (`SREQ`/`HB`; on T1 `htape.json`).

Every theorem of `StateM5a` is stated for `fullAir D extra nb np` with premises that restrict
what the extra tables may do on the M5a buses.  The extra tables of the M5b AIR use only the buses
`TCH` (the M5a tape), `SB2`, `SD2`, `SREQ`, `HB`, `DESC` and `WRITE` (`x_buses`), so every such
premise holds (`x_hx`, `x_hsil`, `rest_hr`, `rest_hrN`, `rest_hrS`, `x_hxV`), and **`prem`**
builds `FinalOrder.Prem` from `Holds` and the semantic premises alone.  Hence
`WsEntries.ws_entries`, `FinalOrder.air_final_sorted`, `SnResp.air_final_sorted_sn2`, … hold for
the M5b AIR with `extra := m5bX host prev post n` (`writes := []`, `rest := m5bRest host`), with
the same remaining premises as on the M5a AIR — minus the tape-time premise, which M5a-6 removed
(`WsDecode3.wsa_t_rng`).

Not covered here (open): the meaning of the new rows — that each `WRITE` an `STW` row sends
carries `sha256` of the key / value bytes the execution side sent on `HB` for its request
(`SHAS`'s digest contract, single run per message id, `DESC` balance).  The M5a theorems take the
`WRITE` messages as given (they constrain the working set by its `WM`/`PT`/`RCH` traffic), so they
hold whatever produces them.
-/

namespace StateM5a.M5b

open ZkFormal.Air ZkFormal.Algebra StateM5a.Bus StateM5a.Tape StateM5a.KeyDecode StateM5a.DecodeM5a StateM5a.FinalOrder

/-- The buses of the M5b extra tables. -/
def stBuses : List Nat := [B_TCH, B_SB2, B_SD2, B_SREQ, B_HB, B_DESC, B_WRITE]

/-- The execution side's public messages are requests and bytes. -/
def HostOK (host : List (Nat × Bool × List Nat)) : Prop := ∀ e ∈ host, e.1 = B_SREQ ∨ e.1 = B_HB

/-- The tables after the M5a tape. -/
def m5bRest (host : List (Nat × Bool × List Nat)) : List Table := m5bExtra ++ [tapeTable host]

/-- The extra tables of the M5b prover AIR (`fullAir D (m5bX …)`). -/
def m5bX (host : List (Nat × Bool × List Nat)) (prev post : NearSpec.Bytes) (n : Nat) : List Table :=
  tapeTable (m5aTape [] prev post n) :: m5bRest host

theorem extra_buses :
    (m5bExtra.all fun T => T.interactions.all fun i => decide (i.bus ∈ stBuses)) = true := by decide

theorem rest_buses {host : List (Nat × Bool × List Nat)} (hh : HostOK host) :
    ∀ T ∈ m5bRest host, ∀ i ∈ T.interactions, i.bus ∈ stBuses := by
  intro T hT i hi
  rcases List.mem_append.1 hT with hT | hT
  · exact of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 extra_buses T hT) i hi)
  · simp only [List.mem_singleton] at hT
    subst hT
    simp only [tapeTable, List.mem_map] at hi
    obtain ⟨e, he, rfl⟩ := hi
    rcases hh e he with h | h <;> simp [stBuses, h]

theorem x_buses {host : List (Nat × Bool × List Nat)} (hh : HostOK host) (prev post : NearSpec.Bytes)
    (n : Nat) : ∀ T ∈ m5bX host prev post n, ∀ i ∈ T.interactions, i.bus ∈ stBuses := by
  intro T hT i hi
  rcases List.mem_cons.1 hT with rfl | hT
  · rcases tape_bus [] prev post n i hi with h | h <;> simp [stBuses, h]
  · exact rest_buses hh T hT i hi

theorem no_bus {L : List Table} (hL : ∀ T ∈ L, ∀ i ∈ T.interactions, i.bus ∈ stBuses) {b : Nat}
    (hb : b ∉ stBuses) : ∀ T ∈ L, ∀ i ∈ T.interactions, i.bus ≠ b :=
  fun T hT i hi e => hb (e ▸ hL T hT i hi)

theorem no_send {L : List Table} (hL : ∀ T ∈ L, ∀ i ∈ T.interactions, i.bus ∈ stBuses) {b : Nat}
    (hb : b ∉ stBuses) : ∀ T ∈ L, sendsOn T.interactions b = false := by
  intro T hT
  cases h : sendsOn T.interactions b with
  | false => rfl
  | true =>
    obtain ⟨i, hi, hs⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    exact absurd hs.1 (no_bus hL hb T hT i hi)

section
variable {host : List (Nat × Bool × List Nat)} (hh : HostOK host) (prev post : NearSpec.Bytes) (n : Nat)
include hh

/-- `Prem.hx` / `ws_entries`' `hx`. -/
theorem x_hx : ∀ T ∈ m5bX host prev post n, ∀ i ∈ T.interactions,
    i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG ∧ i.bus ≠ B_TREE := by
  have h := x_buses hh prev post n
  intro T hT i hi
  exact ⟨no_bus h (by decide) T hT i hi, no_bus h (by decide) T hT i hi, no_bus h (by decide) T hT i hi,
    no_bus h (by decide) T hT i hi, no_bus h (by decide) T hT i hi⟩

/-- `Prem.hsil`. -/
theorem x_hsil : ∀ T ∈ m5bX host prev post n,
    sendsOn T.interactions B_NIB = false ∧ sendsOn T.interactions B_KLEN = false ∧
    sendsOn T.interactions B_ORD = false ∧ sendsOn T.interactions B_SHA_BYTES = false ∧
    sendsOn T.interactions B_SHA_DIGEST = false ∧ sendsOn T.interactions B_KC = false ∧
    sendsOn T.interactions B_KDIG = false := by
  have h := x_buses hh prev post n
  intro T hT
  exact ⟨no_send h (by decide) T hT, no_send h (by decide) T hT, no_send h (by decide) T hT,
    no_send h (by decide) T hT, no_send h (by decide) T hT, no_send h (by decide) T hT,
    no_send h (by decide) T hT⟩

/-- `air_final_sorted_sn2`'s `hxV`. -/
theorem x_hxV : ∀ T ∈ m5bX host prev post n, sendsOn T.interactions B_VER = false :=
  no_send (x_buses hh prev post n) (by decide)

/-- `air_final_sorted_sn2`'s `hr`. -/
theorem rest_hr : ∀ T ∈ m5bRest host, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP ∧ i.bus ≠ B_TCH := by
  have h := rest_buses hh
  intro T hT i hi
  refine ⟨no_bus h (by decide) T hT i hi, no_bus h (by decide) T hT i hi, ?_⟩
  -- `TCH` is only on the M5a tape, not on the rest
  intro e
  rcases List.mem_append.1 hT with hT | hT
  · have := of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 rest_noTCH T hT) i hi)
    exact this e
  · simp only [List.mem_singleton] at hT
    subst hT
    simp only [tapeTable, List.mem_map] at hi
    obtain ⟨x, hx, rfl⟩ := hi
    rcases hh x hx with h' | h' <;> simp_all [B_SREQ, B_HB, B_TCH, NUM_BUSES_WS, NUM_BUSES]
where
  rest_noTCH : (m5bExtra.all fun T => T.interactions.all fun i => decide (i.bus ≠ B_TCH)) = true := by decide

/-- `air_final_sorted_sn2`'s `hrN`. -/
theorem rest_hrN : ∀ T ∈ m5bRest host, sendsOn T.interactions B_NIB = false ∧
    sendsOn T.interactions B_KC = false ∧ sendsOn T.interactions B_KCR = false := by
  have h := rest_buses hh
  intro T hT
  exact ⟨no_send h (by decide) T hT, no_send h (by decide) T hT, no_send h (by decide) T hT⟩

/-- `air_final_sorted_sn2`'s `hrS`. -/
theorem rest_hrS : ∀ T ∈ m5bRest host, sendsOn T.interactions B_MATQ = false ∧
    sendsOn T.interactions B_MATR = false ∧ sendsOn T.interactions B_SIBQ = false ∧
    sendsOn T.interactions B_SIBA = false := by
  have h := rest_buses hh
  intro T hT
  exact ⟨no_send h (by decide) T hT, no_send h (by decide) T hT, no_send h (by decide) T hT,
    no_send h (by decide) T hT⟩

end

/-- **`FinalOrder.Prem` for the M5b AIR** from `Holds` and the semantic premises (chip contract,
`CompressOK`, `NodeCR`, `LeafCR`, `Sha256CR`, `1 ≤ D ≤ 20`): every static premise on the extra
tables holds. -/
theorem prem {tr : Trace Fp} {pub : List Fp} {D nb np : Nat} {compress : List Nat → List Nat → List Nat}
    {host : List (Nat × Bool × List Nat)} (hh : HostOK host) {prev post : NearSpec.Bytes} {n : Nat}
    (hH : Holds (fullAir D (m5bX host prev post n) nb np) pub tr)
    (hcomp : Sha512If.CompressOK compress)
    (hC : Sha512If.Sha512IfContract compress
      ((busList (fullAir D (m5bX host prev post n) nb np) tr pub B_IF384 true).map WsDecode.decIf))
    (hD1 : 1 ≤ D) (hD : D ≤ 20) (hNCR : Sha512If.NodeCR compress) (hLCR : WsKey.LeafCR compress)
    (hCR : Walk.Sha256CR) :
    Prem tr pub D (m5bX host prev post n) nb np compress :=
  { hH, hx := x_hx hh prev post n, hcomp, hC, hD1, hD, hNCR, hLCR, hCR, hsil := x_hsil hh prev post n }

end StateM5a.M5b

/-! Axiom audit of this module (kept here, not in `Audit.lean`). -/
#print axioms StateM5a.M5b.rest_buses
#print axioms StateM5a.M5b.x_buses
#print axioms StateM5a.M5b.x_hx
#print axioms StateM5a.M5b.x_hsil
#print axioms StateM5a.M5b.x_hxV
#print axioms StateM5a.M5b.rest_hr
#print axioms StateM5a.M5b.rest_hrN
#print axioms StateM5a.M5b.rest_hrS
#print axioms StateM5a.M5b.prem
