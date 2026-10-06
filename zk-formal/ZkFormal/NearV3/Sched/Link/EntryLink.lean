import ZkFormal.NearV3.Sched.Link.EntryInc

/-!
# ZkFormal.NearV3.Sched.Link.EntryLink — the process link with the scan discharged (stage B)

`proc_link` / `proc_core` (stage A) with the request list fixed to the public one,
`reqs = reqsOf P = convRaw P.params P.n P.raw`, and the hypotheses discharged by the scan link:

* `hR` (increases non-empty, `< 64`) and `hlen` (`|reqs| ≤ T0`) from `ScanPubOk`;
* `hinit`, `hinitOk` from `scan_init` (given `ReadOk`);
* the `INC` part of `EntryOk` (`incs`, `link`, `eout1`) from `entry_inc`, and `size` from the
  allowance size (`stepSt_asz`).

Remaining: `ReadOk` and `EntryMem` (memory link), plus the stage-A operand bounds and `htau`,
`hseed`.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open NearSpecV3 NearSpecV3.Scheduler NearSpec

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

theorem reqsOf_ok {P : InstPub} (PO : ScanPubOk P) :
    ∀ q ∈ reqsOf P, q.incs ≠ [] ∧ q.incs.length < 64 := by
  intro q hq
  rw [reqsOf, convRaw_eq _ _ _ (fun q hq => (PO.raw q hq).2.2)] at hq
  obtain ⟨q0, hq0, rfl⟩ := List.mem_map.1 hq
  exact ⟨(PO.raw q0 hq0).2.2, Nat.lt_of_le_of_lt (incsOf_length_le _ _) (by decide)⟩

theorem reqsOf_len {P : InstPub} (PO : ScanPubOk P) : (reqsOf P).length ≤ T0 := by
  rw [reqsOf_length PO]; have := PO.len16; unfold T0; omega

theorem EntryOk.of_mem {n : Nat} {allowed : Array Bool} {reqs : List Req} {tp f : Nat} {st : St}
    {i j : Nat}
    (hinc : (∃ rest, (reqAt reqs (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout)).incs =
        cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.inc :: rest ∧
      (rest = [] ↔ cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rem = 0)) ∧
      (reqAt reqs (cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout)).link =
        cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link ∧
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.eout + 1 < 2013265921 ∧
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.link < n * n)
    (hsz : st.allowance.size = n * n) (hM : EntryMem n allowed reqs tr tp f st i j) :
    EntryOk n allowed reqs tr tp f st i j := by
  obtain ⟨h1, h2, h3, h4⟩ := hinc
  exact ⟨h1, h2, h3, by rw [stepSt_asz, hsz]; exact h4, hM.sIn, hM.rIn, hM.aIn, hM.cS, hM.cR,
    hM.cL, hM.aOut⟩

/-- **The process phase of one instance, scan link discharged.** -/
theorem proc_link' (hH : HoldsP AP pub tr) {tp tm tcmp ts tch tg tsd : Nat}
    (O : SchedOwn AP tp tm tcmp ts tch tg) (OS : ScanOwn AP tsd tp)
    (htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256)
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (I : Proc.Inst tr tp f m)
    (hK : ∀ i, i < m → cv tr tp (Proc.hdrAt tr tp f i) Proc.K < 2 ^ 29)
    (hts : ∀ i, i < m → ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ts < 2 ^ 29)
    -- the public requests
    (P : InstPub) (SP : ScanPub AP pub (cv tr tp f Proc.tau) P) (PO : ScanPubOk P)
    -- the spec state
    (allowed : Array Bool) (st : St) (hst : st.rng = rngAt (procKey tr tp f) 0)
    (hsz : st.allowance.size = P.n * P.n)
    -- memory link
    (hRd : ReadOk AP tr pub (cv tr tp f Proc.tau) (reqsOf P).length st)
    (hEM : ∀ i, i < m → ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      EntryMem P.n allowed (reqsOf P) tr tp f st i j) :
    let rs := roundsOf tr tp f m
    simR P.n allowed (reqsOf P) rs T0 st = some (specSt P.n allowed (reqsOf P) tr tp f st m, pushRec tr tp f m) ∧
    (entriesOf rs).Perm (initPushes (reqsOf P) st ++ pushRec tr tp f m) ∧
    rs.Pairwise (fun R R' => before (R.key, R.z) (R'.key, R'.z)) ∧
    (∀ R ∈ rs, R.valid) ∧ (∀ R ∈ rs, R.ents ≠ []) ∧ TsOk T0 rs ∧
    processRequests P.n allowed st (reqsOf P) = some (specSt P.n allowed (reqsOf P) tr tp f st m) := by
  have hτ : cv tr tp f Proc.tau < 2013265921 := cv_lt _ _
  obtain ⟨hinit, hinitOk⟩ := scan_init (tp := tp) hH OS SP PO hτ st hRd
  exact proc_link hH O htau hf hk hc I hK hts P.n allowed (reqsOf P) (reqsOf_ok PO) (reqsOf_len PO)
    st hst hinit hinitOk (fun i hi j hj =>
      EntryOk.of_mem (entry_inc hH O OS SP PO I rfl hi hj) hsz (hEM i hi j hj))

/-- The public bounds of an instance that do not follow from the parameters. -/
structure RawOk (P : InstPub) : Prop where
  len16 : P.raw.length ≤ 2 ^ 16
  raw : ∀ q ∈ P.raw, q.s < P.n ∧ q.r < P.n ∧ incsOf P.params q.bm ≠ []

theorem ScanPubOk.of_pv86 {P : InstPub} (hp : Params.calculate Config.pv86 P.ids.length = some P.params)
    (hn64 : P.ids.length ≤ 64) (R : RawOk P) : ScanPubOk P := by
  obtain ⟨hb, hg⟩ := pv86_base_le hp
  exact ⟨by omega, by rw [hg]; omega, hn64, R.len16, R.raw⟩

theorem lpState_asz (ids : List Nat) (p : Params) (allowed : Array Bool) (a0 : Nat → Nat) (seed : Bytes) :
    (lpState ids p allowed a0 seed).allowance.size = ids.length * ids.length := by
  simp [lpState, linkPass]

/-- **The scheduler core with the process phase of one instance, scan link discharged**
(`core_compose` with the instance's public data `P` and `st = lpState P.ids P.params P.allowed a0
P.seed`). -/
theorem proc_core' (hH : HoldsP AP pub tr) {tp tm tcmp ts tch tg tsd : Nat}
    (O : SchedOwn AP tp tm tcmp ts tch tg) (OS : ScanOwn AP tsd tp)
    (htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256)
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (I : Proc.Inst tr tp f m)
    (hK : ∀ i, i < m → cv tr tp (Proc.hdrAt tr tp f i) Proc.K < 2 ^ 29)
    (hts : ∀ i, i < m → ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ts < 2 ^ 29)
    -- the instance's public data
    (P : InstPub) (hn : 1 ≤ P.ids.length) (hn64 : P.ids.length ≤ 64) (hids : ∀ x ∈ P.ids, x < 2 ^ 64)
    (hp : Params.calculate Config.pv86 P.ids.length = some P.params)
    (hA : P.allowed.size = P.ids.length * P.ids.length) (RO : RawOk P)
    (SP : ScanPub AP pub (cv tr tp f Proc.tau) P)
    (prev : Option NearSpec.Bytes) (a0 : Nat → Nat) (h0 : NearSpec.Bytes) (hprev : PrevCanon P.ids prev a0 h0)
    (hseed : procKey tr tp f = leWords P.seed)
    -- memory link
    (hRd : ReadOk AP tr pub (cv tr tp f Proc.tau) (reqsOf P).length
      (lpState P.ids P.params P.allowed a0 P.seed))
    (hEM : ∀ i, i < m → ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      EntryMem P.ids.length P.allowed (reqsOf P) tr tp f (lpState P.ids P.params P.allowed a0 P.seed) i j) :
    let n := P.ids.length
    let stF := specSt P.ids.length P.allowed (reqsOf P) tr tp f (lpState P.ids P.params P.allowed a0 P.seed) m
    coreOf P.ids P.params P.allowed (reqsOf P) P.seed P.ash prev = some
      ⟨NearSpec.Bandwidth.State.encode
          ⟨canonLinks P.ids (fun l => stF.allowance[l]!), sha256 (h0 ++ P.ash)⟩,
        (List.range (n * n)).map (fun l => ((P.ids.getD (l / n) 0, P.ids.getD (l % n) 0),
          (applyGrants n stF (gridGrants n P.allowed stF.senderBudget stF.receiverBudget
            (sordOf n P.allowed stF.senderBudget)
            (rordOf n P.allowed stF.receiverBudget))).granted[l]!)),
        P.params⟩ := by
  intro n stF
  have PO := ScanPubOk.of_pv86 hp hn64 RO
  have hτ : cv tr tp f Proc.tau < 2013265921 := cv_lt _ _
  obtain ⟨hinit, hinitOk⟩ := scan_init (tp := tp) hH OS SP PO hτ
    (lpState P.ids P.params P.allowed a0 P.seed) hRd
  exact proc_core hH O htau hf hk hc I hK hts P.ids hn hn64 hids P.params hp P.allowed hA
    (reqsOf P) P.seed P.ash prev a0 h0 hprev (reqsOf_ok PO) (reqsOf_len PO) hseed hinit hinitOk
    (fun i hi j hj => EntryOk.of_mem (entry_inc hH O OS SP PO I rfl hi hj)
      (lpState_asz _ _ _ _ _) (hEM i hi j hj))

end ZkFormal.NearV3.Sched
