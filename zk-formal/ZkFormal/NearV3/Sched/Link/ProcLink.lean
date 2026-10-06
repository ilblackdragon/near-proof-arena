import ZkFormal.NearV3.Sched.Link.ProcStep
import ZkFormal.NearV3.Sched.Spec.Compose

/-!
# ZkFormal.NearV3.Sched.Link.ProcLink — the process phase of one instance (M3 link, stage A)

`SchedOwn`: the bus ownership the process link uses (STATUS-V3-SCHED §6.1): `sprV3` is table
`tp`, the memory (`MemOwn`) and comparator (`CmpOwn`) contracts, lane v3-chacha's shuffle tables
(`ShufOwn`), `sprV3` the only receiver on `SPUSH` and `SINC`, no public segment on either.

**`proc_link`**: for an instance with key block `f` and `m` rounds (`Proc.Inst`, which exists by
`Proc.inst_exists`), the recorded rounds `rs = roundsOf tr tp f m` satisfy every hypothesis of
`process_rounds` from `t₀ = T0` (`hord`, `hval`, `hne`, `hts`, `hperm`, `hsim` with
`ps = pushRec`), hence `processRequests n allowed st reqs = some (specSt … m)`.

**`proc_core`**: the same with `st = lpState ids p allowed a0 seed` plugged into `core_compose`.

Named hypotheses (obligations of the other link stages):
* `htau` — every active process row has `τ < 256` (public key records `τ < 32`);
* `hK`, `hts` — operand bounds `K_i < 2^29`, `ts < 2^29` (§10: allowances, time stamps);
* `hlen` — `|reqs| ≤ T0 = 2^20`;
* `hinit`, `hinitOk` — the `SPUSH` messages of the other tables (the scan) with this τ are the
  initial pushes, fields `< P` (scan global view; `initMsgs_eq` gives the form from the scan's
  end-row pushes and the `READ` values `key_cid = st.allowance[link_cid]`);
* `hkey` / `hseed` — the instance's ChaCha key (from its public key records) is the seed's;
* `hE` — `EntryOk` for every entry: memory consistency (`sbIn, rbIn, alIn` = spec state, via
  `mem_reads_sim`), GRANT outcomes (`cS, cR, cL, alOut`), `INC` values (scan link).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open NearSpecV3 NearSpecV3.Scheduler NearSpec

/-- Bus ownership used by the process link. -/
structure SchedOwn (AP : AirP) (tp tm tcmp ts tch tg : Nat) : Prop where
  tp_lt : tp < AP.tables.length
  tp_tab : AP.tables[tp]! = Proc.table
  mem : MemOwn AP tm
  cmp : CmpOwn AP tcmp
  shuf : ShufOwn AP tp ts tch tg
  pushRecv : ∀ t, t < AP.tables.length → t ≠ tp → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SPUSH → i.send = true
  pushPub : ∀ seg ∈ AP.pubSegs, seg.bus ≠ B_SPUSH
  incRecv : ∀ t, t < AP.tables.length → t ≠ tp → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SINC → i.send = true
  incPub : ∀ seg ∈ AP.pubSegs, seg.bus ≠ B_SINC

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

theorem flatMap_range_congr {β : Type} {m : Nat} {g h : Nat → List β} (e : ∀ i, i < m → g i = h i) :
    (List.range m).flatMap g = (List.range m).flatMap h :=
  flatMap_congr' fun i hi => e i (List.mem_range.1 hi)

/-- **The process phase of one instance satisfies `process_rounds`.** -/
theorem proc_link (hH : HoldsP AP pub tr) {tp tm tcmp ts tch tg : Nat}
    (O : SchedOwn AP tp tm tcmp ts tch tg)
    (htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256)
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (I : Proc.Inst tr tp f m)
    -- operand bounds
    (hK : ∀ i, i < m → cv tr tp (Proc.hdrAt tr tp f i) Proc.K < 2 ^ 29)
    (hts : ∀ i, i < m → ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ts < 2 ^ 29)
    -- the spec side
    (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hR : ∀ q ∈ reqs, q.incs ≠ [] ∧ q.incs.length < 64) (hlen : reqs.length ≤ T0)
    (st : St) (hst : st.rng = rngAt (procKey tr tp f) 0)
    -- the initial pushes (scan)
    (hinit : ((pushOther AP tr pub tp).filter (headIs (cv tr tp f Proc.tau))).Perm
      ((initPushes reqs st).map (pmMsg (cv tr tp f Proc.tau))))
    (hinitOk : ∀ p ∈ initPushes reqs st, PMOk p)
    -- the steps (memory, scan)
    (hE : ∀ i, i < m → ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      EntryOk n allowed reqs tr tp f st i j) :
    let rs := roundsOf tr tp f m
    simR n allowed reqs rs T0 st = some (specSt n allowed reqs tr tp f st m, pushRec tr tp f m) ∧
    (entriesOf rs).Perm (initPushes reqs st ++ pushRec tr tp f m) ∧
    rs.Pairwise (fun R R' => before (R.key, R.z) (R'.key, R'.z)) ∧
    (∀ R ∈ rs, R.valid) ∧ (∀ R ∈ rs, R.ents ≠ []) ∧ TsOk T0 rs ∧
    processRequests n allowed st reqs = some (specSt n allowed reqs tr tp f st m) := by
  intro rs
  have hL := pLocal_of hH O.tp_lt O.tp_tab
  have hHt := proc_height hH O.tp_lt O.tp_tab
  have hR' : ∀ q ∈ reqs, q.incs.length < 64 := fun q h => (hR q h).2
  have hsim0 := proc_sim hH O.tp_lt O.tp_tab O.shuf htau hf hk hc I n allowed reqs hR' st hst
  have hpush : (List.range m).flatMap (specPush n allowed reqs tr tp f st) = pushRec tr tp f m := by
    rw [pushRec_eq]
    exact flatMap_range_congr fun i hi => round_push hL hHt I n allowed reqs st hi (hE i hi)
  rw [hpush] at hsim0
  have hperm := rounds_perm hH O.tp_lt O.tp_tab O.pushRecv O.pushPub hf hk hc I hinit hinitOk
  have hord := rounds_ord hH O.cmp O.tp_lt O.tp_tab I hK
  have hval := rounds_valid hL hHt I
  have hne := rounds_ne hL hHt I
  have htsok := rounds_ts hH O.cmp O.tp_lt O.tp_tab I hts
  exact ⟨hsim0, hperm, hord, hval, hne, htsok,
    process_rounds n allowed reqs hR rs st _ _ T0 hlen hsim0 hperm hord hval hne htsok⟩

/-- **The scheduler core with the process phase of one instance** (`core_compose` with
`st = lpState ids p allowed a0 seed`). -/
theorem proc_core (hH : HoldsP AP pub tr) {tp tm tcmp ts tch tg : Nat}
    (O : SchedOwn AP tp tm tcmp ts tch tg)
    (htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256)
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (I : Proc.Inst tr tp f m)
    (hK : ∀ i, i < m → cv tr tp (Proc.hdrAt tr tp f i) Proc.K < 2 ^ 29)
    (hts : ∀ i, i < m → ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ts < 2 ^ 29)
    -- the codec side (`core_compose`)
    (ids : List Nat) (hn : 1 ≤ ids.length) (hn64 : ids.length ≤ 64) (hids : ∀ x ∈ ids, x < 2 ^ 64)
    (p : Params) (hp : Params.calculate Config.pv86 ids.length = some p)
    (allowed : Array Bool) (hA : allowed.size = ids.length * ids.length)
    (reqs : List Req) (seed ash : NearSpec.Bytes)
    (prev : Option NearSpec.Bytes) (a0 : Nat → Nat) (h0 : NearSpec.Bytes) (hprev : PrevCanon ids prev a0 h0)
    (hR : ∀ q ∈ reqs, q.incs ≠ [] ∧ q.incs.length < 64) (hlen : reqs.length ≤ T0)
    (hseed : procKey tr tp f = leWords seed)
    (hinit : ((pushOther AP tr pub tp).filter (headIs (cv tr tp f Proc.tau))).Perm
      ((initPushes reqs (lpState ids p allowed a0 seed)).map (pmMsg (cv tr tp f Proc.tau))))
    (hinitOk : ∀ q ∈ initPushes reqs (lpState ids p allowed a0 seed), PMOk q)
    (hE : ∀ i, i < m → ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      EntryOk ids.length allowed reqs tr tp f (lpState ids p allowed a0 seed) i j) :
    let n := ids.length
    let stF := specSt ids.length allowed reqs tr tp f (lpState ids p allowed a0 seed) m
    coreOf ids p allowed reqs seed ash prev = some
      ⟨NearSpec.Bandwidth.State.encode
          ⟨canonLinks ids (fun l => stF.allowance[l]!), sha256 (h0 ++ ash)⟩,
        (List.range (n * n)).map (fun l => ((ids.getD (l / n) 0, ids.getD (l % n) 0),
          (applyGrants n stF (gridGrants n allowed stF.senderBudget stF.receiverBudget
            (sordOf n allowed stF.senderBudget)
            (rordOf n allowed stF.receiverBudget))).granted[l]!)),
        p⟩ := by
  intro n stF
  have hst : (lpState ids p allowed a0 seed).rng = rngAt (procKey tr tp f) 0 := by
    rw [hseed]; exact ofSeed_eq seed
  obtain ⟨hsim, hperm, hord, hval, hne, htsok, -⟩ :=
    proc_link hH O htau hf hk hc I hK hts ids.length allowed reqs hR hlen _ hst hinit hinitOk hE
  exact core_compose ids hn hn64 hids p hp allowed hA reqs seed ash prev a0 h0 hprev hR
    (roundsOf tr tp f m) stF (pushRec tr tp f m) T0 hlen hsim hperm hord hval hne htsok

end ZkFormal.NearV3.Sched
