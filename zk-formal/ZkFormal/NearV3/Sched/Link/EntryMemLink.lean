import ZkFormal.NearV3.Sched.Link.MemLink

/-!
# ZkFormal.NearV3.Sched.Link.EntryMemLink — the process link with the memory discharged (stage B step 2)

`proc_link'` / `proc_core'` with their memory hypotheses `ReadOk` and `EntryMem` discharged by the
memory link (`MemCtx.read_ok`, `MemCtx.entry_mem`), and stage A's operand bounds `hK`, `hts`
derived (step 7):

* every pushed key is a scan READ value (`st.allowance[link]`) or a process `alOut ≤ alIn`, all
  `≤ 4,500,000`, and every pushed time stamp is a scan `cid < 2^16` or a process time
  `< T0 + 2^22` (`pushes_small`);
* each round key `K_i` and each entry time stamp is a pushed one (the `SPUSH` balance,
  `rounds_perm`, which does not use `hK`/`hts`), so `K_i, ts < 2^29` (`keys_ts`).

Remaining hypotheses of **`proc_link''`** / **`proc_core''`**: ownership (`SchedOwn`, `ScanOwn`,
`OpOwn`), public data (`ScanPub`, `RawOk`, `ParSmall`, the instance's `PubOk`-type bounds),
`htau`, `hseed` (stage A), `hInitVals` (`InitVals`) and `IsLOk` (missing constraint).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open NearSpecV3 NearSpecV3.Scheduler NearSpec

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tm tcmp ts tch tg tsd tcd f m : Nat}
  {P : InstPub} {allowed : Array Bool} {st : St}

namespace MemCtx
variable (C : MemCtx AP pub tr tp tm tcmp ts tch tg tsd tcd f m P allowed st)
include C

/-- The in-values of an entry are `≤ 4,500,000`, so is `alOut`. -/
theorem in_le {i : Nat} (hi : i < m) {j : Nat} (hj : j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr) :
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.sbIn ≤ 4500000 ∧
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rbIn ≤ 4500000 ∧
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alIn ≤ 4500000 ∧
    cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alOut ≤ 4500000 := by
  have hn := C.PO.n64
  obtain ⟨-, -, hs, hr', hl, -⟩ := C.ent hi hj
  obtain ⟨⟨o7, m7, t7, a7, v7⟩, ⟨o8, m8, t8, a8, v8⟩, ⟨o9, m9, t9, a9, v9⟩⟩ := C.slot_ops hi hj
  have y7 := C.mem_reads o7 m7
  have y8 := C.mem_reads o8 m8
  have y9 := C.mem_reads o9 m9
  rw [v7, t7, a7] at y7; rw [v8, t8, a8] at y8; rw [v9, t9, a9] at y9
  unfold simσ at y7 y8 y9
  rw [if_pos (QT_snd hn hs), rd_snd _ hn hs] at y7
  rw [if_pos (QT_rcv hn hr'), rd_rcv _ hn hr'] at y8
  rw [if_pos (QT_link hn hl), rd_link _ hn hl] at y9
  have hB := stAt_bnd P.n allowed tr tp f m st C.hB (cv tr tp (Proc.hdrAt tr tp f i) Proc.T + j)
  have b7 : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.sbIn ≤ 4500000 := by rw [y7]; exact (hB _).1
  have b8 : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.rbIn ≤ 4500000 := by rw [y8]; exact (hB _).2.1
  have b9 : cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.alIn ≤ 4500000 := by rw [y9]; exact (hB _).2.2
  obtain ⟨-, -, -, -, -, oL⟩ := grant_sem C.hH C.O C.OS C.I C.hτ C.SP C.PO C.hB C.hV C.hIL hi hj b7 b8 b9
  refine ⟨b7, b8, b9, ?_⟩
  rw [oL]; split <;> omega

/-- **The pushes**: keys `≤ 4,500,000`, time stamps `< T0 + 2^22`. -/
theorem pushes_small : ∀ p ∈ initPushes (reqsOf P) st ++ pushRec tr tp f m,
    p.key ≤ 4500000 ∧ p.ts < T0 + 2 ^ 22 := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · simp only [initPushes, List.mem_map, List.mem_range] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    have := C.PO.len16
    have hl := reqsOf_length C.PO
    exact ⟨(C.hB _).2.2, by simp only; unfold T0; omega⟩
  · simp only [pushRec, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter] at hp
    obtain ⟨i, hi, j, ⟨hj, -⟩, rfl⟩ := hp
    have hT := (C.I.hdr i hi).2
    have hHt := C.hHt
    exact ⟨(C.in_le hi hj).2.2.2, by simp only; omega⟩

/-- **`hK`, `hts`** from the pushes (step 7). -/
theorem keys_ts
    (hperm : (entriesOf (roundsOf tr tp f m)).Perm (initPushes (reqsOf P) st ++ pushRec tr tp f m)) :
    (∀ i, i < m → cv tr tp (Proc.hdrAt tr tp f i) Proc.K < 2 ^ 29) ∧
    (∀ i, i < m → ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ts < 2 ^ 29) := by
  have hent : ∀ i, i < m → ∀ j, j < cv tr tp (Proc.hdrAt tr tp f i) Proc.Lr →
      (⟨cv tr tp (Proc.hdrAt tr tp f i) Proc.K, cv tr tp (Proc.hdrAt tr tp f i) Proc.z,
        cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ts, cv tr tp (Proc.hdrAt tr tp f i + 1 + j) Proc.ein⟩ : PM) ∈
        initPushes (reqsOf P) st ++ pushRec tr tp f m := by
    intro i hi j hj
    apply hperm.subset
    unfold entriesOf roundsOf
    exact List.mem_flatMap.2 ⟨rOf tr tp f i, List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩,
      List.mem_map.2 ⟨_, List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩, rfl⟩⟩
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · have h1 := (Proc.round_shape C.hL C.hHt (C.I.hdr i hi).1.1 (C.I.hdr i hi).1.2.1).1
    have := (C.pushes_small _ (hent i hi 0 (by omega))).1
    simp only at this; omega
  · have := (C.pushes_small _ (hent i hi j hj)).2
    simp only at this; unfold T0 at this; omega

end MemCtx

end

/-- **The process phase of one instance, scan and memory links discharged.** -/
theorem proc_link'' {AP : AirP} {pub : List Fp} {tr : Trace Fp} (hH : HoldsP AP pub tr)
    {tp tm tcmp ts tch tg tsd tcd : Nat}
    (O : SchedOwn AP tp tm tcmp ts tch tg) (OS : ScanOwn AP tsd tp) (OO : OpOwn AP tp tsd tcd)
    (htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256)
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (I : Proc.Inst tr tp f m)
    -- the public data
    (P : InstPub) (SP : ScanPub AP pub (cv tr tp f Proc.tau) P) (PO : ScanPubOk P) (PS : ParSmall AP pub)
    -- the spec state
    (allowed : Array Bool) (st : St) (hst : st.rng = rngAt (procKey tr tp f) 0)
    (hsz : SzA P.n st) (hB : ABnd 4500000 st)
    -- the INIT values (codec / distribute stage) and the `isL` flags (missing constraint)
    (hV : InitVals AP tr pub (cv tr tp f Proc.tau) P.n allowed st)
    (hIL : IsLOk tr tm (cv tr tp f Proc.tau) P.n) :
    let rs := roundsOf tr tp f m
    simR P.n allowed (reqsOf P) rs T0 st = some (specSt P.n allowed (reqsOf P) tr tp f st m, pushRec tr tp f m) ∧
    (entriesOf rs).Perm (initPushes (reqsOf P) st ++ pushRec tr tp f m) ∧
    rs.Pairwise (fun R R' => before (R.key, R.z) (R'.key, R'.z)) ∧
    (∀ R ∈ rs, R.valid) ∧ (∀ R ∈ rs, R.ents ≠ []) ∧ TsOk T0 rs ∧
    processRequests P.n allowed st (reqsOf P) = some (specSt P.n allowed (reqsOf P) tr tp f st m) := by
  have C : MemCtx AP pub tr tp tm tcmp ts tch tg tsd tcd f m P allowed st :=
    ⟨hH, O, OS, OO, PS, htau, hf, hk, hc, I, SP, PO, hB, hsz, hV, hIL⟩
  have hτ : cv tr tp f Proc.tau < 2013265921 := cv_lt _ _
  obtain ⟨hinit, hinitOk⟩ := scan_init (tp := tp) hH OS SP PO hτ st C.read_ok
  have hperm := rounds_perm hH O.tp_lt O.tp_tab O.pushRecv O.pushPub hf hk hc I hinit hinitOk
  obtain ⟨hK, hts⟩ := C.keys_ts hperm
  exact proc_link' hH O OS htau hf hk hc I hK hts P SP PO allowed st hst hsz.2.2 C.read_ok
    (fun i hi j hj => C.entry_mem hi hj)

/-! ## The base state -/

theorem getElem!_map_le {α : Type} (xs : Array α) (g : α → Nat) {B : Nat} (h : ∀ x, g x ≤ B) (i : Nat) :
    (xs.map g)[i]! ≤ B := by
  rw [getElem!_def, Array.getElem?_map]
  cases xs[i]? with
  | none => exact Nat.zero_le _
  | some x => exact h x

theorem lpState_bnd (ids : List Nat) (hn : 1 ≤ ids.length) (p : Params)
    (hp : Params.calculate Config.pv86 ids.length = some p) (allowed : Array Bool) (a0 : Nat → Nat)
    (seed : Bytes) : ABnd 4500000 (lpState ids p allowed a0 seed) := by
  obtain ⟨hM, -, hA, -⟩ := pv86_facts hn hp
  intro x
  simp only [lpState, linkPass]
  refine ⟨getElem!_map_le _ _ (fun c => by omega) x, getElem!_map_le _ _ (fun c => by omega) x,
    getElem!_map_le _ _ (fun l => ?_) x⟩
  have : Nat.min ((srcArr ids a0)[l]! + p.maxShardBandwidth / ids.length) p.maxAllowance ≤ p.maxAllowance :=
    Nat.min_le_right _ _
  split <;> omega

theorem lpState_szA (ids : List Nat) (p : Params) (allowed : Array Bool) (a0 : Nat → Nat) (seed : Bytes) :
    SzA ids.length (lpState ids p allowed a0 seed) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [lpState, linkPass]

/-- **The scheduler core with the process phase of one instance, scan and memory links
discharged** (`core_compose` with the instance's public data `P` and
`st = lpState P.ids P.params P.allowed a0 P.seed`). -/
theorem proc_core'' {AP : AirP} {pub : List Fp} {tr : Trace Fp} (hH : HoldsP AP pub tr)
    {tp tm tcmp ts tch tg tsd tcd : Nat}
    (O : SchedOwn AP tp tm tcmp ts tch tg) (OS : ScanOwn AP tsd tp) (OO : OpOwn AP tp tsd tcd)
    (htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256)
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (I : Proc.Inst tr tp f m)
    -- the instance's public data
    (P : InstPub) (hn : 1 ≤ P.ids.length) (hn64 : P.ids.length ≤ 64) (hids : ∀ x ∈ P.ids, x < 2 ^ 64)
    (hp : Params.calculate Config.pv86 P.ids.length = some P.params)
    (hA : P.allowed.size = P.ids.length * P.ids.length) (RO : RawOk P)
    (SP : ScanPub AP pub (cv tr tp f Proc.tau) P) (PS : ParSmall AP pub)
    (prev : Option NearSpec.Bytes) (a0 : Nat → Nat) (h0 : NearSpec.Bytes) (hprev : PrevCanon P.ids prev a0 h0)
    (hseed : procKey tr tp f = leWords P.seed)
    -- the INIT values (codec / distribute stage) and the `isL` flags (missing constraint)
    (hV : InitVals AP tr pub (cv tr tp f Proc.tau) P.ids.length P.allowed
      (lpState P.ids P.params P.allowed a0 P.seed))
    (hIL : IsLOk tr tm (cv tr tp f Proc.tau) P.ids.length) :
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
  have PO := ScanPubOk.of_pv86 hp hn64 RO
  have C : MemCtx AP pub tr tp tm tcmp ts tch tg tsd tcd f m P P.allowed
      (lpState P.ids P.params P.allowed a0 P.seed) :=
    ⟨hH, O, OS, OO, PS, htau, hf, hk, hc, I, SP, PO, lpState_bnd P.ids hn P.params hp P.allowed a0 P.seed,
      lpState_szA P.ids P.params P.allowed a0 P.seed, hV, hIL⟩
  have hτ : cv tr tp f Proc.tau < 2013265921 := cv_lt _ _
  obtain ⟨hinit, hinitOk⟩ := scan_init (tp := tp) hH OS SP PO hτ
    (lpState P.ids P.params P.allowed a0 P.seed) C.read_ok
  have hperm := rounds_perm hH O.tp_lt O.tp_tab O.pushRecv O.pushPub hf hk hc I hinit hinitOk
  obtain ⟨hK, hts⟩ := C.keys_ts hperm
  exact proc_core' hH O OS htau hf hk hc I hK hts P hn hn64 hids hp hA RO SP prev a0 h0 hprev hseed
    C.read_ok (fun i hi j hj => C.entry_mem hi hj)

end ZkFormal.NearV3.Sched
