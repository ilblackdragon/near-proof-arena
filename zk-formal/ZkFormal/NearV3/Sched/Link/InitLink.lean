import ZkFormal.NearV3.Sched.Link.InitVals
import ZkFormal.NearV3.Sched.Link.EntryMemLink

/-!
# ZkFormal.NearV3.Sched.Link.InitLink — the process link with `InitVals` and the public data discharged (stage C)

`proc_link''` / `proc_core''` with:
* `hV : InitVals …` discharged by **`InitCtx.initVals_of`** (codec and distribute views), at
  `st = lpState P.ids P.params P.allowed (codecA0 tr tcd τ) P.seed`: the previous allowances are the
  ones τ's codec block decodes from its pre bytes (`preA0`, `codec_pre_encode`);
* `htau` by `proc_htau`, `hseed` by `proc_hseed` (`SPUBB` key records, `PubbOwn`);
* `ScanPub` by `scanPub_of_idx` and `ParSmall` by `parSmall_of_idx` (`SPAR`, `PubIdx`);
* the instance facts by `InstOk` (`prepD0`).

Remaining hypotheses of **`proc_core'''`**: ownership (`SchedOwn`, `ScanOwn`, `OpOwn`,
`CodecValOwn`, `SparOwn`, `PubbOwn`, `InitOwn`), `PubIdx` with `render`'s `SPAR` and `SPUBB` records,
`prepD0` facts (`|Ps| ≤ 256`, `InstOk` per instance), and `hprev` (the previous state `prev`
is the canonical encoding of the codec's `a0` with hash `h0`; codec-encoding stage).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open NearSpecV3 NearSpecV3.Scheduler NearSpec

/-- **The process phase of one instance, all links discharged.** -/
theorem proc_link''' {AP : AirP} {pub : List Fp} {tr : Trace Fp} (hH : HoldsP AP pub tr)
    {tp tm tcmp ts tch tg tsd tcd : Nat}
    -- ownership (decidable on the final AIR)
    (O : SchedOwn AP tp tm tcmp ts tch tg) (OS : ScanOwn AP tsd tp) (OO : OpOwn AP tp tsd tcd)
    (OC : CodecValOwn AP tcd) (SO : SparOwn AP) (PB : PubbOwn AP) (IO : InitOwn AP tcd tsd)
    -- the public records (`PubIdx`, R1) and the `prepD0` facts
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrecP : I.recs B_SPAR true = (render Ps fwd).par) (hrecB : I.recs B_SPUBB true = (render Ps fwd).pubb)
    (h256 : Ps.length ≤ 256) (hP : ∀ τ, τ < Ps.length → InstOk (Ps.getD τ instD))
    -- the instance block
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (Ib : Proc.Inst tr tp f m) :
    let P := Ps.getD (cv tr tp f Proc.tau) instD
    let st := lpState P.ids P.params P.allowed (codecA0 tr tcd (cv tr tp f Proc.tau)) P.seed
    let rs := roundsOf tr tp f m
    simR P.n P.allowed (reqsOf P) rs T0 st = some (specSt P.n P.allowed (reqsOf P) tr tp f st m, pushRec tr tp f m) ∧
    (entriesOf rs).Perm (initPushes (reqsOf P) st ++ pushRec tr tp f m) ∧
    rs.Pairwise (fun R R' => before (R.key, R.z) (R'.key, R'.z)) ∧
    (∀ R ∈ rs, R.valid) ∧ (∀ R ∈ rs, R.ents ≠ []) ∧ TsOk T0 rs ∧
    processRequests P.n P.allowed st (reqsOf P) = some (specSt P.n P.allowed (reqsOf P) tr tp f st m) := by
  intro P st
  have hlen : Ps.length < 2013265921 := by omega
  have hτs := proc_htau hH O.tp_lt O.tp_tab PB I Ps fwd hrecB hlen
  have htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256 :=
    fun w hw ha => by have := hτs w hw ha; omega
  have hτ : cv tr tp f Proc.tau < Ps.length :=
    hτs f hf (Proc.act_of (pLocal_of hH O.tp_lt O.tp_tab) hf (Or.inl hk))
  have PO : InstOk P := hP _ hτ
  have SP := scanPub_of_idx I Ps fwd hrecP hlen hτ
  have PS := parSmall_of_idx I Ps fwd hrecP h256 (fun τ h => ⟨(hP τ h).raw, (hP τ h).n64⟩)
  have hseed := proc_hseed hH O.tp_lt O.tp_tab PB I Ps fwd hrecB hlen hf hk hc PO.seed32
  have C : InitCtx AP pub tr tp tm tcmp ts tch tg tsd tcd Ps := ⟨hH, O, OS, OO, OC, SO, IO, h256, hP⟩
  have hV := C.initVals_of I fwd hrecP hτ
  have hst : st.rng = rngAt (procKey tr tp f) 0 := by
    show (Rng.ofSeed P.seed) = _
    rw [hseed]; exact (ofSeed_eq P.seed)
  exact proc_link'' hH O OS OO htau hf hk hc Ib P SP (ScanPubOk.of_pv86 PO.params PO.n64 PO.raw) PS
    P.allowed st hst (lpState_szA P.ids P.params P.allowed _ P.seed)
    (lpState_bnd P.ids PO.n1 P.params PO.params P.allowed _ P.seed) hV

/-- **The scheduler core with the process phase of one instance, all links discharged**
(`core_compose` with `P = Ps[τ]` and `st = lpState P.ids P.params P.allowed a0 P.seed`, where `a0`
is the previous allowance decoded by τ's codec block). -/
theorem proc_core''' {AP : AirP} {pub : List Fp} {tr : Trace Fp} (hH : HoldsP AP pub tr)
    {tp tm tcmp ts tch tg tsd tcd : Nat}
    -- ownership (decidable on the final AIR)
    (O : SchedOwn AP tp tm tcmp ts tch tg) (OS : ScanOwn AP tsd tp) (OO : OpOwn AP tp tsd tcd)
    (OC : CodecValOwn AP tcd) (SO : SparOwn AP) (PB : PubbOwn AP) (IO : InitOwn AP tcd tsd)
    -- the public records (`PubIdx`, R1) and the `prepD0` facts
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrecP : I.recs B_SPAR true = (render Ps fwd).par) (hrecB : I.recs B_SPUBB true = (render Ps fwd).pubb)
    (h256 : Ps.length ≤ 256) (hP : ∀ τ, τ < Ps.length → InstOk (Ps.getD τ instD))
    -- the instance block
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (Ib : Proc.Inst tr tp f m)
    -- the previous state (codec-encoding stage)
    (prev : Option NearSpec.Bytes) (h0 : NearSpec.Bytes)
    (hprev : PrevCanon (Ps.getD (cv tr tp f Proc.tau) instD).ids prev
      (codecA0 tr tcd (cv tr tp f Proc.tau)) h0) :
    let P := Ps.getD (cv tr tp f Proc.tau) instD
    let a0 := codecA0 tr tcd (cv tr tp f Proc.tau)
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
  intro P a0
  have hlen : Ps.length < 2013265921 := by omega
  have hτs := proc_htau hH O.tp_lt O.tp_tab PB I Ps fwd hrecB hlen
  have htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256 :=
    fun w hw ha => by have := hτs w hw ha; omega
  have hτ : cv tr tp f Proc.tau < Ps.length :=
    hτs f hf (Proc.act_of (pLocal_of hH O.tp_lt O.tp_tab) hf (Or.inl hk))
  have PO : InstOk P := hP _ hτ
  have SP := scanPub_of_idx I Ps fwd hrecP hlen hτ
  have PS := parSmall_of_idx I Ps fwd hrecP h256 (fun τ h => ⟨(hP τ h).raw, (hP τ h).n64⟩)
  have hseed := proc_hseed hH O.tp_lt O.tp_tab PB I Ps fwd hrecB hlen hf hk hc PO.seed32
  have C : InitCtx AP pub tr tp tm tcmp ts tch tg tsd tcd Ps := ⟨hH, O, OS, OO, OC, SO, IO, h256, hP⟩
  have hV := C.initVals_of I fwd hrecP hτ
  exact proc_core'' hH O OS OO htau hf hk hc Ib P PO.n1 PO.n64 PO.ids64 PO.params PO.asz PO.raw SP PS
    prev a0 h0 hprev hseed hV

end ZkFormal.NearV3.Sched
