import ZkFormal.NearV3.Sched.Link.SoundProc

/-!
# ZkFormal.NearV3.Sched.Link.Sound — `schedCore_sound` (stage D)

For a `HoldsP` trace of a v2 AIR with the scheduler tables, the ownership conditions, the public
records of `render (p.sched.map instOf) fwd` (`PubIdx`, R1) and a successful `prepD0 cb hint = .ok p`:
for every instance τ `< |p.sched|`, with `sp = p.sched[τ]`, `n = |sp.ids|`:

* `runCore sp (prevOf τ) = some ⟨svOf τ (as bytes), grants, sp.params⟩`: the previous state the core
  reads is the codec's `VBYTES` bytes (`prevOf`, `pvOf_vbytes`), and the new `0x0f` value is exactly
  the bytes the codec sends on `SPOST` (`svOf`, `codec_schedVal`);
* `svOf τ` are bytes and the previous state is canonical (`PrevCanon`, `codec_prevCanon`);
* the grants are `((ids[l / n], ids[l % n]), stF.granted[l] + grid[l])` for `l < n²`, each
  `≤ 4,500,000` (unsaturated, `core_granted`), where `stF` is the spec's final process state of
  τ's process block (`specSt … m`) and `grid = gridGrants …` (sorted by `sordOf` / `rordOf`).

Hypotheses beyond the trace: ownership (`SchedOwn`, `ScanOwn`, `OpOwn`, `CodecValOwn`, `SparOwn`,
`PubbOwn`, `InitOwn`, **`SdlOwn`**, **`PubbRecv`**, **`ShaOwn`**; decidable), `PubIdx` with the `SPAR`,
`SPUBB` and `SDL` (send) records of `render`, `prepD0 cb hint = .ok p`, and two flagged ones:
`ShaKind` (the cross-lane kind registry: no other `BYTES` sender uses kind 11) and `hids64`
(shard ids `< 2^64`; prepD0-derivable from `decodeLayout`'s `pU64`, not yet proved).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

theorem getD_map_instOf (L : List SchedPub) {τ : Nat} (hτ : τ < L.length) :
    (L.map instOf).getD τ instD = instOf L[τ] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hτ]; rfl

/-- The per-instance `prepD0` facts. -/
theorem instOk_of {cb : NearSpec.Bytes} {hint : Hint} {p : Prep} (hprep : prepD0 cb hint = .ok p)
    (hids64 : ∀ sp ∈ p.sched, ∀ x ∈ sp.ids, x < 2 ^ 64) :
    ∀ τ, τ < (p.sched.map instOf).length → InstOk ((p.sched.map instOf).getD τ instD) := by
  intro τ hτ
  rw [List.length_map] at hτ
  rw [getD_map_instOf _ hτ]
  have hm := List.getElem_mem hτ
  have S := prepD0_sched hprep _ hm
  exact ⟨S.n1, S.n64, S.params, prepD0_asz hprep _ hm, hids64 _ hm, prepD0_rawOk hprep _ hm,
    prepD0_seed hprep _ hm⟩

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

/-- **`schedCore_sound`.** -/
theorem schedCore_sound (hH : HoldsP AP pub tr) {tp tm tcmp ts tch tg tsd tcd tsha : Nat}
    -- ownership (decidable on the final AIR)
    (O : SchedOwn AP tp tm tcmp ts tch tg) (OS : ScanOwn AP tsd tp) (OO : OpOwn AP tp tsd tcd)
    (OC : CodecValOwn AP tcd) (SO : SparOwn AP) (PB : PubbOwn AP) (IO : InitOwn AP tcd tsd)
    (DO : SdlOwn AP tcd) (PR : PubbRecv AP tp tcd) (SH : ShaOwn AP tsha)
    -- the kind registry (cross-lane)
    (SK : ShaKind AP pub tr tcd)
    -- the prepared statement and the public records (`PubIdx`, R1)
    {cb : NearSpec.Bytes} {hint : Hint} {p : Prep} (hprep : prepD0 cb hint = .ok p)
    (hids64 : ∀ sp ∈ p.sched, ∀ x ∈ sp.ids, x < 2 ^ 64)
    (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat))
    (hrecP : I.recs B_SPAR true = (render (p.sched.map instOf) fwd).par)
    (hrecB : I.recs B_SPUBB true = (render (p.sched.map instOf) fwd).pubb)
    (hrecD : I.recs B_SDL true = (render (p.sched.map instOf) fwd).dlSend)
    {τ : Nat} (hτ : τ < p.sched.length) :
    let sp := p.sched[τ]
    let n := sp.ids.length
    ∃ f m, f < tr.height tp ∧ cv tr tp f Proc.kK = 1 ∧ cv tr tp f Proc.kc = 0 ∧
      cv tr tp f Proc.tau = τ ∧ Proc.Inst tr tp f m ∧
      let stF := specSt n sp.allowed (reqsOf (instOf sp)) tr tp f
        (lpState sp.ids sp.params sp.allowed (codecA0 tr tcd τ) sp.seed) m
      let g := gridGrants n sp.allowed stF.senderBudget stF.receiverBudget
        (sordOf n sp.allowed stF.senderBudget) (rordOf n sp.allowed stF.receiverBudget)
      runCore sp (prevOf tr tcd τ) = some
        ⟨(svOf tr tcd τ).map UInt8.ofNat,
          (List.range (n * n)).map (fun l => ((sp.ids.getD (l / n) 0, sp.ids.getD (l % n) 0),
            stF.granted[l]! + (g[l]!).getD 0)),
          sp.params⟩ ∧
      (∀ x ∈ svOf tr tcd τ, x < 256) ∧
      PrevCanon sp.ids (prevOf tr tcd τ) (codecA0 tr tcd τ) (h0Of tr tcd τ) ∧
      (∀ l, l < n * n → stF.granted[l]! + (g[l]!).getD 0 ≤ 4500000) := by
  intro sp n
  -- the `prepD0` facts
  have hlen33 := prepD0_len hprep
  have hP := instOk_of hprep hids64
  have h256 : (p.sched.map instOf).length ≤ 256 := by rw [List.length_map]; omega
  have hlen : (p.sched.map instOf).length < 2013265921 := by omega
  have hτ' : τ < (p.sched.map instOf).length := by rw [List.length_map]; exact hτ
  have hsame : ∀ τ', τ' < (p.sched.map instOf).length →
      ((p.sched.map instOf).getD τ' instD).ids = ((p.sched.map instOf).getD 0 instD).ids := by
    obtain ⟨ids, hids⟩ := prepD0_ids hprep
    intro τ' h'
    rw [List.length_map] at h'
    rw [getD_map_instOf _ h', getD_map_instOf _ (by omega)]
    show p.sched[τ'].ids = p.sched[0].ids
    rw [hids _ (List.getElem_mem h'), hids _ (List.getElem_mem (by omega))]
  have hash32 : ∀ τ', τ' < (p.sched.map instOf).length → ((p.sched.map instOf).getD τ' instD).ash.length = 32 := by
    intro τ' h'
    rw [List.length_map] at h'
    rw [getD_map_instOf _ h']
    exact prepD0_ash hprep _ (List.getElem_mem h')
  have hvals := prepD0_values hprep _ (List.getElem_mem hτ)
  have S := prepD0_sched hprep _ (List.getElem_mem hτ)
  have C : InitCtx AP pub tr tp tm tcmp ts tch tg tsd tcd (p.sched.map instOf) :=
    ⟨hH, O, OS, OO, OC, SO, IO, h256, hP⟩
  have hP0 : (p.sched.map instOf).getD τ instD = instOf sp := getD_map_instOf _ hτ
  -- the process block
  obtain ⟨f, m, hf, hk, hc, hτf, Ib⟩ := proc_exists hH O OC PB PR I _ fwd hrecB hlen hτ'
  refine ⟨f, m, hf, hk, hc, hτf, Ib, ?_⟩
  intro stF g
  -- the previous state
  have hprev := codec_prevCanon C DO I fwd hrecP hrecD hsame hτ'
  rw [hP0] at hprev
  -- the core
  have hcore := proc_core''' hH O OS OO OC SO PB IO I _ fwd hrecP hrecB h256 hP hf hk hc Ib
    (prevOf tr tcd τ) (h0Of tr tcd τ) (by rw [hτf, hP0]; exact hprev)
  have hpost := sched_post C PB DO SH SK I fwd hrecP hrecB hrecD hsame hash32 hf hk hc Ib
  have hlink := proc_link''' hH O OS OO OC SO PB IO I _ fwd hrecP hrecB h256 hP hf hk hc Ib
  simp only [hτf, hP0] at hcore hpost hlink
  obtain ⟨hbytes, hpost⟩ := hpost
  obtain ⟨hsim, -⟩ := hlink
  have hG := (core_granted sp.ids S.n1 sp.params S.params sp.allowed (prepD0_asz hprep _ (List.getElem_mem hτ))
    (reqsOf (instOf sp)) sp.seed (codecA0 tr tcd τ) _ _ _ _ hsim).2
  refine ⟨?_, hbytes, hprev, fun l hl => Nat.le_trans (Nat.le_of_eq (hG l hl).1.symm) (hG l hl).2⟩
  rw [runCore_instOf sp S.n1 S.params hvals, hcore, hpost]
  congr 2
  apply List.map_congr_left
  intro l hl
  exact congrArg (Prod.mk _) (hG l (List.mem_range.1 hl)).1

end

end ZkFormal.NearV3.Sched
