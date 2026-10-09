import ZkFormal.NearV3.Sched.Link.GrantFwd
import ZkFormal.NearV3.Sched.Link.Sound

/-!
# ZkFormal.NearV3.Sched.Link.GrantSound — `schedCore_sound'` (stage E)

`schedCore_sound` (stage D) with the grants tied to the AIR and the τ = 0 forwarding check.
Besides the process key block `f` (rounds `m`), every instance τ has a codec block `fc`
(`codec_exists`, `kF = 1`, `tau = τ`, `NN = n²`), and at the end of each record `l < n²`:

* **`gfin = stF.granted[l]`** (`codec_gfin`: memory FIN of the `w` column, stage E step a);
* `gb < 2^23` (`codec_gb_lt`: the `SDG` grant of a distribute cell);
* the output grant of link `l` is `stF.granted[l] + grid[l] = gfin + grid[l]`;
* **forwarding** (τ = 0): `fwdDemand fwd l mod 2^24 ≤ gfin + gb` (`codec_fwd`).

**Open (step b)**: `GbGrid`, the codec's `gb` of record `l` is `grid[l]`
(`gridGrants … (sordOf …) (rordOf …)`). With it (and demands `< 2^24`, a render condition),
**`schedCore_fwd`**: every forwarding demand of instance 0 is at most its link's output grant.
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-- **Open (stage E step b).** The codec's `gb` of record `l` of block `fc` is the spec's grid grant. -/
def GbGrid (tr : Trace Fp) (tcd fc n : Nat) (g : Array (Option Nat)) : Prop :=
  ∀ l, l < n * n → cv tr tcd (fc + 5 + 24 * l + 23) Codec.gb = (g[l]!).getD 0

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

/-- **`schedCore_sound'`.** -/
theorem schedCore_sound' (hH : HoldsP AP pub tr) {tp tm tcmp ts tch tg tsd tcd tsha : Nat}
    -- ownership (decidable on the final AIR)
    (O : SchedOwn AP tp tm tcmp ts tch tg) (OS : ScanOwn AP tsd tp) (OO : OpOwn AP tp tsd tcd)
    (OC : CodecValOwn AP tcd) (SO : SparOwn AP) (PB : PubbOwn AP) (IO : InitOwn AP tcd tsd)
    (DO : SdlOwn AP tcd) (PR : PubbRecv AP tp tcd) (SH : ShaOwn AP tsha)
    -- the kind registry (cross-lane)
    (SK : ShaKind AP pub tr tcd)
    -- the prepared statement and the public records (`PubIdx`, R1)
    {cb : NearSpec.Bytes} {hint : Hint} {p : Prep} (hprep : prepD0 cb hint = .ok p)
    (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat))
    (hrecP : I.recs B_SPAR true = (render (p.sched.map instOf) fwd).par)
    (hrecB : I.recs B_SPUBB true = (render (p.sched.map instOf) fwd).pubb)
    (hrecD : I.recs B_SDL true = (render (p.sched.map instOf) fwd).dlSend)
    {τ : Nat} (hτ : τ < p.sched.length) :
    let sp := p.sched[τ]
    let n := sp.ids.length
    ∃ f m fc, f < tr.height tp ∧ cv tr tp f Proc.kK = 1 ∧ cv tr tp f Proc.kc = 0 ∧
      cv tr tp f Proc.tau = τ ∧ Proc.Inst tr tp f m ∧
      fc < tr.height tcd ∧ cv tr tcd fc Codec.kF = 1 ∧ cv tr tcd fc Codec.tau = τ ∧
      cv tr tcd fc Codec.NN = n * n ∧
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
      (∀ l, l < n * n → stF.granted[l]! + (g[l]!).getD 0 ≤ 4500000) ∧
      -- the grants as the AIR holds them
      (∀ l, l < n * n → cv tr tcd (fc + 5 + 24 * l + 23) Codec.gfin = stF.granted[l]! ∧
        cv tr tcd (fc + 5 + 24 * l + 23) Codec.gb < 2 ^ 23) ∧
      -- the forwarding check of instance 0
      (τ = 0 → ∀ l, l < n * n →
        fwdDemand fwd l % 2 ^ 24 ≤ stF.granted[l]! + cv tr tcd (fc + 5 + 24 * l + 23) Codec.gb) := by
  intro sp n
  obtain ⟨f, m, hf, hk, hc, hτf, Ib, H⟩ := schedCore_sound hH O OS OO OC SO PB IO DO PR SH SK hprep I fwd
    hrecP hrecB hrecD hτ
  have hlen33 := prepD0_len hprep
  have hP := instOk_of hprep
  have h256 : (p.sched.map instOf).length ≤ 256 := by rw [List.length_map]; omega
  have hτ' : τ < (p.sched.map instOf).length := by rw [List.length_map]; exact hτ
  have S := prepD0_sched hprep _ (List.getElem_mem hτ)
  have hasz := prepD0_asz hprep _ (List.getElem_mem hτ)
  have C : InitCtx AP pub tr tp tm tcmp ts tch tg tsd tcd (p.sched.map instOf) :=
    ⟨hH, O, OS, OO, OC, SO, IO, h256, hP⟩
  have hP0 : (p.sched.map instOf).getD τ instD = instOf sp := getD_map_instOf _ hτ
  have hP00 : (p.sched.map instOf).getD 0 instD = instOf p.sched[0] := getD_map_instOf _ (by omega)
  obtain ⟨-, M⟩ := memCtx_of C PB I fwd hrecP hrecB hf hk hc Ib
  obtain ⟨fc, hfc, hF, hτc⟩ := C.codec_exists I fwd hrecP hτ'
  obtain ⟨-, -, hNN, -⟩ := codec_hdr hH OC SO I _ fwd hrecP h256 hfc hF (by rw [hτc]; exact hP _ hτ')
  rw [hτc, hP0] at hNN
  rw [hτf, hP0] at M
  refine ⟨f, m, fc, hf, hk, hc, hτf, Ib, hfc, hF, hτc, hNN, ?_⟩
  intro stF g
  obtain ⟨hrun, hbytes, hprev, hle⟩ := H
  -- the start state's invariants
  have hG : GInv n 4500000 (lpState sp.ids sp.params sp.allowed (codecA0 tr tcd τ) sp.seed) := by
    have := lpState_ginv sp.ids S.n1 sp.params S.params sp.allowed hasz (codecA0 tr tcd τ) sp.seed
    rw [pv86_maxShard S.params] at this
    exact this
  have hSz : SzOk n (lpState sp.ids sp.params sp.allowed (codecA0 tr tcd τ) sp.seed) := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [lpState, linkPass] <;> rfl
  have hgfin : ∀ l, l < n * n → cv tr tcd (fc + 5 + 24 * l + 23) Codec.gfin = stF.granted[l]! :=
    fun l hl => codec_gfin M hSz hG OC hfc hF (hτc.trans hτf.symm) hNN hl
  have hgb : ∀ l, l < n * n → cv tr tcd (fc + 5 + 24 * l + 23) Codec.gb < 2 ^ 23 :=
    fun l hl => codec_gb_lt hH OC OS IO hfc hF (by rw [hNN]; exact hl)
  refine ⟨hrun, hbytes, hprev, hle, fun l hl => ⟨hgfin l hl, hgb l hl⟩, ?_⟩
  intro h0 l hl
  have hn0 : ((p.sched.map instOf).getD 0 instD).n ≤ 64 := (hP 0 (by omega)).n64
  have hfw := codec_fwd hH OC OS IO O.cmp PB I _ fwd hrecB hn0 hfc hF (by rw [hτc, h0])
    (by rw [hNN]; exact hl) (by rw [hgfin l hl]; exact Nat.le_trans (Nat.le_add_right _ _) (hle l hl))
  rw [hgfin l hl] at hfw
  exact hfw

/-- **The forwarding check against the output grants**, given the open step (b) (`GbGrid`) and
demands below `2^24` (a render condition): every forwarding demand of instance 0 is at most the
grant `runCore` outputs for its link. -/
theorem schedCore_fwd {n fc : Nat} {stF : St} {g : Array (Option Nat)} {fwd : List (Nat × Nat)}
    {tcd : Nat} (hgb : GbGrid tr tcd fc n g) (h24 : ∀ l, l < n * n → fwdDemand fwd l < 2 ^ 24)
    (hfw : ∀ l, l < n * n →
      fwdDemand fwd l % 2 ^ 24 ≤ stF.granted[l]! + cv tr tcd (fc + 5 + 24 * l + 23) Codec.gb) :
    ∀ l, l < n * n → fwdDemand fwd l ≤ stF.granted[l]! + (g[l]!).getD 0 := by
  intro l hl
  have := hfw l hl
  rw [Nat.mod_eq_of_lt (h24 l hl), hgb l hl] at this
  exact this

end

end ZkFormal.NearV3.Sched
