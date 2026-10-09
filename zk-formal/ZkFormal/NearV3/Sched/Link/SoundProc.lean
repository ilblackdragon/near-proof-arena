import ZkFormal.NearV3.Sched.Link.SoundPost

/-!
# ZkFormal.NearV3.Sched.Link.SoundProc — every instance has a process block; `convertRaw`

* **`proc_exists`**: for every τ `< |Ps|` the public key record `(τ, 3, 0, seed₀, seed₁, 0, 0)` is
  received (no table sends on `SPUBB`, every public `SPUBB` segment sends); with `PubbRecv` (only
  the process table and the codec have `SPUBB` interactions, decidable) the receiver is a process
  row with `kK = 1`, `kc = 0`, `tau = τ` (a codec `SPUBB` message has tag 2 or 4), i.e. a key-block
  start, whose rounds `proc_rounds` gives (`Proc.Inst`);
* **`convertRaw_eq_convRaw`**: the spec's raw conversion with the value table
  `requestValues p` is `convRaw` of the resolved requests (`rawOf`).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-- Only the process table and the codec have `SPUBB` interactions. -/
structure PubbRecv (AP : AirP) (tp tc : Nat) : Prop where
  only : ∀ t, t < AP.tables.length → t ≠ tp → t ≠ tc → ∀ i ∈ AP.tables[t]!.interactions, i.bus ≠ B_SPUBB

theorem Proc.pubb_i : ∀ i ∈ Proc.interactions, i.bus = B_SPUBB → i = Proc.interactions[0]! := by
  decide

theorem Codec.pubb_i : ∀ i ∈ Codec.interactions, i.bus = B_SPUBB → i = Codec.interactions[9]! := by
  decide

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

/-- **Every instance has a process key block with its rounds.** -/
theorem proc_exists (hH : HoldsP AP pub tr) {tp tm tcmp ts tch tg tcd : Nat}
    (O : SchedOwn AP tp tm tcmp ts tch tg) (OC : CodecValOwn AP tcd) (PB : PubbOwn AP)
    (PR : PubbRecv AP tp tcd) (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrecB : I.recs B_SPUBB true = (render Ps fwd).pubb) (hlen : Ps.length < 2013265921)
    {τ : Nat} (hτ : τ < Ps.length) :
    ∃ f m, f < tr.height tp ∧ cv tr tp f Proc.kK = 1 ∧ cv tr tp f Proc.kc = 0 ∧
      cv tr tp f Proc.tau = τ ∧ Proc.Inst tr tp f m := by
  obtain ⟨M, hMd⟩ : ∃ M, M = ([τ, TAG_KEY, 0, ((Ps.getD τ instD).seed.getD 0 0).toNat,
      ((Ps.getD τ instD).seed.getD 1 0).toNat, 0, 0] : List Nat).map Fp.ofNat := ⟨_, rfl⟩
  have hpc : 1 ≤ pubCount AP pub B_SPUBB true M := by
    rw [I.count, hrecB, render_pubb]
    apply List.count_pos_iff.2
    refine List.mem_map.2 ⟨_, List.mem_append_left _ (List.mem_flatMap.2 ⟨τ, List.mem_range.2 hτ,
      List.mem_append_left _ (List.mem_map.2 ⟨0, List.mem_range.2 (by decide), rfl⟩)⟩), ?_⟩
    rw [hMd]
  have hbal := hH.balance B_SPUBB M
  rw [busCount_send_zero PB.none, pubCount_zero (s := false) (fun seg h1 h2 => by rw [PB.pub seg h1 h2]; simp) _]
    at hbal
  obtain ⟨t, ht, htc⟩ := busCount_go_pos tr pub B_SPUBB false M AP.tables 0 (by unfold busCount at hbal; omega)
  rw [Nat.zero_add] at htc
  obtain ⟨w, hw, i, hi, hb, -, hmsg, hm⟩ := exists_of_tableBusCount htc
  by_cases htp : t = tp
  · rw [htp] at hi hm hmsg hw
    rw [O.tp_tab] at hi
    have e := Proc.pubb_i i hi hb
    subst e
    rw [Mem.multNat_c (by rw [Proc.i0_def])] at hm
    have hk : cv tr tp w Proc.kK = 1 := by
      by_cases h : cv tr tp w Proc.kK = 1
      · exact h
      · simp [h] at hm
    rw [Proc.i0_def, hMd] at hmsg
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at hmsg
    obtain ⟨e1, -, e3, -⟩ := hmsg
    have h1 : cv tr tp w Proc.tau = τ := by
      show (tr.cell tp w Proc.tau).toNat = τ
      have : (c Proc.tau).eval tr tp w pub = tr.cell tp w Proc.tau := rfl
      rw [← this, e1, toNat_ofNat_lt' (by omega)]
    have h3 : cv tr tp w Proc.kc = 0 := by
      show (tr.cell tp w Proc.kc).toNat = 0
      have : (c Proc.kc).eval tr tp w pub = tr.cell tp w Proc.kc := rfl
      rw [← this, e3]; rfl
    have hL := pLocal_of hH O.tp_lt O.tp_tab
    have hH22 := proc_height hH O.tp_lt O.tp_tab
    obtain ⟨m, A, B, C, D⟩ := Proc.proc_rounds hL hH22 hw hk h3
    exact ⟨w, m, hw, hk, h3, h1, ⟨A, B, C, D⟩⟩
  · by_cases htc' : t = tcd
    · exfalso
      rw [htc'] at hi hm hmsg hw
      rw [OC.tab] at hi
      have e := Codec.pubb_i i hi hb
      subst e
      have hL := codec_local hH OC
      have b1 := Codec.bool_of hL hw (x := Codec.kA) (by simp [Codec.boolCols])
      have b2 := Codec.bool_of hL hw (x := Codec.fwg) (by simp [Codec.boolCols])
      rw [Codec.i9_def, hMd] at hmsg
      simp only [Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at hmsg
      obtain ⟨-, e2, -⟩ := hmsg
      have ev : (Expr.add (smul 2 (c Codec.kA)) (smul 4 (c Codec.fwg))).eval tr tcd w pub =
          Fp.ofNat (2 * cv tr tcd w Codec.kA + 4 * cv tr tcd w Codec.fwg) :=
        Codec.ev_of (by simp only [zev_add, zev_smul, zev_c, cur_cv]; omega)
      rw [ev] at e2
      have := ofNat_inj' (by omega) (by decide) e2
      simp [TAG_KEY] at this
      omega
    · exact absurd hb (PR.only t ht htp htc' i hi)

end

/-! ## The spec's raw conversion -/

theorem convertRaw_eq_convRaw {ids : List Nat} {p : Params} (hn : 1 ≤ ids.length)
    (hp : Params.calculate Config.pv86 ids.length = some p) (raw : List (Nat × List BandwidthRequest)) :
    convertRaw (requestValues p) p.base ids raw = convRaw p ids.length (rawOf ids raw) := by
  simp only [convertRaw, convRaw, rawOf, List.filterMap_flatMap, List.filterMap_filterMap]
  congr 1
  funext x
  obtain ⟨sender, brs⟩ := x
  simp only
  congr 1
  funext br
  simp only [convertRequestV, increases_eq_incsFrom hn hp]
  cases indexOf ids sender <;> cases indexOf ids br.toShard <;> simp only [Option.bind] <;>
    cases incsOf p br.bitmap <;> rfl

/-- `runCore` on the instance record's requests. -/
theorem runCore_instOf (sp : SchedPub) (hn : 1 ≤ sp.ids.length)
    (hp : Params.calculate Config.pv86 sp.ids.length = some sp.params)
    (hv : sp.values = requestValues sp.params) (prev : Option NearSpec.Bytes) :
    runCore sp prev = coreOf (instOf sp).ids (instOf sp).params (instOf sp).allowed (reqsOf (instOf sp))
      (instOf sp).seed (instOf sp).ash prev := by
  rw [runCore_eq, hv, convertRaw_eq_convRaw hn hp]
  unfold reqsOf
  rw [show (instOf sp).n = sp.ids.length from rfl, show (instOf sp).params = sp.params from rfl,
    convRaw_instOf]
  rfl

end ZkFormal.NearV3.Sched
