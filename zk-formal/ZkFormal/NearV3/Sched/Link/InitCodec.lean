import ZkFormal.NearV3.Sched.Link.InitBus

/-!
# ZkFormal.NearV3.Sched.Link.InitCodec — the link `INIT`s of the codec (stage C)

Instance block `f` of `schV3` (`kF = 1`, `τ = tau f`, `P = Ps[τ]`), record `k < N`:

* **`codec_hdr`**: from the public codec record `parCodec τ P` (`first_par`): `nn = n`,
  `N = n²`, `base = P.params.base`, `fair = maxShardBandwidth / n`;
* **`codec_sdg`**: the `SDG` message received at the record start comes from a distribute cell,
  which received `linkRec τ P k`: `al = allowed[k]`, `srcC = src`, `hasC = [src exists]`;
* **`codec_sa0`**: with `hasC = 1`, the `SA0` message received at byte 2 is sent by record `src`
  of the same block (`block_unique`): `apR`, `bigR` are that record's `ap`, `bF`;
* **`codec_cb`**: the comparator bit `cb = [MA ≤ apR + fair]` (`cmp_sound`);
* **`codec_init_val`**: the `INIT` sent at the record end is `initRec τ allowed st k` with
  `st = lpState P.ids P.params P.allowed (preA0 f) P.seed`, where `preA0 f l` is the previous
  allowance of record `l` that the codec decodes from the pre bytes (`codec_pre_encode`).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-- **Per-instance public-data facts** (all from `prepD0`: `prepD0_sched`, `prepD0_rawOk`,
`prepD0_seed`, the borsh layout bounds). -/
structure InstOk (P : InstPub) : Prop where
  n1 : 1 ≤ P.ids.length
  n64 : P.ids.length ≤ 64
  params : Params.calculate Config.pv86 P.ids.length = some P.params
  asz : P.allowed.size = P.ids.length * P.ids.length
  ids64 : ∀ x ∈ P.ids, x < 2 ^ 64
  raw : RawOk P
  seed32 : P.seed.length = 32

/-- The previous allowance of record `l` decoded by the codec block `f` (`codec_pre_encode`; the
eight little-endian pre bytes of the record, `0` beyond the block's `N` records). -/
def preA0 (tr : Trace Fp) (t f : Nat) (l : Nat) : Nat :=
  if l < cv tr t f Codec.NN then Codec.rowLE tr t Codec.bpre (f + 5 + 24 * l + 16) 8 else 0

theorem getElem!_range_toArray_map {α : Type} [Inhabited α] (N : Nat) (g : Nat → α) {k : Nat}
    (hk : k < N) : ((List.range N).toArray.map g)[k]! = g k := by
  simp [getElem!_def, hk]

theorem srcOf_lt {ids : List Nat} {l s : Nat} (h : srcOf ids l = some s) : s < ids.length * ids.length := by
  unfold srcOf at h
  have := List.mem_of_getLast? h
  exact List.mem_range.1 (List.mem_filter.1 this).1

namespace Codec

theorem sa0_send_i : ∀ i ∈ interactions, i.bus = B_SA0 → i.send = true → i = interactions[13]! := by
  decide

theorem par_i : ∀ i ∈ interactions, i.bus = B_SPAR → i = interactions[6]! := by
  decide

end Codec

theorem ScanDist.sdg_i : ∀ i ∈ ScanDist.interactions, i.bus = B_SDG → i = ScanDist.interactions[9]! := by
  decide

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem ScanDist.sdg_msg (w : Nat) : (ScanDist.interactions[9]!).msgVal tr t w pub =
    [cv tr t w Dist.tau, cv tr t w Dist.llo + 256 * cv tr t w Dist.lhi, cv tr t w Dist.al,
      cv tr t w Dist.gb, cv tr t w Dist.side + 256 * cv tr t w Dist.shd, cv tr t w Dist.lnk,
      cv tr t w Dist.by0].map Fp.ofNat := by
  have ec : ∀ x, (c x).eval tr t w pub = Fp.ofNat (cv tr t w x) := fun x =>
    Scan.eval_ofNat (by simp only [zev_c, cur_cv])
  have e1 : Dist.linkE.eval tr t w pub = Fp.ofNat (cv tr t w Dist.llo + 256 * cv tr t w Dist.lhi) :=
    Scan.eval_ofNat (by simp only [Dist.linkE, zev_add, zev_smul, zev_c, cur_cv]; omega)
  have e2 : (Expr.add (c Dist.side) (smul 256 (c Dist.shd))).eval tr t w pub =
      Fp.ofNat (cv tr t w Dist.side + 256 * cv tr t w Dist.shd) :=
    Scan.eval_ofNat (by simp only [zev_add, zev_smul, zev_c, cur_cv]; omega)
  show [(c Dist.tau).eval tr t w pub, Dist.linkE.eval tr t w pub, (c Dist.al).eval tr t w pub,
    (c Dist.gb).eval tr t w pub, (Expr.add (c Dist.side) (smul 256 (c Dist.shd))).eval tr t w pub,
    (c Dist.lnk).eval tr t w pub, (c Dist.by0).eval tr t w pub] = _
  simp only [ec, e1, e2, List.map_cons, List.map_nil]

/-- On a cell, `alc = al`. -/
theorem Dist.cell_alc (hL : Dist.DLocal tr t pub) {w : Nat} (hw : w < tr.height t)
    (hc : cv tr t w Dist.kC = 1) : cv tr t w Dist.alc = cv tr t w Dist.al := by
  have h := hL.zc hw (e := .mul (c Dist.kC) (sub (c Dist.alc) (c Dist.al))) (by simp [Dist.constraints, Dist.cGrid])
  simp only [zev_mul, zev_sub, zev_c, cur_cv, hc] at h
  have := cv_lt (tr := tr) (t := t) w Dist.alc
  have := cv_lt (tr := tr) (t := t) w Dist.al
  have := h (by omega) (by omega)
  omega

end

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tm tcmp ts tch tg tsd tcd : Nat}

theorem b3_parts {x : Nat} (hx : x < 2 ^ 24) {a b d : Nat} (ha : a = x % 256) (hb : b = x / 256 % 256)
    (hd : d = x / 65536 % 256) : (a + 256 * b + 65536 * d) % 2013265921 = x := by
  subst ha hb hd; rw [b3_sum x hx]; exact Nat.mod_eq_of_lt (by omega)

/-- **The header of an instance block** from its public codec record. -/
theorem codec_hdr (hH : HoldsP AP pub tr) (OC : CodecValOwn AP tcd) (SO : SparOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) (h256 : Ps.length ≤ 256)
    {f : Nat} (hf : f < tr.height tcd) (hF : cv tr tcd f Codec.kF = 1)
    (PO : InstOk (Ps.getD (cv tr tcd f Codec.tau) instD)) :
    cv tr tcd f Codec.tau < Ps.length ∧
      cv tr tcd f Codec.nn = (Ps.getD (cv tr tcd f Codec.tau) instD).n ∧
      cv tr tcd f Codec.NN = (Ps.getD (cv tr tcd f Codec.tau) instD).n *
        (Ps.getD (cv tr tcd f Codec.tau) instD).n ∧
      cv tr tcd f Codec.base = (Ps.getD (cv tr tcd f Codec.tau) instD).params.base ∧
      cv tr tcd f Codec.fair = (Ps.getD (cv tr tcd f Codec.tau) instD).params.maxShardBandwidth /
        (Ps.getD (cv tr tcd f Codec.tau) instD).n := by
  have hL := codec_local hH OC
  have hH22 := codec_h22 hH OC
  obtain ⟨hlt, hpar⟩ := first_par hH OC SO I Ps fwd hrec (by omega) hf hF
  obtain ⟨-, -, -, -, -, m6, eb, efa⟩ := Codec.codec_first hL hH22 hf hF
  obtain ⟨-, hN, -⟩ := Codec.codec_block hL hH22 hf hF
  generalize hP : Ps.getD (cv tr tcd f Codec.tau) instD = P at PO hpar ⊢
  have hn := PO.n64
  obtain ⟨hM, -, hA, hbase, -, hbf⟩ := pv86_facts PO.n1 PO.params
  have hnn : P.n * P.n ≤ 4096 := Nat.mul_le_mul hn hn
  have hb100 : P.params.base ≤ 100000 := by rw [hbase]; exact Nat.min_le_right _ _
  have hfair : P.params.maxShardBandwidth / P.n ≤ 4500000 := by rw [hM]; exact Nat.div_le_self _ _
  rw [m6] at hpar
  have e := ofNat_list_inj (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      have := cv_lt (tr := tr) (t := tcd) f Codec.NN
      rcases hx with h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;>
        first | exact cv_lt _ _ | omega)
    (fun x hx => by
      simp only [parCodec, b2, b3, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      have hn' : P.n ≤ 64 := hn
      rcases hx with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> omega) hpar
  simp only [parCodec, b2, b3, List.cons_append, List.nil_append, List.cons.injEq] at e
  obtain ⟨-, -, e2, e3, e4, e5, e6, e7, e8, e9, e10, -⟩ := e
  refine ⟨hlt, e2, ?_, ?_, ?_⟩
  · omega
  · rw [eb]; exact b3_parts (by omega) e5 e6 e7
  · rw [efa]; exact b3_parts (by omega) e8 e9 e10

/-- **The `SDG` data of a record** (from the distribute cell of link `k`). -/
theorem codec_sdg (hH : HoldsP AP pub tr) (OC : CodecValOwn AP tcd) (SO : SparOwn AP)
    (OS : ScanOwn AP tsd tp) (IO : InitOwn AP tcd tsd)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) (h256 : Ps.length ≤ 256)
    (hP : ∀ τ, τ < Ps.length → InstOk (Ps.getD τ instD))
    {f : Nat} (hf : f < tr.height tcd) (hF : cv tr tcd f Codec.kF = 1)
    {k : Nat} (hk : k < cv tr tcd f Codec.NN) :
    let P := Ps.getD (cv tr tcd f Codec.tau) instD
    let e := f + 5 + 24 * k + 23
    cv tr tcd e Codec.al = P.al k ∧ cv tr tcd e Codec.srcC = (srcOf P.ids k).getD 0 ∧
      cv tr tcd e Codec.hasC = (if (srcOf P.ids k).isSome then 1 else 0) := by
  intro P e
  have hL := codec_local hH OC
  have hH22 := codec_h22 hH OC
  obtain ⟨-, -, -, -, -, -, -, RR, RS, -⟩ := Codec.codec_block hL hH22 hf hF
  obtain ⟨m12, msg12, -⟩ := Codec.codec_rec_msgs hL (RR k hk) (RS k hk)
  have hw0 : f + 5 + 24 * k < tr.height tcd := (RR k hk 0 (by omega)).1
  obtain ⟨r', hr', i', hi', hb', -, hmsg, hm'⟩ := recv_matched hH OS.lt IO.dgOnly IO.dgPub OC.lt hw0
    (by rw [OC.tab]; exact codec_mem 12 (by decide)) (by rw [Codec.i12_def]) (by rw [Codec.i12_def])
    (by rw [m12]; exact Nat.one_ne_zero)
  rw [OS.tab] at hi'
  have e9 := ScanDist.sdg_i i' hi' hb'
  subst e9
  have hSD := sd_local hH OS
  have hkC : cv tr tsd r' Dist.kC = 1 := Codec.one_of_mult (i := ScanDist.interactions[9]!) rfl hm'
  obtain ⟨hτ', l, hl, hpv⟩ := cell_rec hH OS I Ps fwd hrec h256 hr' hkC
  have hn := (hP _ hτ').n64
  rw [ScanDist.sdg_msg, msg12] at hmsg
  have halc := Dist.cell_alc (Dist.DLocal.of_sd hSD) hr' hkC
  generalize hQ : Ps.getD (cv tr tsd r' Dist.tau) instD = Q at hpv hl hn
  simp only [Scan.parV, linkRec, srcFields, b2, List.cons_append, List.nil_append, List.cons.injEq] at hpv
  obtain ⟨-, -, p0, p1, p2, -, -, -, p6, p7, p8, -⟩ := hpv
  have hs0 : cv tr tsd r' Dist.side = (srcOf Q.ids l).getD 0 % 256 := p0
  have hs1 : cv tr tsd r' Dist.shd = (srcOf Q.ids l).getD 0 / 256 % 256 := p1
  have hs2 : cv tr tsd r' Dist.lnk = (if (srcOf Q.ids l).isSome then 1 else 0) := p2
  have hl0 : cv tr tsd r' Dist.llo = l % 256 := p6
  have hl1 : cv tr tsd r' Dist.lhi = l / 256 % 256 := p7
  have hal : cv tr tsd r' Dist.alc = Q.al l := p8
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmsg
  obtain ⟨t0, t1, t2, -, t4, t5, -⟩ := hmsg
  have hnn : Q.n * Q.n ≤ 4096 := Nat.mul_le_mul hn hn
  have hτ := (ofNat_inj' (cv_lt _ _) (cv_lt _ _) t0).symm
  have hsrc : (srcOf Q.ids l).getD 0 < 4096 := by
    cases h : srcOf Q.ids l with
    | none => simp
    | some s => have := srcOf_lt h; unfold InstPub.n at hnn; simp; omega
  rw [hl0, hl1, show l % 256 + 256 * (l / 256 % 256) = l by omega] at t1
  have hkl := (ofNat_inj' (by omega) (by omega) t1).symm
  subst hkl
  have hQP : Q = P := by rw [← hQ, ← hτ]
  subst hQP
  refine ⟨?_, ?_, ?_⟩
  · exact (ofNat_inj' (cv_lt _ _) (cv_lt _ _) t2).symm.trans (halc.symm.trans hal)
  · rw [hs0, hs1, b2_sum _ (by omega)] at t4
    exact (ofNat_inj' (by omega) (cv_lt _ _) t4).symm
  · rw [hs2] at t5
    exact (ofNat_inj' (by split <;> decide) (cv_lt _ _) t5).symm

/-- **The `SA0` data of a record with a source**: the source record's `ap`, `bF` (same block). -/
theorem codec_sa0 (hH : HoldsP AP pub tr) (OC : CodecValOwn AP tcd) (SO : SparOwn AP)
    (IO : InitOwn AP tcd tsd)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) (h256 : Ps.length ≤ 256)
    {f : Nat} (hf : f < tr.height tcd) (hF : cv tr tcd f Codec.kF = 1)
    {k : Nat} (hk : k < cv tr tcd f Codec.NN)
    (hhas : cv tr tcd (f + 5 + 24 * k + 23) Codec.hasC = 1) :
    cv tr tcd (f + 5 + 24 * k + 23) Codec.srcC < cv tr tcd f Codec.NN ∧
      cv tr tcd (f + 5 + 24 * k + 18) Codec.apR =
        cv tr tcd (f + 5 + 24 * cv tr tcd (f + 5 + 24 * k + 23) Codec.srcC + 23) Codec.ap ∧
      cv tr tcd (f + 5 + 24 * k + 18) Codec.bigR =
        cv tr tcd (f + 5 + 24 * cv tr tcd (f + 5 + 24 * k + 23) Codec.srcC + 23) Codec.bF := by
  have hL := codec_local hH OC
  have hH22 := codec_h22 hH OC
  obtain ⟨-, -, -, -, -, -, -, RR, RS, -⟩ := Codec.codec_block hL hH22 hf hF
  obtain ⟨-, -, -, m14, msg14, -⟩ := Codec.codec_rec_msgs hL (RR k hk) (RS k hk)
  have hb : f + 5 + 24 * k + 18 < tr.height tcd := (RR k hk 18 (by omega)).1
  obtain ⟨r', hr', i', hi', hb', hs', hmsg, hm'⟩ := recv_matched hH OC.lt IO.a0Only IO.a0Pub OC.lt hb
    (by rw [OC.tab]; exact codec_mem 14 (by decide)) (by rw [Codec.i14_def]) (by rw [Codec.i14_def])
    (by rw [m14, hhas]; exact Nat.one_ne_zero)
  rw [OC.tab] at hi'
  have e13 := Codec.sa0_send_i i' hi' hb' hs'
  subst e13
  have hu : cv tr tcd r' Codec.u0g = 1 := Codec.one_of_mult (i := Codec.interactions[13]!) rfl hm'
  obtain ⟨f', k', hf', hF', hk', rfl⟩ := Codec.rend_rec hL hH22 hr' (Codec.rend_of_u0g hL hr' hu)
  obtain ⟨-, -, -, -, -, -, -, RR', RS', -⟩ := Codec.codec_block hL hH22 hf' hF'
  have M' := Codec.codec_rec_msgs hL (RR' k' hk') (RS' k' hk')
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, msg13, -⟩ := M'
  obtain ⟨hap, hbF, -⟩ := Codec.alw_walk hL (RR' k' hk')
  rw [msg13, msg14, ← hap, ← hbF] at hmsg
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmsg
  obtain ⟨t0, t1, t2, t3, -⟩ := hmsg
  have hτ := ofNat_inj' (cv_lt _ _) (cv_lt _ _) t0
  have e := block_unique hH OC SO I Ps fwd hrec (by omega) hf' hF' hf hF hτ
  subst e
  have hk'' := ofNat_inj' (by omega) (cv_lt _ _) t1
  subst hk''
  exact ⟨hk', ofNat_inj' (cv_lt _ _) (cv_lt _ _) t2 |>.symm, ofNat_inj' (cv_lt _ _) (cv_lt _ _) t3 |>.symm⟩

/-- **The comparator bit of the link pass.** -/
theorem codec_cb (hH : HoldsP AP pub tr) (OC : CodecValOwn AP tcd) (CO : CmpOwn AP tcmp)
    {f : Nat} (hf : f < tr.height tcd) (hF : cv tr tcd f Codec.kF = 1)
    {k : Nat} (hk : k < cv tr tcd f Codec.NN)
    (hx : cv tr tcd (f + 5 + 24 * k + 18) Codec.apR + cv tr tcd f Codec.fair < 2 ^ 29) :
    cv tr tcd (f + 5 + 24 * k + 18) Codec.cb =
      (if Codec.MA ≤ cv tr tcd (f + 5 + 24 * k + 18) Codec.apR + cv tr tcd f Codec.fair then 1 else 0) := by
  have hL := codec_local hH OC
  have hH22 := codec_h22 hH OC
  obtain ⟨-, -, -, -, -, -, -, RR, RS, -⟩ := Codec.codec_block hL hH22 hf hF
  obtain ⟨-, -, -, -, -, -, m15, msg15, -⟩ := Codec.codec_rec_msgs hL (RR k hk) (RS k hk)
  have hb : f + 5 + 24 * k + 18 < tr.height tcd := (RR k hk 18 (by omega)).1
  rw [Nat.mod_eq_of_lt (show cv tr tcd (f + 5 + 24 * k + 18) Codec.apR + cv tr tcd f Codec.fair <
    2013265921 by omega)] at msg15
  simp only [List.map_cons, List.map_nil] at msg15
  have ex : (Fp.ofNat (cv tr tcd (f + 5 + 24 * k + 18) Codec.apR + cv tr tcd f Codec.fair)).toNat =
      cv tr tcd (f + 5 + 24 * k + 18) Codec.apR + cv tr tcd f Codec.fair := toNat_ofNat_lt' (by omega)
  have ey : (Fp.ofNat Codec.MA).toNat = Codec.MA := toNat_ofNat_lt' (by decide)
  have hc := cmp_sound hH CO OC.lt hb (by rw [OC.tab]; exact codec_mem 15 (by decide))
    (by rw [Codec.i15_def]) (by rw [Codec.i15_def]) (by rw [m15]; exact Nat.one_ne_zero) msg15
    (by rw [ex]; exact hx) (by rw [ey]; decide)
  rw [ex, ey] at hc
  have hcb := cv_lt (tr := tr) (t := tcd) (f + 5 + 24 * k + 18) Codec.cb
  rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h2]; exact ofNat_inj' hcb (by decide) h1
  · rw [if_neg (by omega)]; exact ofNat_inj' hcb (by decide) h1

/-- **The link `INIT` of record `k`.** -/
theorem codec_init_val (hH : HoldsP AP pub tr) (OC : CodecValOwn AP tcd) (SO : SparOwn AP)
    (OS : ScanOwn AP tsd tp) (IO : InitOwn AP tcd tsd) (CO : CmpOwn AP tcmp)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) (h256 : Ps.length ≤ 256)
    (hP : ∀ τ, τ < Ps.length → InstOk (Ps.getD τ instD))
    {f : Nat} (hf : f < tr.height tcd) (hF : cv tr tcd f Codec.kF = 1)
    {k : Nat} (hk : k < cv tr tcd f Codec.NN) :
    (Codec.interactions[10]!).msgVal tr tcd (f + 5 + 24 * k + 23) pub =
      (initRec (cv tr tcd f Codec.tau) (Ps.getD (cv tr tcd f Codec.tau) instD).allowed
        (lpState (Ps.getD (cv tr tcd f Codec.tau) instD).ids (Ps.getD (cv tr tcd f Codec.tau) instD).params
          (Ps.getD (cv tr tcd f Codec.tau) instD).allowed (preA0 tr tcd f)
          (Ps.getD (cv tr tcd f Codec.tau) instD).seed) k).map Fp.ofNat := by
  have hL := codec_local hH OC
  have hH22 := codec_h22 hH OC
  obtain ⟨-, -, -, -, -, -, -, RR, RS, -⟩ := Codec.codec_block hL hH22 hf hF
  have hτ : cv tr tcd f Codec.tau < Ps.length := (first_par hH OC SO I Ps fwd hrec (by omega) hf hF).1
  have PO := hP _ hτ
  obtain ⟨-, -, hNN, hbase, hfair⟩ := codec_hdr hH OC SO I Ps fwd hrec h256 hf hF PO
  obtain ⟨hal, hsrc, hhas⟩ := codec_sdg hH OC SO OS IO I Ps fwd hrec h256 hP hf hF hk
  have M := Codec.codec_rec_msgs hL (RR k hk) (RS k hk)
  obtain ⟨-, -, -, -, -, h0, -, -, -, msg10, -⟩ := M
  generalize Ps.getD (cv tr tcd f Codec.tau) instD = P at PO hNN hbase hfair hal hsrc hhas ⊢
  have hn := PO.n64
  obtain ⟨hMS, -, hMA, hb, -, hbf⟩ := pv86_facts PO.n1 PO.params
  have hb100 : P.params.base ≤ 100000 := by rw [hb]; exact Nat.min_le_right _ _
  have hfl : P.params.maxShardBandwidth / P.n ≤ 4500000 := by rw [hMS]; exact Nat.div_le_self _ _
  unfold InstPub.n at hNN hfair hfl
  -- the source of record k and the previous allowance it reads
  have hA : ∀ (apv bgv : Nat), apv < 2 ^ 24 → bgv ≤ 1 →
      (bgv = 1 → Codec.MA ≤ (srcArr P.ids (preA0 tr tcd f))[k]!) →
      (bgv = 0 → (srcArr P.ids (preA0 tr tcd f))[k]! = apv) →
      cv tr tcd (f + 5 + 24 * k + 18) Codec.apR = apv →
      cv tr tcd (f + 5 + 24 * k + 18) Codec.bigR = bgv →
      (Codec.interactions[10]!).msgVal tr tcd (f + 5 + 24 * k + 23) pub =
        (initRec (cv tr tcd f Codec.tau) P.allowed
          (lpState P.ids P.params P.allowed (preA0 tr tcd f) P.seed) k).map Fp.ofNat := by
    intro apv bgv hap hbg hbig hsm eapR ebig
    have hcb := codec_cb hH OC (tcmp := tcmp) CO hf hF hk (by rw [eapR, hfair]; omega)
    obtain ⟨L1, Lal, L2, -, L4⟩ := Codec.codec_link hL (RR k hk) hcb (by rw [eapR, hfair]; omega)
    rw [ebig, eapR, hfair] at L1
    rw [hbase] at L2 L4
    have hkN : k < P.ids.length * P.ids.length := by omega
    have hk4 : k < 4096 := by have := Nat.mul_le_mul hn hn; omega
    -- the spec value a1
    have ha1 : cv tr tcd (f + 5 + 24 * k + 23) Codec.a1 =
        Nat.min ((srcArr P.ids (preA0 tr tcd f))[k]! + P.params.maxShardBandwidth / P.ids.length)
          P.params.maxAllowance := by
      rw [L1, hMA]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hbg with h | h
      · rw [if_neg (by omega), hsm h]; rfl
      · rw [if_pos h]; have := hbig h; unfold Codec.MA at this ⊢
        exact (Nat.min_eq_right (by omega)).symm
    have hle : cv tr tcd (f + 5 + 24 * k + 23) Codec.al * P.params.base ≤
        cv tr tcd (f + 5 + 24 * k + 23) Codec.a1 := by
      rw [ha1, hal, hMA]
      have := al_le P k
      have : P.params.base ≤ P.params.maxShardBandwidth / P.ids.length := hbf
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (al_le P k) with h | h <;> rw [h] <;>
        simp only [Nat.zero_mul, Nat.one_mul, Nat.zero_le] <;>
        exact Nat.le_min.2 ⟨by omega, by omega⟩
    have ha2 := L4 hle
    have hst_a : (lpState P.ids P.params P.allowed (preA0 tr tcd f) P.seed).allowance[k]! =
        (if P.allowed[k]! then Nat.min ((srcArr P.ids (preA0 tr tcd f))[k]! +
          P.params.maxShardBandwidth / P.ids.length) P.params.maxAllowance - P.params.base
        else Nat.min ((srcArr P.ids (preA0 tr tcd f))[k]! +
          P.params.maxShardBandwidth / P.ids.length) P.params.maxAllowance) := by
      simp only [lpState, linkPass]; exact getElem!_range_toArray_map _ _ hkN
    have hst_g : (lpState P.ids P.params P.allowed (preA0 tr tcd f) P.seed).granted[k]! =
        (if P.allowed[k]! then P.params.base else 0) := by
      simp only [lpState, linkPass]; exact getElem!_range_toArray_map _ _ hkN
    have h1 : rd (cv tr tcd f Codec.tau) (lpState P.ids P.params P.allowed (preA0 tr tcd f) P.seed)
        (cv tr tcd f Codec.tau * 16384 + k) = cv tr tcd (f + 5 + 24 * k + 23) Codec.a2 := by
      unfold rd
      rw [show cv tr tcd f Codec.tau * 16384 + k - cv tr tcd f Codec.tau * 16384 = k by omega,
        if_pos hk4, hst_a, ha2, ha1, hal]
      unfold InstPub.al
      split <;> simp
    have h2 : (if P.allowed[k]! then 1 else 0) = cv tr tcd (f + 5 + 24 * k + 23) Codec.al := by
      rw [hal]; rfl
    have h3 : (lpState P.ids P.params P.allowed (preA0 tr tcd f) P.seed).granted[k]! =
        cv tr tcd (f + 5 + 24 * k + 23) Codec.g2 := by
      rw [hst_g, L2, hal]
      unfold InstPub.al
      split <;> simp
    rw [msg10]
    congr 1
    rw [initRec, if_pos hk4, if_pos hk4, if_pos hk4, h1, h2, h3, Nat.mul_comm]
  -- case on the source
  cases hs : srcOf P.ids k with
  | none =>
    rw [hs] at hhas
    obtain ⟨z1, z2⟩ := h0 (by simpa using hhas)
    refine hA 0 0 (by decide) (by decide) (by intro h; exact absurd h (by decide)) (fun _ => ?_) z1 z2
    unfold srcArr
    rw [getElem!_range_toArray_map _ _ (by omega), hs]
  | some s =>
    rw [hs] at hhas hsrc
    simp only [Option.isSome_some, ite_true] at hhas
    simp only [Option.getD_some] at hsrc
    obtain ⟨hsN, eap, ebg⟩ := codec_sa0 hH OC SO IO I Ps fwd hrec h256 hf hF hk hhas
    rw [hsrc] at hsN eap ebg
    obtain ⟨hsplit, haplt, hbF0⟩ := Codec.a0_split hL hH22 hf hF hsN
    have hsa : (srcArr P.ids (preA0 tr tcd f))[k]! = preA0 tr tcd f s := by
      unfold srcArr
      rw [getElem!_range_toArray_map _ _ (by omega), hs]
    have hbFb : cv tr tcd (f + 5 + 24 * s + 23) Codec.bF ≤ 1 := by
      obtain ⟨-, hbF, -⟩ := Codec.alw_walk hL (RR s hsN)
      rw [hbF]; split <;> decide
    refine hA _ _ haplt hbFb (fun h => ?_) (fun h => ?_) eap ebg
    · rw [hsa]; unfold preA0
      rw [if_pos hsN, hsplit]
      have : Codec.rowLE tr tcd Codec.bpre (f + 5 + 24 * s + 19) 5 ≠ 0 := fun h0 =>
        absurd (hbF0.2 h0) (by omega)
      unfold Codec.MA
      have : 2 ^ 24 ≤ 2 ^ 24 * Codec.rowLE tr tcd Codec.bpre (f + 5 + 24 * s + 19) 5 :=
        Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero this)
      omega
    · rw [hsa]; unfold preA0
      rw [if_pos hsN, hsplit, hbF0.1 h]; simp

end

end ZkFormal.NearV3.Sched
