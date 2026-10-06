import ZkFormal.NearV3.Sched.Link.GridCell
import ZkFormal.NearV3.Sched.Link.GrantSound

/-!
# ZkFormal.NearV3.Sched.Link.GridLink — `GbGrid` and the forwarding check against the output grants (stage F, b6)

* `par_link_count`, **`cell_unique`**: a public link record occurs once in `render`'s `SPAR`
  records, so two cells receiving the same record are the same row (as `shard_unique`);
* **`codec_cell`**: the `SDG` message the codec receives at record `k` of its block of instance τ
  is sent by a cell that received `linkRec τ P k`, and carries that cell's `gb`;
* **`gbGrid_of`**: in τ's distribute section (`shard_exists` + `cover`), the cell `(i, j)` with
  `sord[i]·n + rord[j] = k` is that cell (`cell_unique`), and its grant is the grid grant
  (`grid_cells`, `gridGrants_get`), so **`GbGrid`** holds;
* **`schedCore_sound''`**: `schedCore_sound'` plus `GbGrid` and, for τ = 0, every forwarding
  demand below `2^24` is at most its link's output grant `stF.granted[l] + grid[l]`;
* **`schedCore_fwd'`**: the same, stated on `runCore`'s output for instance 0.

New hypothesis: **`SdlxOwn`** (ownership, decidable). The demand bound `< 2^24` is an assembly
condition (the public forwarding record holds three bytes; the renderer must reject larger
demands, which exceed every grant `≤ 4,500,000`).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-! ## One cell per link record -/

theorem linkRec_inj {τ : Nat} {P : InstPub} (hτ : τ < 256) {l1 l2 : Nat} (h1 : l1 < 65536) (h2 : l2 < 65536)
    (h : (linkRec τ P l1).map Fp.ofNat = (linkRec τ P l2).map Fp.ofNat) : l1 = l2 := by
  have e := ofNat_list_inj (linkRec_lt hτ l1) (linkRec_lt hτ l2) h
  have e8 := congrArg (·[8]?) e
  have e9 := congrArg (·[9]?) e
  simp [linkRec, srcFields, b2] at e8 e9
  omega

/-- **A link record occurs at most once in `render`'s `par` records.** -/
theorem par_link_count {Ps : List InstPub} {fwd : List (Nat × Nat)} (h256 : Ps.length ≤ 256)
    (hn : ∀ τ, τ < Ps.length → (Ps.getD τ instD).n ≤ 64)
    {τ : Nat} (hτ : τ < Ps.length) {l : Nat} (hl : l < (Ps.getD τ instD).n * (Ps.getD τ instD).n) :
    ((render Ps fwd).par.map (·.map Fp.ofNat)).count ((linkRec τ (Ps.getD τ instD) l).map Fp.ofNat) ≤ 1 := by
  generalize hM : (linkRec τ (Ps.getD τ instD) l).map Fp.ofNat = M
  rw [render_par]
  rw [count_flatMap_one Fp.ofNat _ _ τ _ List.nodup_range (List.mem_range.2 hτ) ?_]
  · have hn' := hn τ hτ
    generalize hP : Ps.getD τ instD = P at hM hl hn'
    have hnn : P.n * P.n ≤ 4096 := Nat.mul_le_mul hn' hn'
    have hM1 : M[1]? = some (Fp.ofNat 4) := by rw [← hM]; simp [linkRec, PT_LINK]
    have tagne : ∀ r : List Nat, ∀ a, r[1]? = some a → a < 8 → a ≠ 4 → r.map Fp.ofNat ≠ M := by
      intro r a hr ha hne e
      rw [← e] at hM1
      exact hne (tag_of_map hr (by omega) (by decide) hM1)
    unfold parBlock
    simp only [List.map_append, List.count_append]
    have c1 : ([parCodec τ P].map (·.map Fp.ofNat)).count M = 0 :=
      count_map_zero _ _ _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact tagne _ 0 (by simp [parCodec]) (by decide) (by decide))
    have c2 : ((if P.raw.isEmpty then [] else [parScan τ P]).map (·.map Fp.ofNat)).count M = 0 :=
      count_map_zero _ _ _ (fun r hr => by
        split at hr
        · simp at hr
        · simp only [List.mem_singleton] at hr; subst hr
          exact tagne _ 1 (by simp [parScan, PT_SCAN]) (by decide) (by decide))
    have c3 : ((rawRecs τ P).map (·.map Fp.ofNat)).count M = 0 :=
      count_map_zero _ _ _ (fun r hr => by
        simp only [rawRecs, List.mem_map] at hr
        obtain ⟨⟨q, c⟩, -, rfl⟩ := hr
        exact tagne _ 2 (by simp [PT_RAW]) (by decide) (by decide))
    have c4 : ((shardRecs τ P).map (·.map Fp.ofNat)).count M = 0 :=
      count_map_zero _ _ _ (fun r hr => by
        obtain ⟨side, x, -, -, rfl⟩ := mem_shardRecs.1 hr
        exact tagne _ 3 (by simp [shardRec, PT_SHD]) (by decide) (by decide))
    have c5 : ((linkRecs τ P).map (·.map Fp.ofNat)).count M ≤ 1 := by
      unfold linkRecs
      rw [List.map_map]
      exact count_map_le_one _ M l _ List.nodup_range (fun y hy hyM => by
        rw [← hM] at hyM
        have := List.mem_range.1 hy
        exact linkRec_inj (by omega) (by omega) (by omega) hyM)
    omega
  · intro τ' hmem hne r hr
    rw [← hM]
    intro e
    have h1 := congrArg List.head? e
    have hh := parBlock_head hr
    cases r with
    | nil => simp at hh
    | cons a r =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simp only [List.map_cons, List.head?_cons, linkRec, List.cons_append, Option.some.injEq] at h1
      exact hne (ofNat_inj' (by have := List.mem_range.1 hmem; omega) (by omega) h1)

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tsd tcd : Nat}

/-- **One cell per link record.** -/
theorem cell_unique (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (I : PubIdx AP pub Fp.ofNat)
    (Ps : List InstPub) (fwd : List (Nat × Nat)) (hrec : I.recs B_SPAR true = (render Ps fwd).par)
    (h256 : Ps.length ≤ 256) (hn : ∀ τ, τ < Ps.length → (Ps.getD τ instD).n ≤ 64)
    {w1 w2 : Nat} (hw1 : w1 < tr.height tsd) (hc1 : cv tr tsd w1 Dist.kC = 1)
    (hw2 : w2 < tr.height tsd) (hc2 : cv tr tsd w2 Dist.kC = 1)
    (he : Scan.parV tr tsd w1 = Scan.parV tr tsd w2) : w1 = w2 := by
  have hS := Scan.SLocal.of_sd (sd_local hH OS)
  refine Classical.byContradiction fun hne => ?_
  have h2 := pub_two hH OS hw1 hw2 hne (par_mult' hS hw1 (Or.inr hc1)) (par_mult' hS hw2 (Or.inr hc2))
    (by rw [Scan.par_msg, Scan.par_msg, he])
  obtain ⟨hτ, l, hl, hpv⟩ := cell_rec hH OS I Ps fwd hrec h256 hw1 hc1
  rw [Scan.par_msg, hpv, I.count, hrec] at h2
  have := par_link_count (fwd := fwd) h256 hn hτ hl
  omega

/-- **The `SDG` sender of a codec record** is a cell that received the record's link record. -/
theorem codec_cell (hH : HoldsP AP pub tr) (OC : CodecValOwn AP tcd) (OS : ScanOwn AP tsd tp)
    (IO : InitOwn AP tcd tsd) (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrec : I.recs B_SPAR true = (render Ps fwd).par) (h256 : Ps.length ≤ 256)
    (hP : ∀ τ, τ < Ps.length → InstOk (Ps.getD τ instD))
    {f : Nat} (hf : f < tr.height tcd) (hF : cv tr tcd f Codec.kF = 1)
    {k : Nat} (hk : k < cv tr tcd f Codec.NN) :
    ∃ r', r' < tr.height tsd ∧ cv tr tsd r' Dist.kC = 1 ∧
      Scan.parV tr tsd r' = linkRec (cv tr tcd f Codec.tau) (Ps.getD (cv tr tcd f Codec.tau) instD) k ∧
      cv tr tsd r' Dist.gb = cv tr tcd (f + 5 + 24 * k + 23) Codec.gb := by
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
  have hkC : cv tr tsd r' Dist.kC = 1 := Codec.one_of_mult (i := ScanDist.interactions[9]!) rfl hm'
  obtain ⟨hτ', l, hl, hpv⟩ := cell_rec hH OS I Ps fwd hrec h256 hr' hkC
  have hn := (hP _ hτ').n64
  rw [ScanDist.sdg_msg, msg12] at hmsg
  generalize hQ : Ps.getD (cv tr tsd r' Dist.tau) instD = Q at hpv hl hn
  have hpv' := hpv
  simp only [Scan.parV, linkRec, srcFields, b2, List.cons_append, List.nil_append, List.cons.injEq] at hpv'
  obtain ⟨-, -, -, -, -, -, -, -, p6, p7, -, -⟩ := hpv'
  have hl0 : cv tr tsd r' Dist.llo = l % 256 := p6
  have hl1 : cv tr tsd r' Dist.lhi = l / 256 % 256 := p7
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hmsg
  obtain ⟨t0, t1, -, t3, -⟩ := hmsg
  have hnn : Q.n * Q.n ≤ 4096 := Nat.mul_le_mul hn hn
  have hτ := (ofNat_inj' (cv_lt _ _) (cv_lt _ _) t0).symm
  rw [hl0, hl1, show l % 256 + 256 * (l / 256 % 256) = l by omega] at t1
  have hkl := (ofNat_inj' (by omega) (by omega) t1).symm
  subst hkl
  refine ⟨r', hr', hkC, ?_, (ofNat_inj' (cv_lt _ _) (cv_lt _ _) t3)⟩
  rw [hpv, ← hQ, ← hτ]

end

/-! ## `GbGrid` -/

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tm tcmp ts tch tg tsd tcd : Nat}
variable {Ps : List InstPub} {I : PubIdx AP pub Fp.ofNat} {fwd : List (Nat × Nat)}

theorem sordOf_eq (n : Nat) (allowed : Array Bool) (sb : Array Nat) :
    sortByKey (fun y => avgLink (cntSd n allowed 0 y, sb[y]!)) (List.range n) = sordOf n allowed sb := rfl

theorem rordOf_eq (n : Nat) (allowed : Array Bool) (rb : Array Nat) :
    sortByKey (fun y => avgLink (cntSd n allowed 1 y, rb[y]!)) (List.range n) = rordOf n allowed rb := rfl

/-- An index of a permutation of `[0, n)` hitting `x < n`. -/
theorem exists_idx {l : List Nat} {n x : Nat} (hnd : l.Nodup) (hlt : ∀ y ∈ l, y < n) (hlen : l.length = n)
    (hx : x < n) : ∃ i, i < n ∧ l[i]! = x := by
  have hm := (mem_of_nodup_of_length n l hnd hlt hlen x).2 hx
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hm
  exact ⟨i, by omega, by rw [getElem!_pos l i hi, he]⟩

/-- **`GbGrid`**: the codec's `gb` of record `l` is the spec's grid grant. -/
theorem gbGrid_of (G : GridPub AP pub tr tsd tp Ps I fwd) (DX : SdlxOwn AP tsd)
    (OC : CodecValOwn AP tcd) (IO : InitOwn AP tcd tsd)
    {f m : Nat} {P : InstPub} {st : St}
    (C : MemCtx AP pub tr tp tm tcmp ts tch tg tsd tcd f m P P.allowed st)
    {τ : Nat} (hτl : τ < Ps.length) (hP : Ps.getD τ instD = P) (hτf : cv tr tp f Proc.tau = τ)
    {fc : Nat} (hfc : fc < tr.height tcd) (hF : cv tr tcd fc Codec.kF = 1)
    (hτc : cv tr tcd fc Codec.tau = τ) (hNN : cv tr tcd fc Codec.NN = P.n * P.n) :
    GbGrid tr tcd fc P.n (gridGrants P.n P.allowed
      (specSt P.n P.allowed (reqsOf P) tr tp f st m).senderBudget
      (specSt P.n P.allowed (reqsOf P) tr tp f st m).receiverBudget
      (sordOf P.n P.allowed (specSt P.n P.allowed (reqsOf P) tr tp f st m).senderBudget)
      (rordOf P.n P.allowed (specSt P.n P.allowed (reqsOf P) tr tp f st m).receiverBudget)) := by
  generalize hstF : specSt P.n P.allowed (reqsOf P) tr tp f st m = stF
  have hD := G.hD
  have PO := G.hP τ hτl
  rw [hP] at PO
  have hn1 : 1 ≤ P.n := PO.n1
  have hn64 : P.n ≤ 64 := PO.n64
  -- τ's section
  obtain ⟨w, hw, hs, hτw, -⟩ := shard_exists G.hH G.OS I Ps fwd G.hrec G.h256 G.hn hτl (side := 0) (x := 0)
    (by decide) (by rw [hP]; exact hn1)
  obtain ⟨w0, st0, hlo, hhi⟩ := Dist.cover (sd_local G.hH G.OS) G.hN w hw (Or.inl hs)
  have hN0 := G.hN w0 st0.1 st0.2.1
  have ic := Dist.ic_of hD st0 rfl hN0.1 hN0.2 hlo hhi
  have hτ0 : cv tr tsd w0 Dist.tau = τ := ic.1.symm.trans hτw
  obtain ⟨-, -, -, hnn0, -⟩ := shard_vals G.hH G.OS I Ps fwd G.hrec G.h256 G.hn st0.1 st0.2.1
  rw [hτ0, hP] at hnn0
  have S : SecOk tr tsd w0 τ P := ⟨st0, hτ0, hnn0, hn1, hn64⟩
  -- the final budgets of the shard rows
  have hL2 : ∀ sd x, sd < 2 → x < P.n → cv tr tsd (w0 + sd * P.n + x) Dist.L2 =
      if sd = 0 then stF.senderBudget[Dist.shardAt tr tsd w0 P.n sd x]! else
        stF.receiverBudget[Dist.shardAt tr tsd w0 P.n sd x]! := by
    intro sd x hsd hx
    obtain ⟨hwx, hsx, hside, -, htx, -, hrx, -⟩ :=
      sec_shard G.hH G.OS I Ps fwd G.hrec G.h256 G.hn hP S hsd hx
    have := shard_L2 C hwx hsx (by rw [htx, hτf]) (by omega) hrx
    rw [hside, hstF] at this
    exact this
  have hsb : ∀ x, x < P.n → cv tr tsd (w0 + 0 * P.n + x) Dist.L2 =
      stF.senderBudget[Dist.shardAt tr tsd w0 P.n 0 x]! := fun x hx => by
    rw [hL2 0 x (by decide) hx, if_pos rfl]
  have hrb : ∀ x, x < P.n → cv tr tsd (w0 + 1 * P.n + x) Dist.L2 =
      stF.receiverBudget[Dist.shardAt tr tsd w0 P.n 1 x]! := fun x hx => by
    rw [hL2 1 x (by decide) hx, if_neg (by decide)]
  -- the sorted orders
  have hso : Dist.sideList tr tsd w0 P.n 0 = sordOf P.n P.allowed stF.senderBudget := by
    rw [← sordOf_eq]
    exact (side_sorted G.hH G.OS C.O.cmp I Ps fwd G.hrec G.h256 G.hn hP S (sd := 0) (by decide)
      stF.senderBudget hsb).symm
  have hro : Dist.sideList tr tsd w0 P.n 1 = rordOf P.n P.allowed stF.receiverBudget := by
    rw [← rordOf_eq]
    exact (side_sorted G.hH G.OS C.O.cmp I Ps fwd G.hrec G.h256 G.hn hP S (sd := 1) (by decide)
      stF.receiverBudget hrb).symm
  have GC := G.grid_cells DX C.O.cmp hP S stF.senderBudget stF.receiverBudget _ _ hso hro hsb hrb
  obtain ⟨nd0, lt0, len0⟩ := side_nodup G.hH G.OS I Ps fwd G.hrec G.h256 G.hn hP S (sd := 0) (by decide)
  obtain ⟨nd1, lt1, len1⟩ := side_nodup G.hH G.OS I Ps fwd G.hrec G.h256 G.hn hP S (sd := 1) (by decide)
  rw [hso] at nd0 lt0 len0
  rw [hro] at nd1 lt1 len1
  intro l hl
  -- the cell of link `l`
  have hpos : 0 < P.n := hn1
  have hdl : l / P.n < P.n := by rw [Nat.div_lt_iff_lt_mul hpos]; exact hl
  have hml : l % P.n < P.n := Nat.mod_lt _ hpos
  obtain ⟨i, hi, hie⟩ := exists_idx nd0 lt0 len0 hdl
  obtain ⟨j, hj, hje⟩ := exists_idx nd1 lt1 len1 hml
  have hlk : (sordOf P.n P.allowed stF.senderBudget)[i]! * P.n +
      (rordOf P.n P.allowed stF.receiverBudget)[j]! = l := by
    rw [hie, hje, Nat.mul_comm]; exact Nat.div_add_mod l P.n
  obtain ⟨es, er, eSE, eRE, egb⟩ := GC i j hi hj
  obtain ⟨SR, HR, CR, -⟩ := Dist.block hD S.st S.nn S.n1 S.n64
  obtain ⟨hwc', hcc', -, -, hic⟩ := CR i j hi hj
  have hwc : Dist.cellAt w0 P.n i j < tr.height tsd := hwc'
  have hcc : cv tr tsd (Dist.cellAt w0 P.n i j) Dist.kC = 1 := hcc'
  have hτc' : cv tr tsd (Dist.cellAt w0 P.n i j) Dist.tau = τ := hic.1.trans S.tau
  have hnc : cv tr tsd (Dist.cellAt w0 P.n i j) Dist.nn = P.n := hic.2.trans S.nn
  obtain ⟨-, -, -, hpvc⟩ := G.cell_link hP hwc hcc hτc' hnc
    (by rw [es, hie]; exact hdl) (by rw [er, hje]; exact hml)
  rw [es, er, hlk] at hpvc
  -- the codec's `SDG` sender is that cell
  obtain ⟨r', hr', hkC, hpv', hgb'⟩ := codec_cell G.hH OC G.OS IO I Ps fwd G.hrec G.h256 G.hP hfc hF
    (by rw [hNN]; exact hl)
  rw [hτc, hP] at hpv'
  have hrc : r' = Dist.cellAt w0 P.n i j :=
    cell_unique G.hH G.OS I Ps fwd G.hrec G.h256 G.hn hr' hkC hwc hcc (by rw [hpv', hpvc])
  rw [← hgb', hrc, egb]
  -- the grid grant
  have hg := gridGrants_get P.n P.allowed stF.senderBudget stF.receiverBudget
    (sordOf P.n P.allowed stF.senderBudget) (rordOf P.n P.allowed stF.receiverBudget)
    (sortByKey_range_nodup _ _) (length_sortByKey_range _ _)
    (fun x hx => (mem_sortByKey_range _ _ x).1 hx)
    (sortByKey_range_nodup _ _) (length_sortByKey_range _ _)
    (fun x hx => (mem_sortByKey_range _ _ x).1 hx) i j hi hj
  rw [hlk] at hg
  rw [hg, hlk]
  split <;> rfl

end

end ZkFormal.NearV3.Sched
