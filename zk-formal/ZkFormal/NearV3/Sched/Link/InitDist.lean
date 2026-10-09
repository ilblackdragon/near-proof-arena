import ZkFormal.NearV3.Sched.Link.InitCodec

/-!
# ZkFormal.NearV3.Sched.Link.InitDist — the budget `INIT`s of the distribute shard rows (stage C)

A shard row `w` of `ssdV3` (`kSh = 1`) receives the public shard record
`shardRec τ P side x` (`shard_rec`, `τ < |Ps|`, `side < 2`, `x < n`) and sends on `SOP` the merged
message `(τ·2^14 + adr, b + kS, kS, s, s + bv, 0, 0, 0)` with `adr = 4096·(side + 1) + x`,
`b = s = kS = 0` and `bv = B₀ = budget0 P side x` (`Dist.shard_row`). So:

* **`shard_init_val`**: that message is `initRec τ allowed st (4096·(side + 1) + x)` for
  `st = lpState P.ids P.params P.allowed a0 P.seed` (any `a0`: the budgets after the link pass are
  `maxShardBandwidth − base·cnt`, `linkPass`'s `sb`/`rb`);
* **`shard_unique`**: two shard rows receiving the same record are the same row (the public
  record occurs once, `par_shard_count`, and `pub_two`);
* **`shard_exists`**: every shard record of an instance is received by a shard row (only
  `ssdV3` receives non-zero tags, `ScanOwn.parTag`).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

namespace Dist
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem kSh_eq (hL : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hs : cv tr t w kSh = 1)
    {x : Nat} {e : Expr} (he : Expr.mul (c kSh) (sub (c x) e) ∈ constraints) {v : Nat}
    (hv : zev (tenv tr t w pub) e = (v : Int)) (hvl : v < 2013265921) : cv tr t w x = v := by
  have h := hL.zc hw he
  simp only [zev_mul, zev_sub, zev_c, cur_cv, hs, hv] at h
  have := cv_lt (tr := tr) (t := t) w x
  have := h (by omega) (by omega)
  omega

theorem kSh_zero (hL : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hs : cv tr t w kSh = 1)
    {x : Nat} (he : Expr.mul (c kSh) (c x) ∈ constraints) : cv tr t w x = 0 := by
  have h := hL.zc hw he
  simp only [zev_mul, zev_c, cur_cv, hs] at h
  have := cv_lt (tr := tr) (t := t) w x
  have := h (by omega) (by omega)
  omega

/-- **The window and the memory `INIT` of a shard row.** -/
theorem shard_row (hL : DLocal tr t pub) {w : Nat} (hw : w < tr.height t) (hs : cv tr t w kSh = 1)
    (hside : cv tr t w side ≤ 1) (hshd : cv tr t w shd < 4096) (h0 : cv tr t w by0 < 256)
    (h1 : cv tr t w by1 < 256) (h2 : cv tr t w by2 < 256) :
    cv tr t w r = cv tr t w shd ∧ cv tr t w b = 0 ∧ cv tr t w s = 0 ∧
      cv tr t w adr = 4096 * (cv tr t w side + 1) + cv tr t w shd ∧
      cv tr t w bv = cv tr t w by0 + 256 * cv tr t w by1 + 65536 * cv tr t w by2 := by
  have er : cv tr t w r = cv tr t w shd := by
    have := kSh_eq hL hw hs (x := shd) (e := c r) (v := cv tr t w r) (by simp [constraints, cShard])
      (by simp only [zev_c, cur_cv]) (cv_lt _ _)
    exact this.symm
  refine ⟨er, ?_, ?_, ?_, ?_⟩
  · exact kSh_zero hL hw hs (x := b) (by simp [constraints, cShard])
  · exact kSh_zero hL hw hs (x := s) (by simp [constraints, cShard])
  · exact kSh_eq hL hw hs (x := adr) (e := .add (smul 4096 (.add (c side) (k 1))) (c r))
      (by simp [constraints, cShard]) (by simp only [zev_add, zev_smul, zev_c, zev_k, cur_cv, er]; omega)
      (by omega)
  · exact kSh_eq hL hw hs (x := bv) (e := b0E) (by simp [constraints, cShard])
      (by simp only [b0E, zev_add, zev_smul, zev_c, cur_cv]; omega) (by omega)

end Dist

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tsd tcd : Nat}

theorem getElem!_list_toArray_map {α : Type} [Inhabited α] (n : Nat) (g : Nat → Nat) (h : Nat → α)
    {x : Nat} (hx : x < n) : (((List.range n).map g).toArray.map h)[x]! = h (g x) := by
  simp [getElem!_def, hx]

theorem budget0_le (P : InstPub) (side x : Nat) : budget0 P side x ≤ P.params.maxShardBandwidth := by
  unfold budget0; exact Nat.sub_le _ _

/-- **The budget `INIT` of a shard row.** -/
theorem shard_init_val (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (I : PubIdx AP pub Fp.ofNat)
    (Ps : List InstPub) (fwd : List (Nat × Nat)) (hrec : I.recs B_SPAR true = (render Ps fwd).par)
    (h256 : Ps.length ≤ 256) (hP : ∀ τ, τ < Ps.length → InstOk (Ps.getD τ instD))
    {w : Nat} (hw : w < tr.height tsd) (hs : cv tr tsd w Dist.kSh = 1) (a0 : Nat → Nat) :
    cv tr tsd w Dist.tau < Ps.length ∧ ∃ side x, side < 2 ∧
      x < (Ps.getD (cv tr tsd w Dist.tau) instD).n ∧
      Scan.parV tr tsd w = shardRec (cv tr tsd w Dist.tau) (Ps.getD (cv tr tsd w Dist.tau) instD) side x ∧
      (ScanDist.interactions[4]!).msgVal tr tsd w pub =
        (initRec (cv tr tsd w Dist.tau) (Ps.getD (cv tr tsd w Dist.tau) instD).allowed
          (lpState (Ps.getD (cv tr tsd w Dist.tau) instD).ids (Ps.getD (cv tr tsd w Dist.tau) instD).params
            (Ps.getD (cv tr tsd w Dist.tau) instD).allowed a0 (Ps.getD (cv tr tsd w Dist.tau) instD).seed)
          (4096 * (side + 1) + x)).map Fp.ofNat := by
  have hSD := sd_local hH OS
  have hS := Scan.SLocal.of_sd hSD
  have hD := Dist.DLocal.of_sd hSD
  obtain ⟨hτ, side, x, hs2, hx, hpv⟩ := shard_rec hH OS I Ps fwd hrec h256 (fun τ h => (hP τ h).n64) hw hs
  refine ⟨hτ, side, x, hs2, hx, hpv, ?_⟩
  have PO := hP _ hτ
  have F := Scan.row_flags hS hw
  have hkS : cv tr tsd w Scan.kS = 0 := by
    have hs' : cv tr tsd w Scan.kSh = 1 := hs
    omega
  generalize hPdef : Ps.getD (cv tr tsd w Dist.tau) instD = P at hpv hx PO
  have hn := PO.n64
  obtain ⟨hMS, -, -, -, -, -⟩ := pv86_facts PO.n1 PO.params
  have hB := budget0_le P side x
  rw [hMS] at hB
  simp only [Scan.parV, shardRec, b3, List.cons_append, List.nil_append, List.cons.injEq] at hpv
  obtain ⟨-, -, p0, p1, -, p3, p4, p5, -⟩ := hpv
  have es : cv tr tsd w Dist.side = side := p0
  have ex : cv tr tsd w Dist.shd = x := p1
  have e0 : cv tr tsd w Dist.by0 = budget0 P side x % 256 := p3
  have e1 : cv tr tsd w Dist.by1 = budget0 P side x / 256 % 256 := p4
  have e2 : cv tr tsd w Dist.by2 = budget0 P side x / 65536 % 256 := p5
  have hnx : x < 64 := by unfold InstPub.n at hx; omega
  obtain ⟨-, eb, es0, eadr, ebv⟩ := Dist.shard_row hD hw hs (by omega) (by omega) (by omega) (by omega)
    (by omega)
  rw [e0, e1, e2, b3_sum _ (by omega)] at ebv
  rw [es, ex] at eadr
  have eadr' : cv tr tsd w Scan.link = 4096 * (side + 1) + x := eadr
  have eb' : cv tr tsd w Scan.cid = 0 := eb
  have es0' : cv tr tsd w Scan.key = 0 := es0
  have ebv' : cv tr tsd w Scan.bvz = budget0 P side x := ebv
  have htau' : cv tr tsd w Scan.tau = cv tr tsd w Dist.tau := rfl
  rw [Scan.op_msg, eadr', eb', es0', ebv', hkS, htau']
  congr 1
  have hxn : x < P.ids.length := hx
  have hrd : rd (cv tr tsd w Dist.tau) (lpState P.ids P.params P.allowed a0 P.seed)
      (cv tr tsd w Dist.tau * 16384 + (4096 * (side + 1) + x)) = budget0 P side x := by
    unfold rd
    rw [show cv tr tsd w Dist.tau * 16384 + (4096 * (side + 1) + x) - cv tr tsd w Dist.tau * 16384 =
      4096 * (side + 1) + x by omega, if_neg (by omega)]
    rcases (by omega : side = 0 ∨ side = 1) with rfl | rfl
    · rw [if_pos (by omega), show 4096 * (0 + 1) + x - 4096 = x by omega]
      simp only [lpState, linkPass]
      rw [getElem!_list_toArray_map _ _ _ hxn]
      simp [budget0, cntS, InstPub.n]
    · rw [if_neg (by omega), show 4096 * (1 + 1) + x - 8192 = x by omega]
      simp only [lpState, linkPass]
      rw [getElem!_list_toArray_map _ _ _ hxn]
      simp [budget0, cntR, InstPub.n]
  rw [initRec, if_neg (by omega), if_neg (by omega), if_neg (by omega), hrd,
    Nat.mul_comm (cv tr tsd w Dist.tau) 16384, Nat.zero_add, Nat.zero_add]
  rfl

/-! ## One shard row per shard record -/

theorem count_map_le_one {α β : Type} [BEq β] [LawfulBEq β] (g : α → β) (M : β) (a0 : α) :
    ∀ l : List α, l.Nodup → (∀ y ∈ l, g y = M → y = a0) → (l.map g).count M ≤ 1
  | [], _, _ => by simp
  | a :: l, hnd, h => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.count_cons]
    by_cases ha : g a = M
    · have e := h a List.mem_cons_self ha
      have : (l.map g).count M = 0 := by
        rw [List.count_eq_zero]
        intro hm
        obtain ⟨y, hy, hy'⟩ := List.mem_map.1 hm
        have := h y (List.mem_cons_of_mem _ hy) hy'
        exact hnd.1 (by rw [e, ← this]; exact hy)
      rw [this]; simp [ha]
    · have := count_map_le_one g M a0 l hnd.2 (fun y hy => h y (List.mem_cons_of_mem _ hy))
      have : (g a == M) = false := by simpa using ha
      simp [this]; omega

theorem count_map_zero {α β : Type} [BEq β] [LawfulBEq β] (g : α → β) (M : β) (l : List α)
    (h : ∀ y ∈ l, g y ≠ M) : (l.map g).count M = 0 := by
  rw [List.count_eq_zero]
  intro hm
  obtain ⟨y, hy, hy'⟩ := List.mem_map.1 hm
  exact h y hy hy'

theorem shardRec_inj {τ : Nat} {P : InstPub} (hτ : τ < 256) (hn : P.n ≤ 64) {s1 x1 s2 x2 : Nat}
    (hs1 : s1 < 2) (hx1 : x1 < P.n) (hs2 : s2 < 2) (hx2 : x2 < P.n)
    (h : (shardRec τ P s1 x1).map Fp.ofNat = (shardRec τ P s2 x2).map Fp.ofNat) : s1 = s2 ∧ x1 = x2 := by
  have e := ofNat_list_inj (shardRec_lt hτ hn hs1 hx1) (shardRec_lt hτ hn hs2 hx2) h
  simp only [shardRec, List.cons_append, List.cons.injEq] at e
  exact ⟨e.2.2.1, e.2.2.2.1⟩

theorem shardRecs_split (τ : Nat) (P : InstPub) :
    shardRecs τ P = (List.range P.n).map (shardRec τ P 0) ++ (List.range P.n).map (shardRec τ P 1) := by
  simp only [shardRecs, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

/-- **A shard record occurs at most once in `render`'s `par` records.** -/
theorem par_shard_count {Ps : List InstPub} {fwd : List (Nat × Nat)} (h256 : Ps.length ≤ 256)
    (hn : ∀ τ, τ < Ps.length → (Ps.getD τ instD).n ≤ 64)
    {τ : Nat} (hτ : τ < Ps.length) {side x : Nat} (hs : side < 2) (hx : x < (Ps.getD τ instD).n) :
    ((render Ps fwd).par.map (·.map Fp.ofNat)).count
      ((shardRec τ (Ps.getD τ instD) side x).map Fp.ofNat) ≤ 1 := by
  generalize hM : (shardRec τ (Ps.getD τ instD) side x).map Fp.ofNat = M
  rw [render_par]
  rw [count_flatMap_one Fp.ofNat _ _ τ _ List.nodup_range (List.mem_range.2 hτ) ?_]
  · have hn' := hn τ hτ
    generalize hP : Ps.getD τ instD = P at hM hx hn'
    have hM1 : M[1]? = some (Fp.ofNat 3) := by rw [← hM]; simp [shardRec, PT_SHD]
    have tagne : ∀ r : List Nat, ∀ a, r[1]? = some a → a < 8 → a ≠ 3 → r.map Fp.ofNat ≠ M := by
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
    have c5 : ((linkRecs τ P).map (·.map Fp.ofNat)).count M = 0 :=
      count_map_zero _ _ _ (fun r hr => by
        obtain ⟨l, -, rfl⟩ := mem_linkRecs.1 hr
        exact tagne _ 4 (by simp [linkRec, PT_LINK]) (by decide) (by decide))
    have c4 : ((shardRecs τ P).map (·.map Fp.ofNat)).count M ≤ 1 := by
      rw [shardRecs_split, List.map_append, List.count_append, List.map_map, List.map_map]
      have inner : ∀ s', s' < 2 → ((List.range P.n).map ((·.map Fp.ofNat) ∘ shardRec τ P s')).count M ≤
          if s' = side then 1 else 0 := by
        intro s' hs'
        split
        · next e =>
          subst e
          exact count_map_le_one _ M x _ List.nodup_range (fun y hy hyM => by
            rw [← hM] at hyM
            exact (shardRec_inj (by omega) hn' hs' (List.mem_range.1 hy) hs' hx hyM).2)
        · next e =>
          apply Nat.le_of_eq
          apply count_map_zero
          intro y hy hyM
          rw [← hM] at hyM
          exact e (shardRec_inj (by omega) hn' hs' (List.mem_range.1 hy) hs hx hyM).1
      have i0 := inner 0 (by decide)
      have i1 := inner 1 (by decide)
      split at i0 <;> split at i1 <;> omega
    omega
  · intro τ' hmem hne r hr
    rw [← hM]
    intro e
    have h1 := congrArg List.head? e
    obtain ⟨-, hh⟩ : True ∧ r.head? = some τ' := ⟨trivial, parBlock_head hr⟩
    cases r with
    | nil => simp at hh
    | cons a r =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simp only [List.map_cons, List.head?_cons, shardRec, List.cons_append, Option.some.injEq] at h1
      exact hne (ofNat_inj' (by have := List.mem_range.1 hmem; omega) (by omega) h1)

/-- **One shard row per shard record.** -/
theorem shard_unique (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (I : PubIdx AP pub Fp.ofNat)
    (Ps : List InstPub) (fwd : List (Nat × Nat)) (hrec : I.recs B_SPAR true = (render Ps fwd).par)
    (h256 : Ps.length ≤ 256) (hn : ∀ τ, τ < Ps.length → (Ps.getD τ instD).n ≤ 64)
    {w1 w2 : Nat} (hw1 : w1 < tr.height tsd) (hs1 : cv tr tsd w1 Dist.kSh = 1)
    (hw2 : w2 < tr.height tsd) (hs2 : cv tr tsd w2 Dist.kSh = 1)
    (he : Scan.parV tr tsd w1 = Scan.parV tr tsd w2) : w1 = w2 := by
  have hS := Scan.SLocal.of_sd (sd_local hH OS)
  refine Classical.byContradiction fun hne => ?_
  have h2 := pub_two hH OS hw1 hw2 hne (par_mult' hS hw1 (Or.inl hs1)) (par_mult' hS hw2 (Or.inl hs2))
    (by rw [Scan.par_msg, Scan.par_msg, he])
  obtain ⟨hτ, side, x, hs, hx, hpv⟩ := shard_rec hH OS I Ps fwd hrec h256 hn hw1 hs1
  rw [Scan.par_msg, hpv, I.count, hrec] at h2
  have := par_shard_count (fwd := fwd) h256 hn hτ hs hx
  omega

/-- **Every shard record is received by a shard row.** -/
theorem shard_exists (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (I : PubIdx AP pub Fp.ofNat)
    (Ps : List InstPub) (fwd : List (Nat × Nat)) (hrec : I.recs B_SPAR true = (render Ps fwd).par)
    (h256 : Ps.length ≤ 256) (hn : ∀ τ, τ < Ps.length → (Ps.getD τ instD).n ≤ 64)
    {τ : Nat} (hτ : τ < Ps.length) {side x : Nat} (hs : side < 2) (hx : x < (Ps.getD τ instD).n) :
    ∃ w, w < tr.height tsd ∧ cv tr tsd w Dist.kSh = 1 ∧ cv tr tsd w Dist.tau = τ ∧
      Scan.parV tr tsd w = shardRec τ (Ps.getD τ instD) side x := by
  have hL := sd_local hH OS
  have hS := Scan.SLocal.of_sd hL
  obtain ⟨M, hMd⟩ : ∃ M, M = (shardRec τ (Ps.getD τ instD) side x).map Fp.ofNat := ⟨_, rfl⟩
  have hpc : 1 ≤ pubCount AP pub B_SPAR true M := by
    rw [I.count, hrec, hMd, render_par]
    apply List.count_pos_iff.2
    refine List.mem_map.2 ⟨_, List.mem_flatMap.2 ⟨τ, List.mem_range.2 hτ, ?_⟩, rfl⟩
    unfold parBlock
    simp only [List.mem_append]
    exact Or.inl (Or.inr (mem_shardRecs.2 ⟨side, x, hs, hx, rfl⟩))
  rw [par_count hH OS] at hpc
  unfold busCount at hpc
  obtain ⟨t, ht, htc⟩ := busCount_go_pos tr pub _ _ M AP.tables 0 (Nat.pos_iff_ne_zero.1 hpc)
  rw [Nat.zero_add] at htc
  obtain ⟨w, hw, i, hi, hb, hs', hmsg, hm⟩ := exists_of_tableBusCount htc
  have hlt := shardRec_lt (τ := τ) (P := Ps.getD τ instD) (by omega) (hn τ hτ) hs hx
  by_cases htd : t = tsd
  · subst htd
    rw [OS.tab] at hi
    have hi0 := Scan.par_cases i hi hb
    subst hi0
    rw [Scan.par_msg] at hmsg
    have he := ofNat_list_inj (Scan.parV_lt hS hw) hlt (hmsg.trans hMd)
    have htag : cv tr t w Scan.kP + 2 * cv tr t w Scan.kS + 3 * cv tr t w Scan.kSh +
        4 * cv tr t w Scan.kC = 3 := by
      have := congrArg (·[1]?) he
      simpa [Scan.parV, shardRec, PT_SHD] using this
    have F := Scan.row_flags hS hw
    have hsh : cv tr t w Dist.kSh = 1 := by
      have : cv tr t w Scan.kSh = 1 := by omega
      exact this
    have hτw : cv tr t w Dist.tau = τ := by
      have := congrArg List.head? he
      simpa [Scan.parV, shardRec, Scan.tau] using this
    exact ⟨w, hw, hsh, hτw, he⟩
  · have h1 := OS.parTag t ht htd i hi hb
    have e := congrArg (·[1]?) hmsg
    rw [hMd] at e
    simp only [Interaction.msgVal, List.getElem?_map, h1, shardRec, List.map_cons, List.cons_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at e
    have : (k 0).eval tr t w pub = Fp.ofNat 0 := Scan.eval_ofNat (by simp [zev_k])
    rw [this] at e
    exact absurd ((Proc.ofNat_cv_eq (by decide) (by decide)).1 e) (by simp [PT_SHD])

end

end ZkFormal.NearV3.Sched
