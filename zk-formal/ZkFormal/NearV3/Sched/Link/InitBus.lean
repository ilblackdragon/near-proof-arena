import ZkFormal.NearV3.Sched.Pub.ParSmall
import ZkFormal.NearV3.Sched.Link.MemTau
import ZkFormal.NearV3.Sched.View.CodecState

/-!
# ZkFormal.NearV3.Sched.Link.InitBus — buses and public records for the `INIT` link (stage C)

Generic pieces for `InitVals` (`Link/InitVals.lean`):

* **`InitOwn`** (ownership, decidable on the final AIR): only `schV3` (`tcd`) and `ssdV3` (`tsd`)
  have an `SPAR` interaction; only `ssdV3` sends on `SDG` and only `schV3` on `SA0`; no public
  segment sends on `SDG` or `SA0`;
* counting: `tbc_single` (a table with one interaction on a bus side), `sum_le_one`,
  `multNat_le1`;
* the `SPAR` records of `render` by tag: `shardRec` (tag 3), `linkRec` (tag 4), `par_cases`;
* `ssdV3` rows: a shard row (`kSh`) receives `shardRec τ' P' side x`, a cell (`kC`) receives
  `linkRec τ' P' l` (`shard_rec`, `cell_rec`), with `τ' < |Ps|`;
* `schV3` rows: every `rend` row is the end of a record `k < N` of an instance block
  (**`Codec.rend_rec`**).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-- **Ownership for the `INIT` link** (decidable on the final AIR). -/
structure InitOwn (AP : AirP) (tcd tsd : Nat) : Prop where
  parRecv : ∀ t, t < AP.tables.length → t ≠ tcd → t ≠ tsd → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus ≠ B_SPAR
  dgOnly : ∀ t, t < AP.tables.length → t ≠ tsd → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SDG → i.send = false
  dgPub : ∀ seg ∈ AP.pubSegs, seg.bus = B_SDG → seg.send = false
  a0Only : ∀ t, t < AP.tables.length → t ≠ tcd → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = B_SA0 → i.send = false
  a0Pub : ∀ seg ∈ AP.pubSegs, seg.bus = B_SA0 → seg.send = false

/-! ## Counting -/

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

theorem rowTraffic_filter (is : List Interaction) (tr : Trace F) (t r : Nat) (pub : List F) (b : Nat)
    (s : Bool) : rowTraffic is tr t r pub b s =
      rowTraffic (is.filter fun i => decide (i.bus = b ∧ i.send = s)) tr t r pub b s := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    unfold rowTraffic at ih ⊢
    rw [List.flatMap_cons, ih]
    by_cases h : i.bus = b ∧ i.send = s
    · rw [List.filter_cons_of_pos (by simpa using h), List.flatMap_cons, if_pos h]
    · rw [List.filter_cons_of_neg (by simpa using h), if_neg h, List.nil_append]

/-- A table with a single interaction on a bus side counts that interaction's rows. -/
theorem tbc_single {is : List Interaction} {tr : Trace F} {t : Nat} {pub : List F} {b : Nat} {s : Bool}
    {i0 : Interaction} (hf : is.filter (fun i => decide (i.bus = b ∧ i.send = s)) = [i0]) (M : List F) :
    tableBusCount is tr t pub b s M =
      ((List.range (tr.height t)).map fun r =>
        if i0.msgVal tr t r pub = M then i0.multNat tr t r pub else 0).sum := by
  have hb : i0.bus = b ∧ i0.send = s := by
    have : i0 ∈ is.filter (fun i => decide (i.bus = b ∧ i.send = s)) := by rw [hf]; simp
    simpa using (List.mem_filter.1 this).2
  rw [tableBusCount_eq, count_flatMap_rows]
  congr 1
  apply List.map_congr_left
  intro r _
  rw [rowTraffic_filter, hf]
  simp only [rowTraffic, List.flatMap_cons, List.flatMap_nil, List.append_nil, if_pos hb,
    List.count_replicate]
  by_cases e : i0.msgVal tr t r pub = M
  · simp [e]
  · simp [e, Ne.symm e]

end

theorem sum_zero_of (g : Nat → Nat) : ∀ (l : List Nat), (∀ r ∈ l, g r = 0) → (l.map g).sum = 0
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      sum_zero_of g l (fun r hr => h r (List.mem_cons_of_mem _ hr))]

/-- A sum of bits over distinct rows with at most one nonzero term is `≤ 1`. -/
theorem sum_le_one (g : Nat → Nat) : ∀ (l : List Nat), (∀ r ∈ l, g r ≤ 1) →
    (∀ r1 ∈ l, ∀ r2 ∈ l, g r1 ≠ 0 → g r2 ≠ 0 → r1 = r2) → l.Nodup → (l.map g).sum ≤ 1
  | [], _, _, _ => by simp
  | a :: l, h1, hu, hnd => by
    rw [List.map_cons, List.sum_cons]
    rw [List.nodup_cons] at hnd
    by_cases ha : g a = 0
    · rw [ha, Nat.zero_add]
      exact sum_le_one g l (fun r hr => h1 r (List.mem_cons_of_mem _ hr))
        (fun r1 h1' r2 h2' => hu r1 (List.mem_cons_of_mem _ h1') r2 (List.mem_cons_of_mem _ h2')) hnd.2
    · have : (l.map g).sum = 0 := sum_zero_of g l (fun r hr => by
        by_cases hz : g r = 0
        · exact hz
        · exact absurd (hu a List.mem_cons_self r (List.mem_cons_of_mem _ hr) ha hz ▸ hr) hnd.1)
      have := h1 a List.mem_cons_self
      omega

theorem multNat_le1 {tr : Trace Fp} {t r : Nat} {pub : List Fp} {i : Interaction} {e : Expr}
    (hm : i.mult = [e]) : i.multNat tr t r pub ≤ 1 := by
  unfold Interaction.multNat
  rw [hm]
  simp only [Interaction.multNat.go]
  split <;> simp

/-! ## The `SPAR` records by tag -/

/-- Shard record `(τ, 3, side, x, links, B₀ (3 bytes), n, 0, 0)`. -/
def shardRec (τ : Nat) (P : InstPub) (side x : Nat) : List Nat :=
  [τ, PT_SHD, side, x, if side = 0 then cntS P.n P.allowed x else cntR P.n P.allowed x] ++
    b3 (budget0 P side x) ++ [P.n, 0, 0]

/-- Link record `(τ, 4, src (2 bytes), hasSrc, use, 0, 0, l (2 bytes), allowed)`. -/
def linkRec (τ : Nat) (P : InstPub) (l : Nat) : List Nat :=
  [τ, PT_LINK] ++ srcFields P.ids l ++ [0, 0] ++ b2 l ++ [P.al l]

theorem mem_shardRecs {τ : Nat} {P : InstPub} {r : List Nat} :
    r ∈ shardRecs τ P ↔ ∃ side x, side < 2 ∧ x < P.n ∧ r = shardRec τ P side x := by
  simp only [shardRecs, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨side, hs, x, hx, rfl⟩
    exact ⟨side, x, by omega, hx, rfl⟩
  · rintro ⟨side, x, hs, hx, rfl⟩
    exact ⟨side, by omega, x, hx, rfl⟩

theorem mem_linkRecs {τ : Nat} {P : InstPub} {r : List Nat} :
    r ∈ linkRecs τ P ↔ ∃ l, l < P.n * P.n ∧ r = linkRec τ P l := by
  simp only [linkRecs, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, rfl⟩

/-- **The records of a block by tag.** -/
theorem par_cases {τ : Nat} {P : InstPub} {r : List Nat} (hr : r ∈ parBlock τ P) :
    r = parCodec τ P ∨ r[1]? = some 1 ∨ r[1]? = some 2 ∨
      (∃ side x, side < 2 ∧ x < P.n ∧ r = shardRec τ P side x) ∨
      (∃ l, l < P.n * P.n ∧ r = linkRec τ P l) := by
  simp only [parBlock, List.mem_append, List.mem_singleton] at hr
  rcases hr with (((rfl | hr) | hr) | hr) | hr
  · exact Or.inl rfl
  · split at hr
    · simp at hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact Or.inr (Or.inl (by simp [parScan, PT_SCAN]))
  · simp only [rawRecs, List.mem_map] at hr
    obtain ⟨⟨q, c⟩, -, rfl⟩ := hr
    exact Or.inr (Or.inr (Or.inl (by simp [PT_RAW])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_shardRecs.1 hr))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_linkRecs.1 hr))))

theorem tag_of_map {r : List Nat} {a b : Nat} (hr : r[1]? = some a) (ha : a < 2013265921)
    (hb : b < 2013265921) (h : (r.map Fp.ofNat)[1]? = some (Fp.ofNat b)) : a = b := by
  rw [List.getElem?_map, hr] at h
  simp only [Option.map_some, Option.some.injEq] at h
  exact ofNat_inj' ha hb h

theorem cnt_le (n : Nat) (allowed : Array Bool) (side x : Nat) :
    (if side = 0 then cntS n allowed x else cntR n allowed x) ≤ n := by
  split
  · unfold cntS; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  · unfold cntR; exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem shardRec_lt {τ : Nat} {P : InstPub} (hτ : τ < 256) (hn : P.n ≤ 64) {side x : Nat}
    (hs : side < 2) (hx : x < P.n) : ∀ y ∈ shardRec τ P side x, y < 2013265921 := by
  have hc := cnt_le P.n P.allowed side x
  intro y hy
  simp only [shardRec, b3, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with ((h | h | h | h | h) | h | h | h) | h | h | h <;> subst h <;>
    first | omega | (simp only [PT_SHD]; omega)

theorem al_le (P : InstPub) (l : Nat) : P.al l ≤ 1 := by unfold InstPub.al; split <;> omega

theorem linkRec_lt {τ : Nat} {P : InstPub} (hτ : τ < 256) (l : Nat) :
    ∀ y ∈ linkRec τ P l, y < 2013265921 := by
  have := al_le P l
  intro y hy
  simp only [linkRec, srcFields, b2, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with ((((h | h) | (h | h) | h | h) | h | h) | h | h) | h <;> subst h <;>
    first | omega | (simp only [PT_LINK]; omega) | (split <;> omega)

/-! ## The public records received by `ssdV3` -/

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tsd tp : Nat}

/-- A row of `ssdV3` receiving on `SPAR` receives a record of some block `τ' < |Ps|`. -/
theorem sd_rec (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (I : PubIdx AP pub Fp.ofNat)
    (Ps : List InstPub) (fwd : List (Nat × Nat)) (hrec : I.recs B_SPAR true = (render Ps fwd).par)
    {w : Nat} (hw : w < tr.height tsd) (hm : (ScanDist.interactions[0]!).multNat tr tsd w pub ≠ 0) :
    ∃ τ', τ' < Ps.length ∧ ∃ r ∈ parBlock τ' (Ps.getD τ' instD),
      r.map Fp.ofNat = (Scan.parV tr tsd w).map Fp.ofNat := by
  have h1 := pub_of_row hH OS hw hm
  rw [Scan.par_msg, I.count, hrec] at h1
  obtain ⟨r, hr, e⟩ := List.mem_map.1 (List.count_pos_iff.1 h1)
  rw [render_par, List.mem_flatMap] at hr
  obtain ⟨τ', hτ', hr⟩ := hr
  exact ⟨τ', List.mem_range.1 hτ', r, hr, e⟩

theorem par_mult' (hL : Scan.SLocal tr tsd pub) {w : Nat} (hw : w < tr.height tsd)
    (h : cv tr tsd w Dist.kSh = 1 ∨ cv tr tsd w Dist.kC = 1) :
    (ScanDist.interactions[0]!).multNat tr tsd w pub ≠ 0 := by
  have F := Scan.row_flags hL hw
  have hf := Scan.bool_of hL hw (x := Scan.fQ) (by simp [Scan.boolCols, Scan.ownBool])
  apply Mem.multNat_ne_of (e := .add (c Scan.kP) (.add (c Scan.fQ) (.add (c Dist.kSh) (c Dist.kC)))) rfl
  rw [Scan.eval_ofNat (v := 1) (by simp only [zev_add, zev_c, cur_cv]; simp only [Scan.kSh, Scan.kC] at F; omega)]
  rfl

/-- **A shard row receives `shardRec τ' P' side x`.** -/
theorem shard_rec (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (I : PubIdx AP pub Fp.ofNat)
    (Ps : List InstPub) (fwd : List (Nat × Nat)) (hrec : I.recs B_SPAR true = (render Ps fwd).par)
    (h256 : Ps.length ≤ 256) (hP : ∀ τ, τ < Ps.length → (Ps.getD τ instD).n ≤ 64)
    {w : Nat} (hw : w < tr.height tsd) (hs : cv tr tsd w Dist.kSh = 1) :
    cv tr tsd w Dist.tau < Ps.length ∧ ∃ side x, side < 2 ∧
      x < (Ps.getD (cv tr tsd w Dist.tau) instD).n ∧
      Scan.parV tr tsd w = shardRec (cv tr tsd w Dist.tau) (Ps.getD (cv tr tsd w Dist.tau) instD) side x := by
  have hS := Scan.SLocal.of_sd (sd_local hH OS)
  obtain ⟨τ', hτ', r, hr, e⟩ := sd_rec hH OS I Ps fwd hrec hw (par_mult' hS hw (Or.inl hs))
  have F := Scan.row_flags hS hw
  have htag : (Scan.parV tr tsd w)[1]? = some 3 := by
    have hs' : cv tr tsd w Scan.kSh = 1 := hs
    simp only [Scan.parV, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
    omega
  have ht : (r.map Fp.ofNat)[1]? = some (Fp.ofNat 3) := by
    rw [e, List.getElem?_map, htag]; rfl
  rcases par_cases hr with rfl | h | h | ⟨side, x, hs2, hx, rfl⟩ | ⟨l, hl, rfl⟩
  · exact absurd (tag_of_map (a := 0) (by simp [parCodec]) (by decide) (by decide) ht) (by decide)
  · exact absurd (tag_of_map h (by decide) (by decide) ht) (by decide)
  · exact absurd (tag_of_map h (by decide) (by decide) ht) (by decide)
  · have hl := ofNat_list_inj (shardRec_lt (by omega) (hP τ' hτ') hs2 hx) (Scan.parV_lt hS hw) e
    have h0 : cv tr tsd w Dist.tau = τ' := by
      have := congrArg List.head? hl
      simpa [shardRec, Scan.parV, Scan.tau] using this.symm
    rw [h0]
    exact ⟨hτ', side, x, hs2, hx, hl.symm⟩
  · exact absurd (tag_of_map (a := 4) (by simp [linkRec, PT_LINK]) (by decide) (by decide) ht) (by decide)

/-- **A cell receives `linkRec τ' P' l`.** -/
theorem cell_rec (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (I : PubIdx AP pub Fp.ofNat)
    (Ps : List InstPub) (fwd : List (Nat × Nat)) (hrec : I.recs B_SPAR true = (render Ps fwd).par)
    (h256 : Ps.length ≤ 256)
    {w : Nat} (hw : w < tr.height tsd) (hc : cv tr tsd w Dist.kC = 1) :
    cv tr tsd w Dist.tau < Ps.length ∧ ∃ l, l < (Ps.getD (cv tr tsd w Dist.tau) instD).n *
      (Ps.getD (cv tr tsd w Dist.tau) instD).n ∧
      Scan.parV tr tsd w = linkRec (cv tr tsd w Dist.tau) (Ps.getD (cv tr tsd w Dist.tau) instD) l := by
  have hS := Scan.SLocal.of_sd (sd_local hH OS)
  obtain ⟨τ', hτ', r, hr, e⟩ := sd_rec hH OS I Ps fwd hrec hw (par_mult' hS hw (Or.inr hc))
  have F := Scan.row_flags hS hw
  have htag : (Scan.parV tr tsd w)[1]? = some 4 := by
    have hc' : cv tr tsd w Scan.kC = 1 := hc
    simp only [Scan.parV, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
    omega
  have ht : (r.map Fp.ofNat)[1]? = some (Fp.ofNat 4) := by
    rw [e, List.getElem?_map, htag]; rfl
  rcases par_cases hr with rfl | h | h | ⟨side, x, hs2, hx, rfl⟩ | ⟨l, hl, rfl⟩
  · exact absurd (tag_of_map (a := 0) (by simp [parCodec]) (by decide) (by decide) ht) (by decide)
  · exact absurd (tag_of_map h (by decide) (by decide) ht) (by decide)
  · exact absurd (tag_of_map h (by decide) (by decide) ht) (by decide)
  · exact absurd (tag_of_map (a := 3) (by simp [shardRec, PT_SHD]) (by decide) (by decide) ht) (by decide)
  · have hl' := ofNat_list_inj (linkRec_lt (by omega) l) (Scan.parV_lt hS hw) e
    have h0 : cv tr tsd w Dist.tau = τ' := by
      have := congrArg List.head? hl'
      simpa [linkRec, Scan.parV, Scan.tau] using this.symm
    rw [h0]
    exact ⟨hτ', l, hl, hl'.symm⟩

end

/-! ## Record ends of the codec -/

namespace Codec
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- **Every `rend` row is the end of a record `k < N` of an instance block.** -/
theorem rend_rec (hL : CLocal tr t pub) (hH : tr.height t ≤ 2 ^ 22) {r : Nat} (hr : r < tr.height t)
    (hrd : cv tr t r rend = 1) :
    ∃ f k, f < tr.height t ∧ cv tr t f kF = 1 ∧ k < cv tr t f NN ∧ r = f + 5 + 24 * k + 23 := by
  have K := kinds hL hr
  have hA := (rend_row hL hr hrd).1
  have hact : cv tr t r act = 1 := by omega
  obtain ⟨f, hfr, hF, hrf⟩ := codec_cover hL hH r hr hact
  have hf : f < tr.height t := by omega
  obtain ⟨-, -, -, -, -, -, HR, RR, -, ZR, -, AR, -⟩ := codec_block hL hH hf hF
  by_cases h1 : r - f < 5
  · obtain ⟨-, hk, -⟩ := HR (r - f) h1
    rw [show f + (r - f) = r by omega] at hk
    omega
  by_cases h2 : r - f < 5 + 24 * cv tr t f NN
  · have hk : (r - f - 5) / 24 < cv tr t f NN := by omega
    have ho : (r - f - 5) % 24 < 24 := Nat.mod_lt _ (by decide)
    have hR := RR _ hk _ ho
    have e : f + 5 + 24 * ((r - f - 5) / 24) + (r - f - 5) % 24 = r := by omega
    have F := rrow_flags hL hR ho
    rw [e] at F
    have h23 : (r - f - 5) % 24 = 23 := by
      have := F.2.2.2.2.1; rw [hrd] at this; split at this <;> omega
    exact ⟨f, (r - f - 5) / 24, hf, hF, hk, by omega⟩
  by_cases h3 : r - f < 5 + 24 * cv tr t f NN + 32
  · obtain ⟨-, hk, -⟩ := ZR (r - f - (5 + 24 * cv tr t f NN)) (by omega)
    rw [show f + 5 + 24 * cv tr t f NN + (r - f - (5 + 24 * cv tr t f NN)) = r by omega] at hk
    omega
  · obtain ⟨-, hk, -⟩ := AR (r - f - (5 + 24 * cv tr t f NN + 32)) (by omega)
    rw [show f + 5 + 24 * cv tr t f NN + 32 + (r - f - (5 + 24 * cv tr t f NN + 32)) = r by omega] at hk
    omega

/-- A nonzero multiplicity of a `[c x]` interaction makes `x = 1`. -/
theorem one_of_mult {i : Interaction} {x w : Nat} (hm : i.mult = [c x])
    (h : i.multNat tr t w pub ≠ 0) : cv tr t w x = 1 := by
  rw [Mem.multNat_c hm] at h
  by_cases e : cv tr t w x = 1
  · exact e
  · simp [e] at h

/-- The `SA0` send gate `u0g = rend·useC` is set only on record ends. -/
theorem rend_of_u0g (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hu : cv tr t r u0g = 1) :
    cv tr t r rend = 1 := by
  have hb := bool_of hL hr (x := rend) (by simp [boolCols])
  obtain ⟨q, c1⟩ := zd hL hr (e := sub (c u0g) (.mul (c rend) (c useC))) (by simp [constraints, cRec])
  zs c1 [hu]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h | h
  · rw [h] at c1; simp at c1; omega
  · exact h

theorem sop_filter :
    interactions.filter (fun i => decide (i.bus = B_SOP ∧ i.send = true)) = [interactions[10]!] := by
  decide

end Codec

theorem ScanDist.sop_filter :
    ScanDist.interactions.filter (fun i => decide (i.bus = B_SOP ∧ i.send = true)) =
      [ScanDist.interactions[4]!] := by
  decide

end ZkFormal.NearV3.Sched
