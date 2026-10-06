import ZkFormal.NearV3.Sched.Link.GridBlock
import ZkFormal.NearV3.Sched.Link.SoundFin
import ZkFormal.NearV3.Sched.Spec.Dist

/-!
# ZkFormal.NearV3.Sched.Link.GridShard — the shard rows of a distribute section (stage F, b2–b3)

**b2 — shard rows.** A shard row `w` (`kSh = 1`) of instance `τ = tau(w)`, `P = Ps[τ]`:

* `shard_vals` (public shard record `shardRec τ P side x`, `shard_rec`): `side < 2`, the shard
  `r = x < n`, `nn = n`, the links count `N2 = cntS/cntR`;
* `shard_L2` (memory `SFIN`, `fin_snd`/`fin_rcv`): the final budget `L2 = stF.senderBudget[r]` /
  `stF.receiverBudget[r]`;
* `side_nodup`: the shards of one side of a section are pairwise distinct (`shard_unique`), so
  they are a permutation of `[0, n)`; **`start_unique`**: one section per instance.

**b3 — sorted order.** Along a side the comparator (`cb = 1`, `SCMP (key, kp, 1)`) and the `kp`
chain (`kp' = key + 1`) make the key `q2·64 + r` strictly increase, and `q2 = avgLink (N2, L2)`
(`shard_div`), so the side's shard sequence is `sordOf` / `rordOf` (**`side_sorted`**, via
`sortByKey_eq_of_sorted`).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-- Links count of shard `x` on side `sd`. -/
def cntSd (n : Nat) (allowed : Array Bool) (sd x : Nat) : Nat :=
  if sd = 0 then cntS n allowed x else cntR n allowed x

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tsd : Nat}

set_option maxRecDepth 8000 in
/-- **b2: the public part of a shard row.** -/
theorem shard_vals (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (I : PubIdx AP pub Fp.ofNat)
    (Ps : List InstPub) (fwd : List (Nat × Nat)) (hrec : I.recs B_SPAR true = (render Ps fwd).par)
    (h256 : Ps.length ≤ 256) (hn : ∀ τ, τ < Ps.length → (Ps.getD τ instD).n ≤ 64)
    {w : Nat} (hw : w < tr.height tsd) (hs : cv tr tsd w Dist.kSh = 1) :
    cv tr tsd w Dist.tau < Ps.length ∧ cv tr tsd w Dist.side < 2 ∧
      cv tr tsd w Dist.r < (Ps.getD (cv tr tsd w Dist.tau) instD).n ∧
      cv tr tsd w Dist.nn = (Ps.getD (cv tr tsd w Dist.tau) instD).n ∧
      cv tr tsd w Dist.N2 = cntSd (Ps.getD (cv tr tsd w Dist.tau) instD).n
        (Ps.getD (cv tr tsd w Dist.tau) instD).allowed (cv tr tsd w Dist.side) (cv tr tsd w Dist.r) ∧
      Scan.parV tr tsd w = shardRec (cv tr tsd w Dist.tau) (Ps.getD (cv tr tsd w Dist.tau) instD)
        (cv tr tsd w Dist.side) (cv tr tsd w Dist.r) := by
  have hD := Dist.DLocal.of_sd (sd_local hH OS)
  obtain ⟨hτ, sd, x, hsd, hx, hpv⟩ := shard_rec hH OS I Ps fwd hrec h256 hn hw hs
  have hpv' := hpv
  generalize hP : Ps.getD (cv tr tsd w Dist.tau) instD = P at hpv' hx hpv ⊢
  simp only [Scan.parV, shardRec, b3, List.cons_append, List.nil_append, List.cons.injEq] at hpv'
  obtain ⟨-, -, p0, p1, p2, -, -, -, p6, -, -⟩ := hpv'
  have es : cv tr tsd w Dist.side = sd := p0
  have ex : cv tr tsd w Dist.shd = x := p1
  have ec : cv tr tsd w Dist.lnk = cntSd P.n P.allowed sd x := p2
  have en : cv tr tsd w Dist.llo = P.n := p6
  have er : cv tr tsd w Dist.shd = cv tr tsd w Dist.r :=
    Dist.kSh_eq hD hw hs (x := Dist.shd) (e := c Dist.r) (by simp [Dist.constraints, Dist.cShard])
      (by simp only [zev_c, cur_cv]) (cv_lt _ _)
  have eN : cv tr tsd w Dist.lnk = cv tr tsd w Dist.N2 :=
    Dist.kSh_eq hD hw hs (x := Dist.lnk) (e := c Dist.N2) (by simp [Dist.constraints, Dist.cShard])
      (by simp only [zev_c, cur_cv]) (cv_lt _ _)
  have enn : cv tr tsd w Dist.llo = cv tr tsd w Dist.nn :=
    Dist.kSh_eq hD hw hs (x := Dist.llo) (e := c Dist.nn) (by simp [Dist.constraints, Dist.cShard])
      (by simp only [zev_c, cur_cv]) (cv_lt _ _)
  have hrx : cv tr tsd w Dist.r = x := by omega
  refine ⟨hτ, by omega, by omega, by omega, by rw [← eN, ec, es, hrx], by rw [es, hrx]; exact hpv⟩

/-- The `SFIN` receive of `ssdV3`. -/
theorem ScanDist.fin_def : ScanDist.interactions[5]! =
    { bus := B_SFIN, mult := [c Dist.kSh], send := false, msg := [Dist.addrE, c Dist.L2, k 0] } := rfl

set_option maxRecDepth 8000 in
/-- **b2: the final budget of a shard row** (memory `SFIN`). -/
theorem shard_L2 {tm tcmp ts tch tg tcd f m : Nat} {P : InstPub} {allowed : Array Bool} {st : St}
    (C : MemCtx AP pub tr tp tm tcmp ts tch tg tsd tcd f m P allowed st)
    {w : Nat} (hw : w < tr.height tsd) (hs : cv tr tsd w Dist.kSh = 1)
    (hτ : cv tr tsd w Dist.tau = cv tr tp f Proc.tau) (hsd : cv tr tsd w Dist.side < 2)
    (hr : cv tr tsd w Dist.r < P.n) :
    cv tr tsd w Dist.L2 = if cv tr tsd w Dist.side = 0 then
      (specSt P.n allowed (reqsOf P) tr tp f st m).senderBudget[cv tr tsd w Dist.r]! else
      (specSt P.n allowed (reqsOf P) tr tp f st m).receiverBudget[cv tr tsd w Dist.r]! := by
  have OS := C.OS
  have hn := C.PO.n64
  have hτ256 := C.hτ
  obtain ⟨r', hr', hl, hmsg⟩ := fin_src C.hH C.O.mem OS.lt hw (by rw [OS.tab]; exact Scan.sd_mem 5 (by decide))
    (by rw [ScanDist.fin_def]) (by rw [ScanDist.fin_def])
    (by rw [Mem.multNat_c (by rw [ScanDist.fin_def]), hs]; simp)
  have hrn : cv tr tsd w Dist.r < 64 := by unfold InstPub.n at hr hn; omega
  have ea : Dist.addrE.eval tr tsd w pub = Fp.ofNat (cv tr tsd w Dist.tau * 16384 +
      (cv tr tsd w Dist.side + 1) * 4096 + cv tr tsd w Dist.r) :=
    Scan.eval_ofNat (by simp only [Dist.addrE, zev_add, zev_smul, zev_c, zev_k, cur_cv]; omega)
  rw [ScanDist.fin_def] at hmsg
  simp only [Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at hmsg
  obtain ⟨e1, e2, -⟩ := hmsg
  rw [ea] at e1
  have haddr : cv tr tm r' Mem.addr = cv tr tsd w Dist.tau * 16384 + (cv tr tsd w Dist.side + 1) * 4096 +
      cv tr tsd w Dist.r := by
    show (tr.cell _ r' Mem.addr).toNat = _
    rw [← e1, toNat_ofNat_lt' (by omega)]
  have hv : cv tr tm r' Mem.v = cv tr tsd w Dist.L2 := by
    show (tr.cell _ r' Mem.v).toNat = _
    rw [← e2]; rfl
  rw [← hv]
  by_cases h0 : cv tr tsd w Dist.side = 0
  · rw [if_pos h0]
    exact C.fin_snd hr' hl hr (by rw [haddr, h0, hτ]; unfold addrOf; omega)
  · rw [if_neg h0]
    exact C.fin_rcv hr' hl hr (by rw [haddr, show cv tr tsd w Dist.side = 1 by omega, hτ]; unfold addrOf; omega)

/-! ## The comparator on shard rows -/

theorem ScanDist.cmp_def : ScanDist.interactions[6]! =
    { bus := B_SCMP, mult := [c Dist.cg], send := true, msg := [c Dist.cx, c Dist.cy, c Dist.cb] } := rfl

/-- Shard rows: `cx = key`, `cy = kp`, `cb = 1`, `cg = 1`. -/
theorem Dist.shard_cmp_cells (hD : Dist.DLocal tr tsd pub) {w : Nat} (hw : w < tr.height tsd)
    (hs : cv tr tsd w Dist.kSh = 1) :
    cv tr tsd w Dist.cx = (64 * cv tr tsd w Dist.q2 + cv tr tsd w Dist.r) % 2013265921 ∧
      cv tr tsd w Dist.cy = cv tr tsd w Dist.kp ∧ cv tr tsd w Dist.cb = 1 ∧ cv tr tsd w Dist.cg = 1 := by
  have K := Dist.kinds hD hw
  have hC : cv tr tsd w Dist.kC = 0 := by omega
  have lt := fun x => cv_lt (tr := tr) (t := tsd) w x
  obtain ⟨q1, c1⟩ := Mem.zdvd hD hw (e := .mul (c Dist.kSh) (sub (c Dist.cx) (.add (smul 64 (c Dist.q2)) (c Dist.r))))
    (by simp [Dist.constraints, Dist.cShard])
  obtain ⟨q2, c2⟩ := Mem.zdvd hD hw (e := .mul (c Dist.kSh) (sub (c Dist.cy) (c Dist.kp)))
    (by simp [Dist.constraints, Dist.cShard])
  obtain ⟨q3, c3⟩ := Mem.zdvd hD hw (e := .mul (c Dist.kSh) (sub (c Dist.cb) (k 1)))
    (by simp [Dist.constraints, Dist.cShard])
  obtain ⟨q4, c4⟩ := Mem.zdvd hD hw (e := sub (c Dist.cg) (.add (c Dist.kSh) (.mul (c Dist.kC) (c Dist.al))))
    (by simp [Dist.constraints, Dist.cGrid])
  simp only [zev_mul, zev_sub, zev_add, zev_smul, zev_c, zev_k, cur_cv, hs, hC] at c1 c2 c3 c4
  push_cast at c1 c2 c3 c4
  have := lt Dist.cx; have := lt Dist.q2; have := lt Dist.r; have := lt Dist.cy; have := lt Dist.kp
  have := lt Dist.cb; have := lt Dist.cg
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- **b3: the comparator on a shard row**: `kp ≤ key`. -/
theorem shard_cmp {tcmp : Nat} (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (CO : CmpOwn AP tcmp)
    {w : Nat} (hw : w < tr.height tsd) (hs : cv tr tsd w Dist.kSh = 1)
    (hx : cv tr tsd w Dist.cx < 2 ^ 29) (hy : cv tr tsd w Dist.kp ≤ 2 ^ 29) :
    cv tr tsd w Dist.kp ≤ cv tr tsd w Dist.cx := by
  have hD := Dist.DLocal.of_sd (sd_local hH OS)
  obtain ⟨-, ey, eb, eg⟩ := Dist.shard_cmp_cells hD hw hs
  have hc := cmp_sound_le hH CO OS.lt hw (by rw [OS.tab]; exact Scan.sd_mem 6 (by decide))
    (by rw [ScanDist.cmp_def]) (by rw [ScanDist.cmp_def])
    (by rw [Mem.multNat_c (by rw [ScanDist.cmp_def]), eg]; simp)
    (x := tr.cell tsd w Dist.cx) (y := tr.cell tsd w Dist.cy) (b := tr.cell tsd w Dist.cb)
    (by rw [ScanDist.cmp_def]; rfl) hx (by show cv tr tsd w Dist.cy ≤ _; omega)
  rcases hc with ⟨-, h⟩ | ⟨h, -⟩
  · show cv tr tsd w Dist.kp ≤ _; rw [← ey]; exact h
  · exfalso
    have : cv tr tsd w Dist.cb = 0 := by unfold cv; rw [h]; rfl
    omega

/-- The key of a shard row: `cx = avgLink (N2, L2)·64 + r`. -/
theorem Dist.shard_key (hD : Dist.DLocal tr tsd pub) {w : Nat} (hw : w < tr.height tsd)
    (hs : cv tr tsd w Dist.kSh = 1) (hr : cv tr tsd w Dist.r < 64) :
    cv tr tsd w Dist.cx = sortKey (avgLink (cv tr tsd w Dist.N2, cv tr tsd w Dist.L2)) (cv tr tsd w Dist.r) ∧
      cv tr tsd w Dist.cx < 2 ^ 29 := by
  obtain ⟨ex, -⟩ := Dist.shard_cmp_cells hD hw hs
  obtain ⟨-, hq2, -, -⟩ := Dist.ranges hD hw
  obtain ⟨D1, D2⟩ := Dist.shard_div hD hw hs
  have hq : cv tr tsd w Dist.q2 = avgLink (cv tr tsd w Dist.N2, cv tr tsd w Dist.L2) := by
    unfold avgLink
    by_cases h : cv tr tsd w Dist.N2 = 0
    · rw [if_pos h]; exact D2 h
    · rw [if_neg h]; exact (D1 h).2.2
  have hr' := hr
  have e : cv tr tsd w Dist.cx = 64 * cv tr tsd w Dist.q2 + cv tr tsd w Dist.r := by
    rw [ex]; exact Nat.mod_eq_of_lt (by omega)
  rw [← hq, e]
  unfold sortKey
  refine ⟨by omega, by omega⟩

end

/-! ## A side of a section -/

namespace Dist

/-- Shard `x` of side `sd` of the section at `w₀`. -/
def shardAt (tr : Trace Fp) (t w0 nv sd x : Nat) : Nat := cv tr t (w0 + sd * nv + x) r

/-- The shards of side `sd`, in row order. -/
def sideList (tr : Trace Fp) (t w0 nv sd : Nat) : List Nat :=
  (List.range nv).map (shardAt tr t w0 nv sd)

theorem sideList_get {tr : Trace Fp} {t w0 nv sd x : Nat} (hx : x < nv) :
    (sideList tr t w0 nv sd)[x]! = shardAt tr t w0 nv sd x := by
  simp [sideList, getElem!_def, hx]

end Dist

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp} {tp tsd : Nat}

/-- Facts of a section of instance `τ` (with `P = Ps[τ]`): its start, `nn = n`. -/
structure SecOk (tr : Trace Fp) (tsd w0 τ : Nat) (P : InstPub) : Prop where
  st : Dist.Start tr tsd w0
  tau : cv tr tsd w0 Dist.tau = τ
  nn : cv tr tsd w0 Dist.nn = P.n
  n1 : 1 ≤ P.n
  n64 : P.n ≤ 64

/-- The shard rows of a section: values from the public record. -/
theorem sec_shard (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (I : PubIdx AP pub Fp.ofNat)
    (Ps : List InstPub) (fwd : List (Nat × Nat)) (hrec : I.recs B_SPAR true = (render Ps fwd).par)
    (h256 : Ps.length ≤ 256) (hn : ∀ τ, τ < Ps.length → (Ps.getD τ instD).n ≤ 64)
    {w0 τ : Nat} {P : InstPub} (hP : Ps.getD τ instD = P) (S : SecOk tr tsd w0 τ P)
    {sd x : Nat} (hsd : sd < 2) (hx : x < P.n) :
    w0 + sd * P.n + x < tr.height tsd ∧ cv tr tsd (w0 + sd * P.n + x) Dist.kSh = 1 ∧
      cv tr tsd (w0 + sd * P.n + x) Dist.side = sd ∧ cv tr tsd (w0 + sd * P.n + x) Dist.a = x ∧
      cv tr tsd (w0 + sd * P.n + x) Dist.tau = τ ∧ τ < Ps.length ∧
      cv tr tsd (w0 + sd * P.n + x) Dist.r < P.n ∧
      cv tr tsd (w0 + sd * P.n + x) Dist.N2 =
        cntSd P.n P.allowed sd (cv tr tsd (w0 + sd * P.n + x) Dist.r) ∧
      Scan.parV tr tsd (w0 + sd * P.n + x) = shardRec τ P sd (cv tr tsd (w0 + sd * P.n + x) Dist.r) := by
  have hD := Dist.DLocal.of_sd (sd_local hH OS)
  obtain ⟨SR, -⟩ := Dist.block hD S.st S.nn S.n1 S.n64
  obtain ⟨hw, hs, hside, ha, hic, -⟩ := SR sd x hsd hx
  have hτ : cv tr tsd (w0 + sd * P.n + x) Dist.tau = τ := hic.1.trans S.tau
  obtain ⟨hτl, -, hr, -, hN, hpv⟩ := shard_vals hH OS I Ps fwd hrec h256 hn hw hs
  rw [hτ, hP] at hr
  rw [hτ, hP, hside] at hN
  rw [hτ, hP, hside] at hpv
  rw [hτ] at hτl
  exact ⟨hw, hs, hside, ha, hτ, hτl, hr, hN, hpv⟩

/-- **The shards of a side are pairwise distinct** (one row per shard record). -/
theorem side_nodup (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (I : PubIdx AP pub Fp.ofNat)
    (Ps : List InstPub) (fwd : List (Nat × Nat)) (hrec : I.recs B_SPAR true = (render Ps fwd).par)
    (h256 : Ps.length ≤ 256) (hn : ∀ τ, τ < Ps.length → (Ps.getD τ instD).n ≤ 64)
    {w0 τ : Nat} {P : InstPub} (hP : Ps.getD τ instD = P) (S : SecOk tr tsd w0 τ P)
    {sd : Nat} (hsd : sd < 2) :
    (Dist.sideList tr tsd w0 P.n sd).Nodup ∧ (∀ y ∈ Dist.sideList tr tsd w0 P.n sd, y < P.n) ∧
      (Dist.sideList tr tsd w0 P.n sd).length = P.n := by
  refine ⟨?_, ?_, by simp [Dist.sideList]⟩
  · unfold Dist.sideList
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {x y} hx hy hxy he => hxy ?_) List.nodup_range
    have hx' := List.mem_range.1 hx
    have hy' := List.mem_range.1 hy
    have Sx := sec_shard hH OS I Ps fwd hrec h256 hn hP S hsd hx'
    have Sy := sec_shard hH OS I Ps fwd hrec h256 hn hP S hsd hy'
    have he' : cv tr tsd (w0 + sd * P.n + x) Dist.r = cv tr tsd (w0 + sd * P.n + y) Dist.r := he
    have hw := shard_unique hH OS I Ps fwd hrec h256 hn Sx.1 Sx.2.1 Sy.1 Sy.2.1
      (by rw [Sx.2.2.2.2.2.2.2.2, Sy.2.2.2.2.2.2.2.2, he'])
    omega
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact (sec_shard hH OS I Ps fwd hrec h256 hn hP S hsd (List.mem_range.1 hx)).2.2.2.2.2.2.1

/-- **One section per instance.** -/
theorem start_unique (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (I : PubIdx AP pub Fp.ofNat)
    (Ps : List InstPub) (fwd : List (Nat × Nat)) (hrec : I.recs B_SPAR true = (render Ps fwd).par)
    (h256 : Ps.length ≤ 256) (hn : ∀ τ, τ < Ps.length → (Ps.getD τ instD).n ≤ 64)
    {w0 τ : Nat} {P : InstPub} (hP : Ps.getD τ instD = P) (S : SecOk tr tsd w0 τ P)
    {w1 : Nat} (st1 : Dist.Start tr tsd w1) (hτ1 : cv tr tsd w1 Dist.tau = τ) : w1 = w0 := by
  obtain ⟨hw1, hs1, hsd1, ha1, -⟩ := st1
  obtain ⟨-, -, hr1, -, -, hpv1⟩ := shard_vals hH OS I Ps fwd hrec h256 hn hw1 hs1
  rw [hτ1, hP] at hr1 hpv1
  rw [hsd1] at hpv1
  obtain ⟨hnd, hlt, hlen⟩ := side_nodup hH OS I Ps fwd hrec h256 hn hP S (sd := 0) (by decide)
  have hm := (mem_of_nodup_of_length P.n _ hnd hlt hlen (cv tr tsd w1 Dist.r)).2 hr1
  obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hm
  have hx' := List.mem_range.1 hx
  have Sx := sec_shard hH OS I Ps fwd hrec h256 hn hP S (sd := 0) (by decide) hx'
  have he : w0 + 0 * P.n + x = w1 := shard_unique hH OS I Ps fwd hrec h256 hn Sx.1 Sx.2.1 hw1 hs1
    (by rw [Sx.2.2.2.2.2.2.2.2, hpv1]; unfold Dist.shardAt at hxe; rw [hxe])
  have : x = 0 := by have := Sx.2.2.2.1; rw [he, ha1] at this; omega
  omega

/-- **b3: a side of a section is in sorted order.** With the final budgets `B` of the side
(`L2 = B[r]`), the side's shards are `sortByKey (avgLink (cnt, B[·]))`, i.e. `sordOf` /
`rordOf`. -/
theorem side_sorted {tcmp : Nat} (hH : HoldsP AP pub tr) (OS : ScanOwn AP tsd tp) (CO : CmpOwn AP tcmp)
    (I : PubIdx AP pub Fp.ofNat)
    (Ps : List InstPub) (fwd : List (Nat × Nat)) (hrec : I.recs B_SPAR true = (render Ps fwd).par)
    (h256 : Ps.length ≤ 256) (hn : ∀ τ, τ < Ps.length → (Ps.getD τ instD).n ≤ 64)
    {w0 τ : Nat} {P : InstPub} (hP : Ps.getD τ instD = P) (S : SecOk tr tsd w0 τ P)
    {sd : Nat} (hsd : sd < 2) (B : Array Nat)
    (hL2 : ∀ x, x < P.n → cv tr tsd (w0 + sd * P.n + x) Dist.L2 = B[Dist.shardAt tr tsd w0 P.n sd x]!) :
    sortByKey (fun y => avgLink (cntSd P.n P.allowed sd y, B[y]!)) (List.range P.n) =
      Dist.sideList tr tsd w0 P.n sd := by
  have hD := Dist.DLocal.of_sd (sd_local hH OS)
  obtain ⟨hnd, hlt, hlen⟩ := side_nodup hH OS I Ps fwd hrec h256 hn hP S hsd
  -- the key of each row
  have key : ∀ x, x < P.n → cv tr tsd (w0 + sd * P.n + x) Dist.cx =
      sortKey (avgLink (cntSd P.n P.allowed sd (Dist.shardAt tr tsd w0 P.n sd x),
        B[Dist.shardAt tr tsd w0 P.n sd x]!)) (Dist.shardAt tr tsd w0 P.n sd x) ∧
      cv tr tsd (w0 + sd * P.n + x) Dist.cx < 2 ^ 29 := by
    intro x hx
    have Sx := sec_shard hH OS I Ps fwd hrec h256 hn hP S hsd hx
    have K := Dist.shard_key hD Sx.1 Sx.2.1 (by have := S.n64; have := Sx.2.2.2.2.2.2.1; omega)
    rw [Sx.2.2.2.2.2.2.2.1, hL2 x hx] at K
    exact K
  -- strictly increasing along the side
  have step : ∀ x, x + 1 < P.n → cv tr tsd (w0 + sd * P.n + x) Dist.cx <
      cv tr tsd (w0 + sd * P.n + (x + 1)) Dist.cx := by
    intro x hx
    have Sx := sec_shard hH OS I Ps fwd hrec h256 hn hP S hsd (show x < P.n by omega)
    have he := Dist.e1_sh hD Sx.1 Sx.2.1 (by have := S.n64; omega) (by
      obtain ⟨SR, -⟩ := Dist.block hD S.st S.nn S.n1 S.n64
      have := (SR sd x hsd (by omega)).2.2.2.2.1.2; rw [this, S.nn]; exact S.n1) (by
      obtain ⟨SR, -⟩ := Dist.block hD S.st S.nn S.n1 S.n64
      have := (SR sd x hsd (by omega)).2.2.2.2.1.2; rw [this, S.nn]; exact S.n64)
    obtain ⟨SR, -⟩ := Dist.block hD S.st S.nn S.n1 S.n64
    have hnn := (SR sd x hsd (by omega)).2.2.2.2.1.2
    rw [Sx.2.2.2.1, hnn, S.nn, if_neg (by omega)] at he
    obtain ⟨-, -, -, -, hkp, -, -⟩ := Dist.shard_mid hD Sx.1 Sx.2.1 he (by have := S.n64; omega)
    have K0 := (key x (by omega)).2
    have Sx1 := sec_shard hH OS I Ps fwd hrec h256 hn hP S hsd (show x + 1 < P.n from hx)
    have K1 := (key (x + 1) hx).2
    rw [show w0 + sd * P.n + (x + 1) = w0 + sd * P.n + x + 1 by omega] at Sx1 K1 ⊢
    have hc := shard_cmp hH OS CO Sx1.1 Sx1.2.1 K1 (by rw [hkp]; omega)
    rw [hkp, Nat.mod_eq_of_lt (by omega)] at hc
    omega
  have mono : ∀ x y, x < y → y < P.n → cv tr tsd (w0 + sd * P.n + x) Dist.cx <
      cv tr tsd (w0 + sd * P.n + y) Dist.cx := by
    intro x y hxy hy
    induction y with
    | zero => omega
    | succ y ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hxy with h | h
      · exact Nat.lt_trans (ih h (by omega)) (step y hy)
      · subst h; exact step x hy
  apply sortByKey_eq_of_sorted _ P.n S.n64 _ hnd hlt hlen
  unfold Dist.sideList
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem (fun {x y} hx hy hxy => ?_) List.pairwise_lt_range
  have hx' := List.mem_range.1 hx
  have hy' := List.mem_range.1 hy
  rw [← (key x hx').1, ← (key y hy').1]
  exact mono x y hxy hy'

end

end ZkFormal.NearV3.Sched
