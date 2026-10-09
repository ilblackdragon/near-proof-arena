import ZkFormal.NearV3.Sched.Spec.Steps
import ZkFormal.NearV3.Sched.Spec.Draws
import ZkFormal.NearV3.Sched.Link.ScanPush
import ZkFormal.NearV3.Sched.Pub.Prep
import ZkFormal.NearV3.Sched.Link.SoundPrep
import ZkFormal.NearV3.Sched.Complete.Height

/-!
# ZkFormal.NearV3.Sched.Complete.Steps — the heights with A8 and the step budget discharged (M4)

An instance of the claim (`HInst`): public data `sp`, whether the previous `0x0f` value is
present, previous allowances `a0`, the rounds `rs` the process table records, the RNG words
`K`. Its counts (`HInst.stat`): `n = |ids|`, `C = |reqsOf (instOf sp)|`, `S = |entriesOf rs|`,
`Rd = |rs|`.

* `stat_ok`: if `sp` satisfies the `prepD0` facts (`SchedPubOk`) and `rs` is a replay of the
  instance (`Replay`: `simR` from `lpState`, `SPUSH` balance, nonempty rounds — the hypotheses
  of `process_rounds`, which the honest rounds satisfy), then A8 (`C ≤ N`, `n ≤ 64`) and the
  step budget (`Rd ≤ S ≤ C + 43·n`) hold.
* `heights_inst` (parametric in `B0`, `T`, `maxLog`), **`heights_prep`** (`prepD0` succeeded,
  `B0 = 2,000,000`, `maxLog = 22`): the five scheduler tables fit `2^22` given **only A7** and
  the replays.
* `replay_draws`: the replay's RNG ends at stream position `K` with `K + 64·Rd ≤ 64·S` (the
  fuel bound, all the spec gives); `lane_prep`: `shufV3 ≤ 2^22`, and **given** the RelD0a
  word bound `Σ K ≤ W0 = 770,000` (A9 `e.chacha_words`, not a consequence of the rest of the
  spec: `worstK_exceeds`), `genV3 < 2^20`, `chachaV3 < 2^22`.
-/

namespace ZkFormal.NearV3.Sched.Complete

open ZkFormal.NearV3.Sched NearSpecV3 NearSpecV3.Scheduler NearSpec

/-- The process replay of instance `sp` from the link-pass state with previous allowances `a0`
(the hypotheses of `process_rounds` that the counts depend on): `simR` replays the rounds, the
bucket entries are the initial pushes and the re-pushes (`SPUSH` balance), rounds are nonempty. -/
def Replay (sp : SchedPub) (a0 : Nat → Nat) (rs : List RoundD) : Prop :=
  ∃ t0 stF ps,
    simR sp.ids.length sp.allowed (reqsOf (instOf sp)) rs t0
        (lpState sp.ids sp.params sp.allowed a0 sp.seed) = some (stF, ps) ∧
      (entriesOf rs).Perm
        (initPushes (reqsOf (instOf sp)) (lpState sp.ids sp.params sp.allowed a0 sp.seed) ++ ps) ∧
      ∀ R ∈ rs, R.ents ≠ []

/-- One instance of the claim. -/
structure HInst where
  sp : SchedPub
  pre : Bool
  a0 : Nat → Nat
  rs : List RoundD
  K : Nat

/-- Its counts. -/
def HInst.stat (x : HInst) : IStat :=
  ⟨x.sp.ids.length, x.pre, (reqsOf (instOf x.sp)).length, (entriesOf x.rs).length, x.rs.length, x.K⟩

/-- At most `n²` resolved requests (A8: distinct senders, distinct `to_shard`s per sender). -/
theorem instOf_raw_le (sp : SchedPub) (H : SchedPubOk sp) :
    (instOf sp).raw.length ≤ sp.ids.length * sp.ids.length := by
  have h1 : (instOf sp).raw.length ≤ (rawOf sp.ids sp.raw).length := List.length_filter_le _ _
  have h2 : (rawKeys sp.ids sp.raw).length ≤ (List.range (sp.ids.length * sp.ids.length)).length :=
    length_le_of_nodup_subset _ _ (keysOf_nodup _ _ H.keys H.a8)
      (fun x hx => List.mem_range.2 (keysOf_lt _ _ x hx))
  rw [← rawOf_rawKeys, List.length_map, List.length_range] at h2
  omega

/-- **A8 and the step budget of one instance.** -/
theorem stat_ok (x : HInst) (H : SchedPubOk x.sp)
    (hA : x.sp.allowed.size = x.sp.ids.length * x.sp.ids.length) (hR : Replay x.sp x.a0 x.rs) :
    (x.stat.C ≤ x.stat.N ∧ x.stat.n ≤ 64) ∧
      (x.stat.Rd ≤ x.stat.S ∧ x.stat.S ≤ x.stat.C + 43 * x.stat.n) := by
  obtain ⟨t0, stF, ps, hsim, hperm, hne⟩ := hR
  have hC : (reqsOf (instOf x.sp)).length ≤ x.sp.ids.length * x.sp.ids.length :=
    Nat.le_trans (List.length_filterMap_le _ _) (instOf_raw_le x.sp H)
  obtain ⟨h1, h2⟩ := steps_pv86 x.sp.ids x.sp.params H.params x.sp.allowed hA (instOf x.sp).raw
    x.a0 x.sp.seed hsim hperm hne
  exact ⟨⟨hC, H.n64⟩, h1, h2⟩

theorem stats_ok (xs : List HInst) (hok : ∀ x ∈ xs, SchedPubOk x.sp ∧ x.sp.allowed.size = x.sp.ids.length * x.sp.ids.length)
    (hrep : ∀ x ∈ xs, Replay x.sp x.a0 x.rs) : A8 (xs.map HInst.stat) ∧ Steps 43 (xs.map HInst.stat) := by
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩ <;>
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    have := stat_ok x (hok x hx).1 (hok x hx).2 (hrep x hx)
    first | exact this.1 | exact this.2

/-- **Heights, parametric**: A7 and the replays; `κ = 43` is proved. -/
theorem heights_inst (B0 T maxLog : Nat) (xs : List HInst) (hok : ∀ x ∈ xs, SchedPubOk x.sp ∧ x.sp.allowed.size = x.sp.ids.length * x.sp.ids.length)
    (hrep : ∀ x ∈ xs, Replay x.sp x.a0 x.rs) (hT : xs.length ≤ T) (h7 : A7 B0 (xs.map HInst.stat))
    (hc : codecMax B0 + 1 ≤ 2 ^ maxLog) (hs : sdMax B0 + 1 ≤ 2 ^ maxLog)
    (hp : procMax B0 T 43 + 1 ≤ 2 ^ maxLog) (hm : memMax B0 T 43 + 1 ≤ 2 ^ maxLog)
    (hq : cmpMax B0 T 43 + 1 ≤ 2 ^ maxLog) :
    let Ps := xs.map HInst.stat
    total IStat.codecRows Ps + 1 ≤ 2 ^ maxLog ∧ total IStat.sdRows Ps + 1 ≤ 2 ^ maxLog ∧
    total IStat.procRows Ps + 1 ≤ 2 ^ maxLog ∧ total IStat.memRows Ps + 1 ≤ 2 ^ maxLog ∧
    total IStat.cmpRows Ps + 1 ≤ 2 ^ maxLog := by
  obtain ⟨h8, hb⟩ := stats_ok xs hok hrep
  exact heights B0 T 43 maxLog _ h7 h8 hb (by simpa using hT) hc hs hp hm hq

/-- **Heights from `prepD0`** (`B0 = 2,000,000`, `maxLog = 22`): for the instances of a
successful `prepD0`, with each instance's rounds a replay, **A7 alone** bounds all five
scheduler tables by `2^22`. -/
theorem heights_prep {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint = .ok p)
    (xs : List HInst) (hx : xs.map HInst.sp = p.sched) (hrep : ∀ x ∈ xs, Replay x.sp x.a0 x.rs)
    (h7 : A7 2000000 (xs.map HInst.stat)) :
    let Ps := xs.map HInst.stat
    total IStat.codecRows Ps + 1 ≤ 2 ^ 22 ∧ total IStat.sdRows Ps + 1 ≤ 2 ^ 22 ∧
    total IStat.procRows Ps + 1 ≤ 2 ^ 22 ∧ total IStat.memRows Ps + 1 ≤ 2 ^ 22 ∧
    total IStat.cmpRows Ps + 1 ≤ 2 ^ 22 := by
  have hok : ∀ x ∈ xs, SchedPubOk x.sp ∧ x.sp.allowed.size = x.sp.ids.length * x.sp.ids.length :=
    fun x hxm => have hm : x.sp ∈ p.sched := hx ▸ List.mem_map_of_mem hxm
      ⟨prepD0_sched h x.sp hm, prepD0_asz h x.sp hm⟩
  have hT : xs.length ≤ 33 := by
    have := prepD0_len h
    rw [← hx, List.length_map] at this
    exact this
  exact heights_inst 2000000 33 22 xs hok hrep hT h7 (by decide) (by decide) (by decide) (by decide)
    (by decide)

/-- **Words drawn by an instance's replay**: the final RNG is `rngAt (leWords seed) K` with
`K + 64·Rd ≤ 64·S`. -/
theorem replay_draws (sp : SchedPub) (a0 : Nat → Nat) (rs : List RoundD) (hR : Replay sp a0 rs) :
    ∃ t0 stF ps, simR sp.ids.length sp.allowed (reqsOf (instOf sp)) rs t0
        (lpState sp.ids sp.params sp.allowed a0 sp.seed) = some (stF, ps) ∧
      ∃ K, stF.rng = ZkFormal.Chacha.rngAt (NearSpecV3.leWords sp.seed) K ∧
        K + 64 * rs.length ≤ 64 * (entriesOf rs).length := by
  obtain ⟨t0, stF, ps, hsim, -, hne⟩ := hR
  exact ⟨t0, stF, ps, hsim, lp_draws sp.ids sp.params sp.allowed a0 sp.seed _ hsim hne⟩

/-- **Lane tables from `prepD0`**: `shufV3` fits `2^22` from A7 and the replays; `genV3` and
`chachaV3` fit `2^20` and `2^22` given the RelD0a word bound `Σ K ≤ W0` (A9). The replay's
`K` is the instance's RNG stream position (`replay_draws`); identifying it with the spec's
`Scheduler.wordsDrawn` (the A9 count) is part of the open `Gen.run → Replay` link. -/
theorem lane_prep {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint = .ok p)
    (xs : List HInst) (hx : xs.map HInst.sp = p.sched) (hrep : ∀ x ∈ xs, Replay x.sp x.a0 x.rs)
    (h7 : A7 2000000 (xs.map HInst.stat))
    (hW : total IStat.genRows (xs.map HInst.stat) ≤ NearSpecV3.W0) :
    let Ps := xs.map HInst.stat
    total IStat.shufRows Ps + 1 ≤ 2 ^ 22 ∧ total IStat.genRows Ps + 1 ≤ 2 ^ 20 ∧
    total IStat.chachaRows Ps + 1 ≤ 2 ^ 22 := by
  have hok : ∀ x ∈ xs, SchedPubOk x.sp ∧ x.sp.allowed.size = x.sp.ids.length * x.sp.ids.length :=
    fun x hxm => have hm : x.sp ∈ p.sched := hx ▸ List.mem_map_of_mem hxm
      ⟨prepD0_sched h x.sp hm, prepD0_asz h x.sp hm⟩
  have hT : xs.length ≤ 33 := by
    have := prepD0_len h
    rw [← hx, List.length_map] at this
    exact this
  obtain ⟨h8, hb⟩ := stats_ok xs hok hrep
  exact lane_770k_22 _ h7 h8 hb (by simpa using hT) hW

end ZkFormal.NearV3.Sched.Complete
