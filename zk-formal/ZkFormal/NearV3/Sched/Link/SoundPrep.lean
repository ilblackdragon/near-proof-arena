import ZkFormal.NearV3.Sched.Pub.Prep

/-!
# ZkFormal.NearV3.Sched.Link.SoundPrep — one layout for every scheduler instance (`prepD0`)

`render` sends the `SDL` id records of instance 0's layout only (`dlRecs 0 (Ps[0]).ids`), and the
codec passes them from instance to instance. The instances agree on the layout because `prepClaim`
builds every apply context with the one layout `L` of the claim:

* **`prepD0_ids`**: `prepD0 cb h = .ok p → ∃ ids, ∀ sp ∈ p.sched, sp.ids = ids`;
* **`prepD0_ash`**: every `allShardsHash` is a `sha256` output, 32 bytes (`pubOf`);
* **`prepD0_values`**: every value table is `requestValues params` (`pubOf`);
* **`prepD0_asz`**: every `allowed` array has `n²` entries (`pubOf`);
* **`prepD0_ids64`**: every shard id is `< 2^64` (`decodeLayout` reads them with `pU64`).
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler NearSpec

theorem schedPub_ids {ctx : ApplyCtx} {sp : SchedPub} (h : schedPub ctx = some sp) :
    sp.ids = ctx.layout.shardIds := by
  unfold schedPub pubOf at h
  by_cases hn : ctx.layout.shardIds.length = 0
  · simp [hn] at h
  · cases hp : Params.calculate Config.pv86 ctx.layout.shardIds.length with
    | none => simp [hn, hp] at h
    | some p =>
      simp only [hn, hp, ↓reduceIte] at h
      simp only [Option.bind, bind, Option.some.injEq] at h
      subst h; rfl

/-- The closing step of `prepClaim` for the layout. -/
theorem ids_close {L : Layout} {own g gp : Nat} {B2 : Blk} {xs : List Blk} {sched : List SchedPub}
    {f : ApplyCtx → Except String SchedPub}
    (hm : List.mapM f (blockCtx L own g B2 gp ::
      List.map (fun M => blockCtx L own g M M.hdr.nextGasPrice) xs) = .ok sched)
    (hf : ∀ ctx sp, f ctx = .ok sp → schedPub ctx = some sp) :
    ∀ sp ∈ sched, sp.ids = L.shardIds := by
  intro sp hsp
  obtain ⟨ctx, hctx, hfc⟩ := mapM_ok f _ _ hm sp hsp
  rw [schedPub_ids (hf ctx sp hfc)]
  rcases List.mem_cons.1 hctx with e | e
  · subst e; rfl
  · obtain ⟨M, -, rfl⟩ := List.mem_map.1 e; rfl

set_option maxHeartbeats 4000000 in
theorem prepClaim_ids {cb : Bytes} {pc : PrepC} (h : prepClaim cb = .ok pc) :
    ∃ ids, ∀ sp ∈ pc.sched, sp.ids = ids := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨_, ids_close (by assumption) (fun ctx sp hc => by
        split at hc
        · simp only [pure, Except.pure, Except.ok.injEq] at hc; subst hc; assumption
        · cases hc)⟩

/-- **One layout for every scheduler instance of a successful `prepD0`.** -/
theorem prepD0_ids {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint = .ok p) :
    ∃ ids, ∀ sp ∈ p.sched, sp.ids = ids := by
  unfold prepD0 at h
  obtain ⟨pc, hpc, hb⟩ := bind_ok h
  rw [prepBody_sched hb]
  exact prepClaim_ids hpc

/-! ## `allShardsHash` is 32 bytes -/

theorem schedPub_ash {ctx : ApplyCtx} {sp : SchedPub} (h : schedPub ctx = some sp) :
    sp.allShardsHash.length = 32 := by
  unfold schedPub pubOf at h
  by_cases hn : ctx.layout.shardIds.length = 0
  · simp [hn] at h
  · cases hp : Params.calculate Config.pv86 ctx.layout.shardIds.length with
    | none => simp [hn, hp] at h
    | some p =>
      simp only [hn, hp, ↓reduceIte] at h
      simp only [Option.bind, bind, Option.some.injEq] at h
      subst h; exact ArenaCore.sha256_length _

theorem ash_close {ctxs : List ApplyCtx} {sched : List SchedPub}
    {f : ApplyCtx → Except String SchedPub} (hm : List.mapM f ctxs = .ok sched)
    (hf : ∀ ctx sp, f ctx = .ok sp → schedPub ctx = some sp) :
    ∀ sp ∈ sched, sp.allShardsHash.length = 32 := by
  intro sp hsp
  obtain ⟨ctx, -, hfc⟩ := mapM_ok f _ _ hm sp hsp
  exact schedPub_ash (hf ctx sp hfc)

set_option maxHeartbeats 4000000 in
theorem prepClaim_ash {cb : Bytes} {pc : PrepC} (h : prepClaim cb = .ok pc) :
    ∀ sp ∈ pc.sched, sp.allShardsHash.length = 32 := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ash_close (by assumption) (fun ctx sp hc => by
        split at hc
        · simp only [pure, Except.pure, Except.ok.injEq] at hc; subst hc; assumption
        · cases hc)

/-- **Every `allShardsHash` of a successful `prepD0` is 32 bytes.** -/
theorem prepD0_ash {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint = .ok p) :
    ∀ sp ∈ p.sched, sp.allShardsHash.length = 32 := by
  unfold prepD0 at h
  obtain ⟨pc, hpc, hb⟩ := bind_ok h
  rw [prepBody_sched hb]
  exact prepClaim_ash hpc

/-! ## Any property of `schedPub` outputs -/

theorem prop_close {Q : SchedPub → Prop} (hQ : ∀ ctx sp, schedPub ctx = some sp → Q sp)
    {ctxs : List ApplyCtx} {sched : List SchedPub}
    {f : ApplyCtx → Except String SchedPub} (hm : List.mapM f ctxs = .ok sched)
    (hf : ∀ ctx sp, f ctx = .ok sp → schedPub ctx = some sp) : ∀ sp ∈ sched, Q sp := by
  intro sp hsp
  obtain ⟨ctx, -, hfc⟩ := mapM_ok f _ _ hm sp hsp
  exact hQ ctx sp (hf ctx sp hfc)

set_option maxHeartbeats 4000000 in
theorem prepClaim_prop {Q : SchedPub → Prop} (hQ : ∀ ctx sp, schedPub ctx = some sp → Q sp)
    {cb : Bytes} {pc : PrepC} (h : prepClaim cb = .ok pc) : ∀ sp ∈ pc.sched, Q sp := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact prop_close hQ (by assumption) (fun ctx sp hc => by
        split at hc
        · simp only [pure, Except.pure, Except.ok.injEq] at hc; subst hc; assumption
        · cases hc)

theorem prepD0_prop {Q : SchedPub → Prop} (hQ : ∀ ctx sp, schedPub ctx = some sp → Q sp)
    {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint = .ok p) : ∀ sp ∈ p.sched, Q sp := by
  unfold prepD0 at h
  obtain ⟨pc, hpc, hb⟩ := bind_ok h
  rw [prepBody_sched hb]
  exact prepClaim_prop hQ hpc

/-- **Every value table of a successful `prepD0` is `requestValues params`.** -/
theorem prepD0_values {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint = .ok p) :
    ∀ sp ∈ p.sched, sp.values = requestValues sp.params :=
  prepD0_prop (fun ctx sp h => by
    unfold schedPub pubOf at h
    by_cases hn : ctx.layout.shardIds.length = 0
    · simp [hn] at h
    · cases hp : Params.calculate Config.pv86 ctx.layout.shardIds.length with
      | none => simp [hn, hp] at h
      | some p =>
        simp only [hn, hp, ↓reduceIte] at h
        simp only [Option.bind, bind, Option.some.injEq] at h
        subst h; rfl) h

/-- **Every `allowed` array of a successful `prepD0` has `n²` entries.** -/
theorem prepD0_asz {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint = .ok p) :
    ∀ sp ∈ p.sched, sp.allowed.size = sp.ids.length * sp.ids.length :=
  prepD0_prop (fun ctx sp h => by
    unfold schedPub pubOf at h
    by_cases hn : ctx.layout.shardIds.length = 0
    · simp [hn] at h
    · cases hp : Params.calculate Config.pv86 ctx.layout.shardIds.length with
      | none => simp [hn, hp] at h
      | some p =>
        simp only [hn, hp, ↓reduceIte] at h
        simp only [Option.bind, bind, Option.some.injEq] at h
        subst h; simp) h

/-! ## Shard ids are `u64` -/

theorem leNat_lt : ∀ (bs : NearSpec.Bytes), NearSpec.leNat bs < 256 ^ bs.length
  | [] => by simp [NearSpec.leNat]
  | b :: bs => by
    simp only [NearSpec.leNat, List.length_cons, Nat.pow_succ]
    have ih := leNat_lt bs
    have := b.toNat_lt
    have : 256 * NearSpec.leNat bs + 256 ≤ 256 * 256 ^ bs.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    rw [Nat.mul_comm (256 ^ bs.length)]; omega

theorem takeN_length : ∀ (n : Nat) (bs h t : NearSpec.Bytes), NearSpec.takeN n bs = some (h, t) → h.length = n
  | 0, bs, h, t, e => by simp only [NearSpec.takeN, Option.some.injEq, Prod.mk.injEq] at e; rw [← e.1]; rfl
  | n + 1, [], h, t, e => by simp [NearSpec.takeN] at e
  | n + 1, b :: bs, h, t, e => by
    simp only [NearSpec.takeN] at e
    cases e' : NearSpec.takeN n bs with
    | none => rw [e'] at e; cases e
    | some r =>
      obtain ⟨h', t'⟩ := r
      rw [e'] at e
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      rw [← e.1, List.length_cons, takeN_length n bs h' t' e']

theorem pU64_lt {w : String} {bs rest : NearSpec.Bytes} {x : Nat} (h : pU64 w bs = .ok (x, rest)) :
    x < 2 ^ 64 := by
  unfold pU64 lift at h
  split at h
  · next r hr =>
    simp only [Except.ok.injEq] at h
    subst h
    unfold NearSpec.readU64 NearSpec.readLE at hr
    cases e : NearSpec.takeN 8 bs with
    | none => rw [e] at hr; cases hr
    | some q =>
      obtain ⟨hd, tl⟩ := q
      rw [e] at hr
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      rw [← hr.1]
      have := leNat_lt hd
      rw [takeN_length 8 bs hd tl e] at this
      simpa using this
  · cases h

theorem pMany_u64 {w : String} : ∀ (n : Nat) (bs rest : NearSpec.Bytes) (xs : List Nat),
    pMany (pU64 w) n bs = .ok (xs, rest) → ∀ x ∈ xs, x < 2 ^ 64
  | 0, bs, rest, xs, h => by
    simp only [pMany, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; simp
  | n + 1, bs, rest, xs, h => by
    simp only [pMany] at h
    obtain ⟨⟨a, bs1⟩, h1, h⟩ := bind_ok h
    obtain ⟨⟨as, bs2⟩, h2, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    intro x hx
    rcases List.mem_cons.1 hx with e | e
    · rw [e]; exact pU64_lt h1
    · exact pMany_u64 n bs1 bs2 as h2 x e

theorem pVec_u64 {w w' : String} {bs rest : NearSpec.Bytes} {xs : List Nat}
    (h : pVec w (pU64 w') bs = .ok (xs, rest)) : ∀ x ∈ xs, x < 2 ^ 64 := by
  unfold pVec at h
  obtain ⟨⟨n, bs1⟩, -, h⟩ := bind_ok h
  exact pMany_u64 n bs1 rest xs h

set_option maxHeartbeats 1000000 in
theorem decodeLayout_ids {b : NearSpec.Bytes} {L : Layout} (h : decodeLayout b = .ok L) :
    ∀ x ∈ L.shardIds, x < 2 ^ 64 := by
  unfold decodeLayout at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact pVec_u64 (by assumption)

/-- The closing step of `prepClaim` for the shard ids' range. -/
theorem ids64_close {L : Layout} {own g gp : Nat} {B2 : Blk} {xs : List Blk} {sched : List SchedPub}
    {f : ApplyCtx → Except String SchedPub} {b : NearSpec.Bytes}
    (hm : List.mapM f (blockCtx L own g B2 gp ::
      List.map (fun M => blockCtx L own g M M.hdr.nextGasPrice) xs) = .ok sched)
    (hf : ∀ ctx sp, f ctx = .ok sp → schedPub ctx = some sp) (hL : decodeLayout b = .ok L) :
    ∀ sp ∈ sched, ∀ x ∈ sp.ids, x < 2 ^ 64 := by
  intro sp hsp
  rw [ids_close hm hf sp hsp]
  exact decodeLayout_ids hL

set_option maxHeartbeats 4000000 in
theorem prepClaim_ids64 {cb : Bytes} {pc : PrepC} (h : prepClaim cb = .ok pc) :
    ∀ sp ∈ pc.sched, ∀ x ∈ sp.ids, x < 2 ^ 64 := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ids64_close (by assumption) (fun ctx sp hc => by
        split at hc
        · simp only [pure, Except.pure, Except.ok.injEq] at hc; subst hc; assumption
        · cases hc) (by assumption)

/-- **Every shard id of a successful `prepD0` is `< 2^64`.** -/
theorem prepD0_ids64 {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint = .ok p) :
    ∀ sp ∈ p.sched, ∀ x ∈ sp.ids, x < 2 ^ 64 := by
  unfold prepD0 at h
  obtain ⟨pc, hpc, hb⟩ := bind_ok h
  rw [prepBody_sched hb]
  exact prepClaim_ids64 hpc

end ZkFormal.NearV3.Sched
