import ZkFormal.NearV3.Sched.Pub.Raw
import NearSpecV3.PrepD0

/-!
# Public data guaranteed by `prepD0`

The verifier runs `prepD0` natively, so these facts about each instance's public data
`sp ∈ p.sched` come for free:

* `prepD0_sched`: `1 ≤ n ≤ 64`, `Params.calculate Config.pv86 n = some sp.params`, the
  sender keys of `sp.raw` are distinct (`BTreeMap` order), and each sender's `to_shard`s are
  distinct (A8, which `prepClaim` checks);
* `prepD0_rawOk`: hence `RawOk (instOf sp)` (at most `n² ≤ 4,096` raw requests).
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler NearSpec

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem throw_ne {α : Type} {e : String} {a : α} (h : (throw e : Except String α) = .ok a) : False := by
  cases h

theorem check_ok {b : Bool} {m : String} {u : Unit} (h : check b m = .ok u) : b = true := by
  unfold check at h; split at h
  · assumption
  · cases h

theorem mapM_ok {ε α β : Type} (f : α → Except ε β) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → ∀ y ∈ r, ∃ x ∈ l, f x = .ok y
  | [], r, h, y, hy => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; simp at hy
  | a :: t, r, h, y, hy => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    rcases List.mem_cons.1 hy with e | e
    · subst e; exact ⟨a, by simp, hb⟩
    · obtain ⟨x, hx, hfx⟩ := mapM_ok f t bs hbs y e
      exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-- The public-data facts of one instance. -/
structure SchedPubOk (sp : SchedPub) : Prop where
  n1 : 1 ≤ sp.ids.length
  n64 : sp.ids.length ≤ 64
  params : Params.calculate Config.pv86 sp.ids.length = some sp.params
  keys : (sp.raw.map Prod.fst).Nodup
  a8 : ∀ e ∈ sp.raw, (e.2.map (·.toShard)).Nodup

/-- `schedPub` of a block whose chunks satisfy A8, in a layout of `≤ 64` shards. -/
theorem schedPub_ok (L : Layout) (own g gp : Nat) (M : Blk) (hL : L.numShards ≤ 64)
    (hA : M.slots.all (fun x => match x with
      | (_, ci) => decide (List.map (fun x => x.toShard) ci.bwRequests).Nodup) = true)
    (sp : SchedPub) (h : schedPub (blockCtx L own g M gp) = some sp) : SchedPubOk sp := by
  unfold schedPub pubOf at h
  simp only [blockCtx] at h
  by_cases hn : L.shardIds.length = 0
  · simp [hn] at h
  · cases hp : Params.calculate Config.pv86 L.shardIds.length with
    | none => simp [hn, hp] at h
    | some p =>
      simp only [hn, hp, ↓reduceIte] at h
      simp only [Option.bind, bind, Option.some.injEq] at h
      subst h
      have hL' : L.shardIds.length ≤ 64 := hL
      refine ⟨Nat.pos_of_ne_zero hn, hL', hp, ?_, ?_⟩
      · exact (toBTreeMap_sorted _).imp (fun h => Nat.ne_of_lt h)
      · intro e he
        have he := toBTreeMap_mem _ e he
        simp only [List.map_map, List.mem_map, Function.comp] at he
        obtain ⟨⟨sl, ci⟩, hx, rfl⟩ := he
        have := List.all_eq_true.1 hA _ hx
        simp only [decide_eq_true_eq] at this
        simpa [List.map_map, Function.comp_def] using this

/-- The closing step of `prepClaim`: the scheduler public data come from blocks of the
segment, all of which passed the layout and A8 checks. -/
theorem sched_close {L : Layout} {blks : List Blk} {i : Nat} {b B2 : Blk} {own g gp : Nat}
    {sched : List SchedPub} {u1 u2 : Unit} {m1 m2 : String}
    {f : ApplyCtx → Except String SchedPub}
    (hm : List.mapM f (blockCtx L own g B2 gp ::
      List.map (fun M => blockCtx L own g M M.hdr.nextGasPrice) (List.take i blks).reverse) = .ok sched)
    (hb : blks[i]? = some b) (hpb : (pure b : Except String Blk) = .ok B2)
    (hL : check (decide (1 ≤ L.numShards) && decide (L.numShards ≤ 64)) m1 = .ok u1)
    (hA : check (blks.all fun b => b.slots.all fun x => match x with
      | (_, ci) => decide (List.map (fun x => x.toShard) ci.bwRequests).Nodup) m2 = .ok u2)
    (hf : ∀ ctx sp, f ctx = .ok sp → schedPub ctx = some sp) :
    ∀ sp ∈ sched, SchedPubOk sp := by
  have hL := check_ok hL
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hL
  have hA := List.all_eq_true.1 (check_ok hA)
  simp only [pure, Except.pure, Except.ok.injEq] at hpb; subst hpb
  have hB2 : b ∈ blks := List.mem_of_getElem? hb
  intro sp hsp
  obtain ⟨ctx, hctx, hfc⟩ := mapM_ok f _ _ hm sp hsp
  have hs := hf ctx sp hfc
  rcases List.mem_cons.1 hctx with e | e
  · subst e; exact schedPub_ok L own g gp b hL.2 (hA b hB2) sp hs
  · obtain ⟨M, hM, rfl⟩ := List.mem_map.1 e
    have hM' : M ∈ blks := List.mem_of_mem_take (List.mem_reverse.1 hM)
    exact schedPub_ok L own g _ M hL.2 (hA M hM') sp hs

set_option maxHeartbeats 4000000 in
/-- Every scheduler public record of a successful `prepClaim` satisfies `SchedPubOk`. -/
theorem prepClaim_sched {cb : Bytes} {pc : PrepC} (h : prepClaim cb = .ok pc) :
    ∀ sp ∈ pc.sched, SchedPubOk sp := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact sched_close (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (fun ctx sp hc => by
        split at hc
        · simp only [pure, Except.pure, Except.ok.injEq] at hc; subst hc; assumption
        · cases hc)

/-- `prepBody` keeps the scheduler public data. -/
theorem prepBody_sched {pc : PrepC} {hint : Hint} {p : Prep} (h : prepBody pc hint = .ok p) :
    p.sched = pc.sched := by
  unfold prepBody at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals first
    | (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; rfl)
    | (cases h)

/-- **Public-data facts of every scheduler instance of a successful `prepD0`.** -/
theorem prepD0_sched {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint = .ok p) :
    ∀ sp ∈ p.sched, SchedPubOk sp := by
  unfold prepD0 at h
  obtain ⟨pc, hpc, hb⟩ := bind_ok h
  rw [prepBody_sched hb]
  exact prepClaim_sched hpc

/-- **`RawOk` of every instance record of a successful `prepD0`.** -/
theorem prepD0_rawOk {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint = .ok p) :
    ∀ sp ∈ p.sched, RawOk (instOf sp) := by
  intro sp hsp
  have H := prepD0_sched h sp hsp
  exact rawOk_of sp (by have := H.n64; omega) H.keys H.a8

/-! ## Seeds are 32 bytes -/

set_option maxHeartbeats 2000000 in
theorem decodeBlockV6_hash {v : Nat} {ph lite rest : Bytes} {hdr : BlockHdr}
    (h : decodeBlockV6 v ph lite rest = .ok hdr) : hdr.hash.length = 32 := by
  unfold decodeBlockV6 at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp [blockHash, ArenaCore.sha256_length])

theorem decodeBlk_hash {r : BlockRec} {b : Blk} (h : decodeBlk r = .ok b) : b.hdr.hash.length = 32 := by
  unfold decodeBlk at h
  obtain ⟨hdr, hh, h⟩ := bind_ok h
  obtain ⟨sl, -, h⟩ := bind_ok h
  obtain ⟨u, -, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  exact decodeBlockV6_hash hh

/-- A hash-linked segment: every block but the last has a 32-byte `prevHash`. -/
theorem prevHash_len {blks : List Blk} {rs : List BlockRec} (hdec : List.mapM decodeBlk rs = .ok blks)
    {u : Unit} {m : String}
    (hlink : check ((blks.zip (List.drop 1 (List.map (fun x => x.hdr.hash) blks))).all fun x =>
        match x with
        | (b, h) => b.hdr.prevHash == h) m = .ok u)
    {k : Nat} (hk : k + 1 < blks.length) : blks[k].hdr.prevHash.length = 32 := by
  have hall := List.all_eq_true.1 (check_ok hlink)
  have hmem : (blks[k], (List.drop 1 (List.map (fun x => x.hdr.hash) blks))[k]'(by simp; omega)) ∈
      blks.zip (List.drop 1 (List.map (fun x => x.hdr.hash) blks)) := by
    have := List.getElem_mem (l := blks.zip (List.drop 1 (List.map (fun x => x.hdr.hash) blks)))
      (n := k) (by simp; omega)
    simpa [List.getElem_zip] using this
  have e := hall _ hmem
  simp only [beq_iff_eq] at e
  rw [e]
  simp only [List.getElem_drop, List.getElem_map]
  obtain ⟨r, -, hr⟩ := mapM_ok decodeBlk rs blks hdec _ (List.getElem_mem (l := blks) (n := k + 1) hk)
  have e2 := decodeBlk_hash hr
  simp only [show 1 + k = k + 1 by omega]
  exact e2

/-- The closing step of `prepClaim` for seeds. -/
theorem seed_close {rs : List BlockRec} {blks : List Blk} {L : Layout} {i j : Nat} {b B2 : Blk}
    {own g gp stop : Nat} {sched : List SchedPub} {u1 u2 : Unit} {m1 m2 : String}
    {f : ApplyCtx → Except String SchedPub}
    (hdec : List.mapM decodeBlk rs = .ok blks)
    (hlink : check ((blks.zip (List.drop 1 (List.map (fun x => x.hdr.hash) blks))).all fun x =>
        match x with
        | (b, h) => b.hdr.prevHash == h) m1 = .ok u1)
    (hm : List.mapM f (blockCtx L own g B2 gp ::
      List.map (fun M => blockCtx L own g M M.hdr.nextGasPrice) (List.take i blks).reverse) = .ok sched)
    (hb : blks[i]? = some b) (hpb : (pure b : Except String Blk) = .ok B2)
    (hst : (pure (i + 1 + j) : Except String Nat) = .ok stop)
    (hlen : check (stop + 1 == blks.length) m2 = .ok u2)
    (hf : ∀ ctx sp, f ctx = .ok sp → schedPub ctx = some sp) :
    ∀ sp ∈ sched, sp.seed.length = 32 := by
  have hl := check_ok hlen
  simp only [beq_iff_eq] at hl
  simp only [pure, Except.pure, Except.ok.injEq] at hpb hst; subst hpb hst
  have hi : i + 1 < blks.length := by omega
  have hseed : ∀ ctx sp, schedPub ctx = some sp → sp.seed = ctx.prevBlockHash := by
    intro ctx sp h
    unfold schedPub pubOf at h
    by_cases hn : ctx.layout.shardIds.length = 0
    · simp [hn] at h
    · cases hp : Params.calculate Config.pv86 ctx.layout.shardIds.length with
      | none => simp [hn, hp] at h
      | some p =>
        simp only [hn, hp, ↓reduceIte] at h
        simp only [Option.bind, bind, Option.some.injEq] at h
        subst h; rfl
  intro sp hsp
  obtain ⟨ctx, hctx, hfc⟩ := mapM_ok f _ _ hm sp hsp
  rw [hseed ctx sp (hf ctx sp hfc)]
  rcases List.mem_cons.1 hctx with e | e
  · subst e
    have hbi : blks[i] = b := by
      rw [List.getElem?_eq_getElem (by omega)] at hb; exact Option.some.inj hb
    simp only [blockCtx]
    rw [← hbi]
    exact prevHash_len hdec hlink hi
  · obtain ⟨M, hM, rfl⟩ := List.mem_map.1 e
    obtain ⟨k, hk, hkM⟩ := List.getElem_of_mem (List.mem_reverse.1 hM)
    rw [List.getElem_take] at hkM
    have hk' : k < i := by simp at hk; omega
    simp only [blockCtx]
    rw [← hkM]
    exact prevHash_len hdec hlink (by omega)

set_option maxHeartbeats 4000000 in
/-- Every seed of a successful `prepClaim` is 32 bytes. -/
theorem prepClaim_seed {cb : Bytes} {pc : PrepC} (h : prepClaim cb = .ok pc) :
    ∀ sp ∈ pc.sched, sp.seed.length = 32 := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact seed_close (by assumption) (by assumption) (by assumption) (by assumption)
      (by assumption) (by assumption) (by assumption) (fun ctx sp hc => by
        split at hc
        · simp only [pure, Except.pure, Except.ok.injEq] at hc; subst hc; assumption
        · cases hc)

/-- **Every scheduler seed of a successful `prepD0` is 32 bytes.** -/
theorem prepD0_seed {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint = .ok p) :
    ∀ sp ∈ p.sched, sp.seed.length = 32 := by
  unfold prepD0 at h
  obtain ⟨pc, hpc, hb⟩ := bind_ok h
  rw [prepBody_sched hb]
  exact prepClaim_seed hpc

end ZkFormal.NearV3.Sched
