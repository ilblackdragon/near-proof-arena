import ZkFormal.NearV3.Rcpt.Candidates.SourceCount
import ZkFormal.NearV3.Assembly.PrepFacts

namespace ZkFormal.NearV3.Rcpt.Candidates
open NearSpec NearSpecV3 Sched

private theorem forIn_growth {α β : Type} (measure : β → Nat) (cost : α → Nat)
    (f : α → β → Except String (ForInStep β)) :
    ∀ (xs : List α) (start out : β),
      (∀ a ∈ xs, ∀ b step, f a b = .ok step →
        (match step with | .done v => measure v | .yield v => measure v) ≤ measure b + cost a) →
      forIn xs start f = .ok out → measure out ≤ measure start + (xs.map cost).sum
  | [], start, out, _, h => by cases h; simp
  | a :: xs, start, out, hf, h => by
    rw [List.forIn_cons] at h
    obtain ⟨step, hs, h⟩ := bind_ok h
    have hh := hf a (by simp) start step hs
    cases step with
    | done v => cases h; dsimp only at hh; simp only [List.map_cons, List.sum_cons]; omega
    | yield v =>
      have ht := forIn_growth measure cost f xs v out (fun x hx => hf x (by simp [hx])) h
      simp only [List.map_cons, List.sum_cons]
      dsimp only at hh
      omega

private theorem const_sum {α : Type} (xs : List α) (c : Nat) :
    (xs.map fun _ => c).sum = c * xs.length := by
  induction xs with
  | nil => simp
  | cons a rest ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, Nat.mul_add, Nat.mul_one]; omega

def slotSources (B : Blk) : Except String (List SrcList) :=
  forIn B.slots [] fun x acc =>
    if x.1.heightIncluded == B.hdr.height then
      pure (.yield (acc ++ [⟨chunkHash x.1.inner x.2.encodedMerkleRoot,
        x.2.shardId, x.2.prevOutgoingReceiptsRoot⟩]))
    else pure (.yield acc)

theorem slotSources_count (B : Blk) {out : List SrcList} (h : slotSources B = .ok out) :
    out.length ≤ B.slots.length := by
  have hg := forIn_growth List.length (fun _ => 1) _ B.slots [] out (by
    intro x hx acc step hs
    split at hs <;> cases hs <;> simp) h
  simpa only [const_sum, Nat.one_mul, List.length_nil, Nat.zero_add] using hg

private theorem shuffle_length {α : Type} {xs ys : List α} {seed : Bytes}
    (h : shuffleWithSeed xs seed = some ys) : ys.length = xs.length := by
  classical
  unfold shuffleWithSeed at h
  cases hs : shuffle xs (Rng.ofSeed seed) with
  | none => simp [hs] at h
  | some p =>
    have he : p.1 = ys := by simpa [hs] using h
    have hp := shuffle_perm hs
    exact he ▸ hp.length_eq

def preparedSourceLists (blocks : List Blk) : Except String (List SrcList) :=
  forIn blocks [] fun B acc => do
    let srcs ← slotSources B
    let shuffled ← match shuffleWithSeed srcs B.hdr.prevHash with
      | some p => pure p
      | none => throw "invalid: shuffle fuel exhausted (probability < 2^-1024)"
    pure (.yield (acc ++ shuffled))

theorem preparedSourceLists_count (blocks : List Blk) {out : List SrcList}
    (hb : ∀ B ∈ blocks, B.slots.length ≤ 64) (h : preparedSourceLists blocks = .ok out) :
    out.length ≤ 64 * blocks.length := by
  have hg := forIn_growth List.length (fun _ => 64) _ blocks [] out (by
    intro B hB acc step hs
    obtain ⟨srcs, hsrc, hs⟩ := bind_ok hs
    have hc := slotSources_count B hsrc
    split at hs
    · rename_i p hp
      obtain ⟨shuffled, he, hs⟩ := bind_ok hs
      cases he
      cases hs
      have hh := shuffle_length hp
      have hbound := hb B hB
      simp only [List.length_append]
      omega
    · obtain ⟨_, he, _⟩ := bind_ok hs; cases he) h
  simpa only [const_sum, List.length_nil, Nat.zero_add] using hg

private theorem source_count_close {rs : List BlockRec} {blks : List Blk} {L : Layout}
    {start stop : Nat} {out : List SrcList}
    (hm : rs.mapM decodeBlk = .ok blks) (hr : rs.length ≤ 32)
    (hl : L.numShards ≤ 64) (hs : ∀ B ∈ blks, B.slots.length = L.numShards)
    (he : stop + 1 = blks.length)
    (hout : preparedSourceLists ((blks.drop start).take (stop - start)) = .ok out) : out.length ≤ 1984 := by
  have hmL := mapM_length decodeBlk rs blks hm
  have hb := sourceBlock_count blks start stop (by omega) he
  have hc := preparedSourceLists_count _ (by
    intro B hB
    have hbmem := List.mem_of_mem_drop (List.mem_of_mem_take hB)
    rw [hs B hbmem]
    exact hl) hout
  omega

set_option maxHeartbeats 4000000 in
/-- Successful actual claim preprocessing bounds all shuffled source occurrences. -/
theorem prepClaim_source_count {cb : Bytes} {pc : PrepC} (h : prepClaim cb = .ok pc) :
    pc.lists.length ≤ 1984 := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    apply source_count_close (by assumption)
    · have hh := check_ok (by assumption : check (decide (_ ≤ 32)) _ = .ok _)
      simpa using hh
    · have hh := check_ok (by assumption : check (decide (1 ≤ _) && decide (_ ≤ 64)) _ = .ok _)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hh
      exact hh.2
    · have hh := check_ok (by assumption : check (List.all _ (fun (b : Blk) => b.slots.length == _)) _ = .ok _)
      simpa only [List.all_eq_true, beq_iff_eq] using hh
    · have hh := check_ok (by assumption : check (_ + 1 == _) _ = .ok _)
      simpa only [beq_iff_eq] using hh
    · assumption

/-- The count survives the real body preprocessing unchanged. -/
theorem prepD0_source_count {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint = .ok p) :
    p.lists.length ≤ 1984 := by
  unfold prepD0 at h
  obtain ⟨pc, hc, hb⟩ := bind_ok h
  have he := (Assembly.prepBody_shape hb).2.2.1
  rw [he]
  exact prepClaim_source_count hc

end ZkFormal.NearV3.Rcpt.Candidates
