import ZkFormal.NearV3.Sched.Spec.Buckets

/-!
# ZkFormal.NearV3.Sched.Spec.Rounds — rounds of `process_bandwidth_requests` (definitions, local lemmas)

The AIR processes the loop as a list of **rounds** `RoundD = (key, z, ents)`: the popped key, its
0-round ordinal `z` (0 for positive keys, `1, 2, …` for the trailing key-0 rounds) and the bucket
entries `(ts, v)` in push order. `simR` replays the rounds: shuffle the entries with the state's
RNG (`NearSpecV3.shuffle`), then process them at consecutive times (`runL`, one `stepE` per entry),
collecting the re-pushes `(allowance, zNext, t, v + 1)`.

* `processBucket_runL`: the spec's `processBucket` on the entries' requests is `runL`, with the
  bucket map extended by the generated pushes (`bucketsOf` of the log, `Buckets.lean`);
* `shuffle_map`: `shuffle` commutes with `List.map`.
-/

namespace ZkFormal.NearV3.Sched

open NearSpecV3 NearSpecV3.Scheduler

/-- 0-round ordinal of a push with key `a` made in round `(K, z)` (`K > 0`: first 0-round). -/
def zNext (K z a : Nat) : Nat := if a = 0 then (if K = 0 then z + 1 else 1) else 0

/-- Process entry `v` at time `t` in round `(K, z)`. -/
def stepE (n : Nat) (allowed : Array Bool) (reqs : List Req) (K z t v : Nat) (st : St) :
    St × List PM :=
  match (reqAt reqs v).incs with
  | [] => (st, [])
  | inc :: rest =>
    let l := (reqAt reqs v).link
    let r := tryGrant n allowed st l inc
    if r.1 = true ∧ rest ≠ [] then
      (r.2, [⟨r.2.allowance[l]!, zNext K z r.2.allowance[l]!, t, v + 1⟩])
    else (r.2, [])

/-- Process a shuffled bucket at times `t, t+1, …`. -/
def runL (n : Nat) (allowed : Array Bool) (reqs : List Req) (K z : Nat) :
    List Nat → Nat → St → St × List PM
  | [], _, st => (st, [])
  | v :: vs, t, st =>
    let a := stepE n allowed reqs K z t v st
    let b := runL n allowed reqs K z vs (t + 1) a.1
    (b.1, a.2 ++ b.2)

/-- One round as the AIR records it. -/
structure RoundD where
  key : Nat
  z : Nat
  ents : List (Nat × Nat)
  deriving Repr

/-- Replay the rounds from time `t`. -/
def simR (n : Nat) (allowed : Array Bool) (reqs : List Req) :
    List RoundD → Nat → St → Option (St × List PM)
  | [], _, st => some (st, [])
  | R :: rs, t, st =>
    match shuffle (R.ents.map Prod.snd) st.rng with
    | none => none
    | some (sh, rng) =>
      let a := runL n allowed reqs R.key R.z sh t { st with rng := rng }
      match simR n allowed reqs rs (t + R.ents.length) a.1 with
      | none => none
      | some (st2, ps) => some (st2, a.2 ++ ps)

/-- Bucket entries of all rounds as push messages. -/
def entriesOf (rs : List RoundD) : List PM :=
  rs.flatMap fun R => R.ents.map fun e => ⟨R.key, R.z, e.1, e.2⟩

/-- Initial pushes: request `i` (in order) with its link's allowance, time `i`, entry `i·64`. -/
def initPushes (reqs : List Req) (st : St) : List PM :=
  (List.range reqs.length).map fun i =>
    let a := st.allowance[(reqs.getD i ⟨0, []⟩).link]!
    ⟨a, zNext 1 0 a, i, i * 64⟩

/-! ## `processBucket` = `runL` -/

theorem tryGrant_rng (n : Nat) (allowed : Array Bool) (st : St) (l bw : Nat) :
    (tryGrant n allowed st l bw).2.rng = st.rng := by
  unfold tryGrant grantMore
  split
  · rfl
  · simp only
    split <;> rfl

/-- `reqAt` of the next entry. -/
theorem reqAt_succ (reqs : List Req) (v : Nat) (hR : ∀ q ∈ reqs, q.incs.length < 64)
    {inc : Nat} {rest : List Nat} (h : (reqAt reqs v).incs = inc :: rest) (hr : rest ≠ []) :
    reqAt reqs (v + 1) = ⟨(reqAt reqs v).link, rest⟩ := by
  unfold reqAt at *
  simp only at h ⊢
  generalize hq : reqs.getD (v / 64) ⟨0, []⟩ = q at h
  have hlen : q.incs.length < 64 := by
    rw [← hq, List.getD_eq_getElem?_getD]
    cases hx : reqs[v / 64]? with
    | none => simp
    | some x => exact hR x (List.mem_of_getElem? hx)
  have hj : v % 64 + 2 ≤ q.incs.length := by
    have h1 := congrArg List.length h
    rw [List.length_drop, List.length_cons] at h1
    cases rest with
    | nil => exact absurd rfl hr
    | cons _ _ => simp at h1; omega
  have hd : (v + 1) / 64 = v / 64 := by omega
  have hm : (v + 1) % 64 = v % 64 + 1 := by omega
  rw [hd, hq, hm]
  congr 1
  rw [← List.drop_drop, h]
  rfl

theorem processBucket_runL (n : Nat) (allowed : Array Bool) (reqs : List Req)
    (hR : ∀ q ∈ reqs, q.incs.length < 64) (K z : Nat) :
    ∀ (vs : List Nat) (t : Nat) (st : St) (P : List PM),
      processBucket n allowed (vs.map (reqAt reqs)) (st, bucketsOf reqs P) =
        ((runL n allowed reqs K z vs t st).1, bucketsOf reqs (P ++ (runL n allowed reqs K z vs t st).2))
  | [], _, _, P => by simp [processBucket, runL]
  | v :: vs, t, st, P => by
    simp only [List.map_cons, processBucket, runL]
    unfold stepE
    split
    · next h => rw [h]; simpa using processBucket_runL n allowed reqs hR K z vs (t + 1) st P
    · next inc rest h =>
      rw [h]
      simp only
      by_cases hok : (tryGrant n allowed st (reqAt reqs v).link inc).1 = true ∧ rest ≠ []
      · rw [if_pos hok, if_pos hok]
        have e : bucketPush (tryGrant n allowed st (reqAt reqs v).link inc).2.allowance[(reqAt reqs v).link]!
            ⟨(reqAt reqs v).link, rest⟩ (bucketsOf reqs P) =
            bucketsOf reqs (P ++ [⟨(tryGrant n allowed st (reqAt reqs v).link inc).2.allowance[(reqAt reqs v).link]!,
              zNext K z (tryGrant n allowed st (reqAt reqs v).link inc).2.allowance[(reqAt reqs v).link]!, t, v + 1⟩]) := by
          simp only [bucketsOf, List.foldl_append, List.foldl_cons, List.foldl_nil]
          rw [reqAt_succ reqs v hR h hok.2]
        rw [e, processBucket_runL n allowed reqs hR K z vs (t + 1), List.append_assoc]
      · rw [if_neg hok, if_neg hok, processBucket_runL n allowed reqs hR K z vs (t + 1)]
        simp

/-! ## `shuffle` commutes with `map` -/

theorem swapAt_map {α β : Type} (f : α → β) (l : List α) (i j : Nat) :
    swapAt (l.map f) i j = (swapAt l i j).map f := by
  unfold swapAt
  simp only [List.getElem?_map]
  cases l[i]? <;> cases l[j]? <;> simp [List.map_set]

theorem shuffleLoop_map {α β : Type} (f : α → β) :
    ∀ (i : Nat) (l : List α) (r : Rng),
      shuffleLoop i (l.map f) r = (shuffleLoop i l r).map fun p => (p.1.map f, p.2)
  | 0, l, r => rfl
  | i + 1, l, r => by
    unfold shuffleLoop
    cases genIndex 64 (i + 2) r with
    | none => rfl
    | some p => simp only [swapAt_map]; exact shuffleLoop_map f i _ _

theorem shuffle_map {α β : Type} (f : α → β) (l : List α) (r : Rng) :
    shuffle (l.map f) r = (shuffle l r).map fun p => (p.1.map f, p.2) := by
  unfold shuffle
  rw [List.length_map]
  exact shuffleLoop_map f _ l r

theorem length_shuffleLoop {α : Type} :
    ∀ (i : Nat) (l : List α) (r : Rng) (l' : List α) (r' : Rng),
      shuffleLoop i l r = some (l', r') → l'.length = l.length
  | 0, l, r, l', r', h => by simp [shuffleLoop] at h; rw [← h.1]
  | i + 1, l, r, l', r', h => by
    unfold shuffleLoop at h
    cases hg : genIndex 64 (i + 2) r with
    | none => rw [hg] at h; cases h
    | some p =>
      rw [hg] at h
      have := length_shuffleLoop i _ _ l' r' h
      rw [this]
      unfold swapAt; split <;> simp

theorem length_shuffle {α : Type} {l l' : List α} {r r' : Rng} (h : shuffle l r = some (l', r')) :
    l'.length = l.length := length_shuffleLoop _ _ _ _ _ h

end ZkFormal.NearV3.Sched
