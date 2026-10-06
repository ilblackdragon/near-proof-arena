import ZkFormal.Assembly.Guard

/-!
# ZkFormal.V3.Hint — proof-carried hints and native public preprocessing (v3 D0 design PoC)

Design: `docs/zk-formal/V3-D0-DESIGN.md` §2.2, §6 (PoC 1).

The v3 D0 verifier does not hand the claim bytes to the STARK. It

1. splits the proof `pb` into a clear **hint** `h` and a STARK proof `π`
   (`split pb = some (h, π)`); for D0, `h` holds the scheduler-state value read at
   `0x0f`, the fixed-key queue values, the applied-receipt count and the outgoing
   body `B` (spec step 18's `borsh((txs, outgoing))`);
2. runs a **native preprocessing** `prep cb h` built from the trusted spec's own
   functions (claim decoding, block-hash chain, `chunk_headers_root`, the walk,
   ChaCha20 shuffles, exact-binary64 congestion, the bandwidth scheduler,
   Reed–Solomon + `encoded_merkle_root`, outgoing-receipts root, forwarding limits):
   either it rejects, or it returns the bytes `cb'` of the prepared public statement;
3. runs the unmodified STARK verifier on `(cb', π)`.

`romSound_hint` transfers `RomSound` from the inner verifier (language `L'` over
prepared statements) to the composed verifier (language `L` over claims), given only
the deterministic implication `prep cb h = some cb' → L' cb' → L cb`. This is the
ROM-game half of the soundness of "move public-only computation out of the AIR";
the other half is the semantic factorization of `RelD0` (design §6, obligations
`FactorSound`/`FactorComplete`).

The reduction post-composes the adversary with a pure map (same oracle queries,
same tape), exactly like `CoinAdversary.map`; the inner verifier then runs on the
same oracle state. No query budget changes.

`stream_eq_of_count` is PoC 2: a byte stream bound to public bus messages by
multiset balance equals the public bytes (how the outgoing body `B` of the hint is
tied to the refund stream of the receipt table, design §3.4).
-/

namespace ZkFormal.V3

open ArenaCore ArenaCore.Security ZkFormal

/-! ## PoC 1: hints + native preprocessing in front of a tree verifier -/

/-- The composed verifier: split the proof, preprocess natively, run `V` on the
prepared statement. Rejects (without oracle queries) when either step fails. -/
def hintTree (split : Bytes → Option (Bytes × Bytes)) (prep : Bytes → Bytes → Option Bytes)
    (V : TreeVerifier) : TreeVerifier :=
  ⟨fun pub cb pb =>
    match split pb with
    | some (h, π) =>
      match prep cb h with
      | some cb' => V.tree pub cb' π
      | none => .pure false
    | none => .pure false⟩

/-- What the inner verifier sees for the composed verifier's input `(cb, pb)`.
On failure, any pair will do (the composed verifier rejects without queries). -/
def inner (split : Bytes → Option (Bytes × Bytes)) (prep : Bytes → Bytes → Option Bytes)
    (cb pb : Bytes) : Bytes × Bytes :=
  match split pb with
  | some (h, π) =>
    match prep cb h with
    | some cb' => (cb', π)
    | none => (cb, pb)
  | none => (cb, pb)

/-- Post-composition with a pure map keeps every weighted query budget. -/
theorem queryBound_bind_pure {spec : OracleSpec} {α β : Type} (w : spec.Query → Nat) (f : α → β) :
    ∀ (oa : OracleComp spec α) (n : Nat), OracleComp.QueryBound w oa n →
      OracleComp.QueryBound w (oa.bind fun a => .pure (f a)) n
  | .pure a, n, _ => .pure (f a) n
  | .query q k, n, h => by
    cases h with
    | query _ _ _ hq hk =>
      exact .query q _ n hq fun r => queryBound_bind_pure w f (k r) (n - w q) (hk r)

/-- **ROM soundness through hints and native preprocessing.** If the inner verifier
`V` is `RomSound` for the language `L'` of prepared statements, the composed verifier
`hintTree split prep V` is `RomSound` (same budgets, same bound) for every claim
language `L` such that a prepared statement in `L'` certifies its claim. -/
theorem romSound_hint {S : ChallengeSpec} {L L' : Bytes → Prop}
    (split : Bytes → Option (Bytes × Bytes)) (prep : Bytes → Bytes → Option Bytes)
    (hprep : ∀ cb h cb', prep cb h = some cb' → L' cb' → L cb)
    (V : TreeVerifier) (P : OracleProver S) (pub : Bytes) {qH qP n num den : Nat}
    (hV : RomSound S L' V.toVerifier P pub qH qP n num den) :
    RomSound S L (hintTree split prep V).toVerifier P pub qH qP n num den := by
  intro A hH hP
  let f : Bytes × Bytes → Bytes × Bytes := fun x => inner split prep x.1 x.2
  let A' : RomAdversary S := A.bind fun x => .pure (f x)
  have hH' := queryBound_bind_pure hashWeight f A qH hH
  have hP' := queryBound_bind_pure proveWeight f A qP hP
  refine PrLE.mono (fun t hw => ?_) (hV A' hH' hP')
  unfold romWins at hw ⊢
  have hsim : OracleComp.simulate (romImpl S P pub) A' (LazyRO.init t) =
      (f (OracleComp.simulate (romImpl S P pub) A (LazyRO.init t)).1,
        (OracleComp.simulate (romImpl S P pub) A (LazyRO.init t)).2) :=
    CoinAdversary.simulate_bind_pure _ f A _
  rw [hsim]
  simp only [TreeVerifier.toVerifier, hintTree] at hw ⊢
  generalize OracleComp.simulate (romImpl S P pub) A (LazyRO.init t) = r1 at hw ⊢
  obtain ⟨⟨cb, pb⟩, s⟩ := r1
  simp only [f, inner] at hw ⊢
  cases hs : split pb with
  | none =>
    rw [hs] at hw
    rcases hw with hw | ⟨hacc, _⟩
    · exact Or.inl (Assembly.runH_overflow _ _ hw)
    · cases hacc
  | some hp =>
    obtain ⟨h, π⟩ := hp
    rw [hs] at hw
    simp only at hw ⊢
    cases hc : prep cb h with
    | none =>
      rw [hc] at hw
      rcases hw with hw | ⟨hacc, _⟩
      · exact Or.inl (Assembly.runH_overflow _ _ hw)
      · cases hacc
    | some cb' =>
      rw [hc] at hw
      simp only at hw ⊢
      rcases hw with hw | ⟨hacc, hn⟩
      · exact Or.inl hw
      · exact Or.inr ⟨hacc, fun hl => hn (hprep cb h cb' hc hl)⟩

/-! ## PoC 2: binding a stream to public bus messages -/

/-- A stream of `n` (index, value) messages. -/
def stream (n : Nat) (v : Nat → Nat) : List (Nat × Nat) := (List.range n).map fun i => (i, v i)

theorem mem_stream {n : Nat} {v : Nat → Nat} {x : Nat × Nat} :
    x ∈ stream n v ↔ x.1 < n ∧ x.2 = v x.1 := by
  obtain ⟨a, b⟩ := x
  simp only [stream, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩; exact ⟨hi, rfl⟩
  · rintro ⟨ha, rfl⟩; exact ⟨a, ha, rfl, rfl⟩

/-- **Stream binding.** If the AIR side sends `(i, s i)` for `i < n` and the verifier
injects `(i, B i)` for `i < m` on the same bus, and the bus balances (equal counts of
every message), then `n = m` and the streams agree. (Used with `B` = the hint's
outgoing body; the AIR stream is the receipt table's refund stream.) -/
theorem stream_eq_of_count {n m : Nat} {s B : Nat → Nat}
    (hbal : ∀ x, (stream n s).count x = (stream m B).count x) :
    n = m ∧ ∀ i, i < n → s i = B i := by
  have side : ∀ i, i < n → i < m ∧ s i = B i := by
    intro i hi
    have h1 : (i, s i) ∈ stream n s := mem_stream.2 ⟨hi, rfl⟩
    have h2 : (i, s i) ∈ stream m B := by
      rw [← List.count_pos_iff, ← hbal, List.count_pos_iff]; exact h1
    obtain ⟨hm, he⟩ := mem_stream.1 h2
    exact ⟨hm, he⟩
  have side' : ∀ i, i < m → i < n := by
    intro i hi
    have h1 : (i, B i) ∈ stream m B := mem_stream.2 ⟨hi, rfl⟩
    have h2 : (i, B i) ∈ stream n s := by
      rw [← List.count_pos_iff, hbal, List.count_pos_iff]; exact h1
    exact (mem_stream.1 h2).1
  refine ⟨?_, fun i hi => (side i hi).2⟩
  rcases Nat.lt_trichotomy n m with h | h | h
  · exact absurd (side' n h) (Nat.lt_irrefl n)
  · exact h
  · exact absurd (side m h).1 (Nat.lt_irrefl m)

/-! ## Budget constants used in the design (kernel-checked) -/

/-- Transfer receipt gas `G` at PV 86 (`NearSpec.Params.G`). -/
def gasG : Nat := 108059500000 + 115123062500

/-- Under amendment A1 (`gas_limit ≤ 10^15`), at most 4481 receipts are applied:
receipt `i` is delayed iff `i·G ≥ gas_limit`, so `n·G` may exceed the limit only by the
last one: `(n − 1)·G < 10^15` forces `n ≤ 4481`. -/
theorem max_receipts : (4480 * gasG < 10 ^ 15) ∧ ¬ (4481 * gasG < 10 ^ 15) := by decide

/-- Size of the canonical bandwidth-scheduler state for `k` shards
(`u8 tag ‖ u32 count ‖ k²·(u64,u64,u64) ‖ hash`). -/
def schedStateLen (k : Nat) : Nat := 1 + 4 + 24 * k * k + 32

theorem schedStateLen_64 : schedStateLen 64 = 98341 := by decide
theorem schedStateLen_6 : schedStateLen 6 = 901 := by decide

end ZkFormal.V3
