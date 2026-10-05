import ZkFormal.Prover.BcsOpen
import ZkFormal.Prover.BcsPrefix
import ZkFormal.Stark.QueryBound

/-!
# ZkFormal.Prover.BcsComplete — BCS completeness of `proveTree` (P1)

`bcs_complete32 : BcsCompleteStmt32`: for every pure hash `H` with **32-byte
answers**, if the IOP has at least one query position (`0 < numChunks`,
`0 < posPerChunk`), `Bcs.compile V` accepts the proof `proveTree V pr pub cb` of a
well-formed, IOP-complete honest prover.

Both extra hypotheses are necessary (the unrestricted `BcsCompleteStmt` is false):

* **hash length.** The compiled verifier parses every Merkle root as exactly 64
  bytes and compares it (`root' == root`) with a recomputed wide hash
  `H(..) ‖ H(..)`.  For `H := fun _ => []` every recomputed root is `[]`, so no
  proof of a schedule with an oracle is accepted (the parsed root has 64 bytes, or
  parsing fails).  `ProverComplete` (formal-core) quantifies over *every*
  `H : Bytes → Bytes`, so the fix belongs to the verifier: normalise oracle answers
  to 32 bytes (see `docs/zk-formal/REQUESTS.md`, R-L7-bcs-1).
* **at least one position.** With `numChunks = 0` (or `posPerChunk = 0`) the
  position list is empty, every multiproof has an empty leaf set, and `mpLevels`
  rejects (`[] ≠ [(0, root)]`), while an IOP with trivial `global`/`check` is
  complete.
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.Prover

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark

/-- (P1, corrected) BCS completeness for 32-byte hashes and a non-empty query phase. -/
def BcsCompleteStmt32 : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [StarkField F K] [StarkFieldLaws F K] [DecidableEq F]
    (V : IopSpec F K) (pr : IopProver F K) (pub cb : Bytes) (H : Bytes → Bytes),
    (∀ m, (fit32 (H m)).length = 32) → 0 < V.numChunks → 0 < V.posPerChunk →
    Bcs.Adapter.SchedOk V → ProverWf V pr cb → IopComplete V pr cb →
    (runH (pureH H) (proveTree V pr pub cb) ()).1.length ≤ V.maxProofBytes →
    (runH (pureH H) (Bcs.compile (F := F) V pub cb (runH (pureH H) (proveTree V pr pub cb) ()).1) ()).1
      = true

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [StarkFieldLaws F K] [DecidableEq F]

theorem ev_queryAnswers_length (H : Bytes → Bytes) (d : Bytes) :
    ∀ n, (ev H (queryAnswers d n)).length = n
  | 0 => rfl
  | n + 1 => by
    simp only [queryAnswers, ev_bind, ev_pure, ev_H, List.length_append, ev_queryAnswers_length H d n,
      List.length_singleton]

theorem positions_lt (V : IopSpec F K) (n0 : Nat) (answers : List Bytes) :
    ∀ x ∈ V.positions n0 answers, x < 2 ^ n0 := by
  intro x hx
  simp only [IopSpec.positions, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨_, _, _, _, rfl⟩ := hx
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem zip_map_map {α β γ : Type} (f : α → β) (g : α → γ) :
    ∀ l : List α, (l.map f).zip (l.map g) = l.map fun a => (f a, g a)
  | [] => rfl
  | a :: l => by simp [zip_map_map f g l]

/-- The proof starts with the header. -/
theorem readHeader_of_parseSlots {hdr : List Nat} {n : Nat} {qs : List Part} {ss : List Slot}
    {r : Bytes} {ps : List (PSlot K)} {rest : Bytes}
    (h : parseSlots (F := F) hdr (.msg (.header n :: qs) :: ss) r = some (ps, rest)) :
    ∃ r', readHeader n r = some (hdr, r') := by
  cases hr : readHeader n r with
  | none => simp [parseSlots, parseParts, hr] at h
  | some p =>
    obtain ⟨l, r'⟩ := p
    by_cases hl : l = hdr
    · subst hl; exact ⟨r', rfl⟩
    · simp [parseSlots, parseParts, hr, hl] at h

end

/-- **(P1, corrected)** BCS completeness of the honest prover model. -/
theorem bcs_complete32 : BcsCompleteStmt32 := by
  intro F K _ _ _ _ _ V pr pub cb H hH hnc hpp hS hw hc hmax
  change (ev H (Bcs.compile (F := F) V pub cb (ev H (proveTree V pr pub cb)))) = true
  change (ev H (proveTree V pr pub cb)).length ≤ _ at hmax
  obtain ⟨R, ps, ents, entsV, ts, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    ev_commitLoop H hw hH (V.schedule pr.hdr) ⟨whp H tagInit (initMsg pub cb), PT.init cb, [], []⟩
      inv_init
  generalize hst : ev H (commitLoop pr (V.schedule pr.hdr)
    ⟨whp H tagInit (initMsg pub cb), PT.init cb, [], []⟩) = st at *
  generalize hxs : V.positions (V.queryLog pr.hdr) (ev H (queryAnswers st.d V.numChunks)) = xs
  have hpt : ev H (proveTree V pr pub cb) = R ++ openBytes (K := K) (V.queryLog pr.hdr) xs ts := by
    simp only [proveTree, hw.hdrOk, ite_true, ev_bind, ev_WH, hst, ev_pure, h2, h3, hxs,
      List.nil_append]
  rw [hpt] at hmax ⊢
  -- parsing
  have hparse : parsePrefix (F := F) V (R ++ openBytes (K := K) (V.queryLog pr.hdr) xs ts) =
      some (pr.hdr, ps, openBytes (K := K) (V.queryLog pr.hdr) xs ts) := by
    obtain ⟨ps0, ss0, hsch⟩ := hS.first pr.hdr hw.hdrOk
    have hp := h5 (openBytes (K := K) (V.queryLog pr.hdr) xs ts)
    rw [hsch] at hp
    obtain ⟨r', hrh⟩ := readHeader_of_parseSlots hp
    simp only [parsePrefix, hrh, hw.hdrOk, ite_true, h5]
  simp only [PT.init, List.nil_append] at h1 h2 h3 h6
  have hn0 : ∀ t ∈ ts, TreeOk (K := K) H (V.queryLog pr.hdr) t := fun t ht =>
    ⟨(h11 t ht).1, (h11 t ht).2, hS.depth pr.hdr hw.hdrOk (shapesOf t.1)
      (by rw [← h10]; exact List.mem_map_of_mem ht)⟩
  have hxne : xs ≠ [] := by
    intro he
    have hl := positions_length V (V.queryLog pr.hdr) (ev H (queryAnswers st.d V.numChunks))
    rw [hxs, he, ev_queryAnswers_length] at hl
    simp at hl
    have := Nat.mul_pos hnc hpp
    omega
  have hxlt : ∀ x ∈ xs, x < 2 ^ V.queryLog pr.hdr := hxs ▸ positions_lt V _ _
  obtain ⟨ops, hev, hrows⟩ := ev_openAll (K := K) H hH (V.queryLog pr.hdr) xs hxne hxlt ts hn0 []
  rw [List.append_nil] at hev
  have hzip : (schedOracles (V.schedule pr.hdr)).zip (PT.mk cb entsV).oracles =
      ts.map fun t => (shapesOf t.1, rootOf t.2) := by
    rw [oracles_eq, h8, ← h10, zip_map_map]
  have hlen1 : (schedOracles (V.schedule pr.hdr)).length = ts.length := by rw [← h10, List.length_map]
  have hlen2 : (PT.mk cb entsV).oracles.length = ts.length := by rw [oracles_eq, h8, List.length_map]
  have herase : (PT.mk cb entsV : PT K Bytes).erase = st.τ.erase := by
    rw [h1]; simp only [PT.erase, h7]
  obtain ⟨hq, hτh⟩ := inv_end hw h4
  obtain ⟨hglob, hchk⟩ := hc st.τ h4.1 hq
  simp only [Bcs.compile, Nat.not_lt.mpr hmax, ite_false, hparse, ev_bind, ev_WH, h6, hxs, hzip,
    hev, ev_pure, List.isEmpty_nil, hlen1, hlen2, beq_self_eq_true, herase, hglob, Bool.true_and,
    List.all_eq_true]
  intro x hx
  have hr := hrows x hx
  simp only at hr
  rw [← h10, hr]
  have hdom : x < V.domSize st.τ := by simp only [IopSpec.domSize, hτh]; exact hxlt x hx
  have hck := hchk x hdom
  simp only [IopSpec.ChecksPass, IopSpec.trueOpenings, hτh] at hck
  rw [h1, oracles_eq, h9] at hck
  rw [h1]
  simpa [List.map_map, Function.comp_def] using hck

end ZkFormal.Prover
