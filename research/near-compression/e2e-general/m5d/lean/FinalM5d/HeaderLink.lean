import FinalM5d.Decode

/-!
# FinalM5d.HeaderLink — the `FIN` row's byte relations give `headerOk`

`RowOK hb fi ro rs rsh n` is what the `FIN` row's constraints say about its cells (read as
naturals; `FinalM5d.FinRow.rowOK_of_constraints` derives it from the constraints over BabyBear):
`hb` the statement stream's first 424 bytes (the chunk inner at `CI_OFF = 114`), `fi` the `FinIn`
record, `ro`/`rs`/`rsh` the outcome / part / shard tree roots the row receives, `n` the public
body length. Positions are absolute stream offsets (`114 + H_*`).

`row_headerOk`: then the spec's decoder accepts the public chunk inner, and **`headerOk H o`**
(lane E's `FinalOut`, all 13 comparisons) holds between the decoded header `H` and the outputs
`o = outputsOf fi ro rs rsh n` — the `Outputs` record whose fields are `FinIn`'s (state root, gas
used, gas limit, balance burnt, congestion, empty proposals / bandwidth requests / split), the
computed tree roots, `zeroHash` as the transaction root (class F1: no transactions), and `n`.
-/

namespace FinalM5d.Link

open NearSpec NearSpecV3 NearSpecV3.E2E FinalM5d.Decode

/-- `n` bytes of a cell function from offset `a`. -/
def slice (f : Nat → Nat) (a n : Nat) : Bytes := (List.range n).map fun j => UInt8.ofNat (f (a + j))

theorem slice_add (f : Nat → Nat) (a n m : Nat) :
    slice f a (n + m) = slice f a n ++ slice f (a + n) m := by
  simp only [slice, List.range_add, List.map_append, List.map_map, Function.comp_def, Nat.add_assoc]

theorem slice_length (f : Nat → Nat) (a n : Nat) : (slice f a n).length = n := by
  simp [slice]

theorem slice_congr {f g : Nat → Nat} {a b n : Nat} (h : ∀ j, j < n → f (a + j) = g (b + j)) :
    slice f a n = slice g b n := by
  simp only [slice]
  apply List.map_congr_left
  intro j hj
  rw [h j (List.mem_range.1 hj)]

theorem slice_zero {f : Nat → Nat} {a n : Nat} (h : ∀ j, j < n → f (a + j) = 0) :
    slice f a n = zeros n := by
  rw [slice_congr (g := fun _ => 0) (b := 0) (fun j hj => h j hj)]
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [slice_add, ih (fun j hj => h j (by omega))]
    simp only [slice, List.range_one, List.map_cons, List.map_nil]
    clear ih h
    induction k with
    | zero => rfl
    | succ k ih2 => simp only [zeros, List.cons_append, ih2]

/-- The `FIN` row's relations (class F1), at absolute stream offsets. -/
structure RowOK (hb fi ro rs rsh : Nat → Nat) (n : Nat) : Prop where
  tag : hb 114 = 4
  psr : ∀ j, j < 32 → hb (147 + j) = fi (0 + j)
  por : ∀ j, j < 32 → hb (179 + j) = ro (0 + j)
  emr : ∀ j, j < 32 → hb (211 + j) = rs (0 + j)
  el : n = hb 243 + 256 * hb 244 + 65536 * hb 245
  el0 : ∀ j, j < 5 → hb (246 + j) = 0
  gu : ∀ j, j < 8 → hb (267 + j) = fi (75 + j)
  gl : ∀ j, j < 8 → hb (275 + j) = fi (99 + j)
  bb : ∀ j, j < 16 → hb (283 + j) = fi (83 + j)
  orr : ∀ j, j < 32 → hb (299 + j) = rsh (0 + j)
  txr : ∀ j, j < 32 → hb (331 + j) = 0
  props : ∀ j, j < 4 → hb (363 + j) = 0
  cong : ∀ j, j < 43 → hb (367 + j) = fi (32 + j)
  congTag : fi 32 = 0
  bw : ∀ j, j < 5 → hb (410 + j) = 0
  split : hb 415 = 0
  bytes : ∀ k, k < 424 → hb k < 256

/-- The decoded header of the window. -/
def hdrOf (hb : Nat → Nat) : ChunkInner :=
  hdrF1 (slice hb 115 32) (slice hb 147 32) (slice hb 179 32) (slice hb 211 32) (slice hb 243 8)
    (slice hb 251 8) (slice hb 259 8) (slice hb 267 8) (slice hb 275 8) (slice hb 283 16)
    (slice hb 299 32) (slice hb 331 32) (slice hb 368 16) (slice hb 384 16) (slice hb 400 8)
    (slice hb 408 2)

/-- The outputs the template computes (class F1). -/
def outputsOf (fi ro rs rsh : Nat → Nat) (n : Nat) : Outputs :=
  { stateRoot := slice fi 0 32, outcomeRoot := slice ro 0 32, proposals := [],
    gasLimit := leNat (slice fi 99 8), gasUsed := leNat (slice fi 75 8),
    balanceBurnt := leNat (slice fi 83 16), outgoingRoot := slice rsh 0 32,
    congestion := ⟨leNat (slice fi 33 16), leNat (slice fi 49 16), leNat (slice fi 65 8),
      leNat (slice fi 73 2)⟩,
    bwRequests := [], proposedSplit := none, txRoot := zeroHash,
    encodedMerkleRoot := slice rs 0 32, encodedLength := n }

/-- The chunk-inner window of the stream. -/
def win (hb : Nat → Nat) : Bytes := slice hb 114 302

theorem slice_one (f : Nat → Nat) (a : Nat) : slice f a 1 = [UInt8.ofNat (f a)] := by
  simp [slice]

theorem win_split (hb : Nat → Nat) :
    win hb = slice hb 114 1 ++ slice hb 115 32 ++ slice hb 147 32 ++ slice hb 179 32 ++
      slice hb 211 32 ++ slice hb 243 8 ++ slice hb 251 8 ++ slice hb 259 8 ++ slice hb 267 8 ++
      slice hb 275 8 ++ slice hb 283 16 ++ slice hb 299 32 ++ slice hb 331 32 ++ slice hb 363 4 ++
      slice hb 367 1 ++ slice hb 368 16 ++ slice hb 384 16 ++ slice hb 400 8 ++ slice hb 408 2 ++
      slice hb 410 1 ++ slice hb 411 4 ++ slice hb 415 1 := by
  simp only [win, List.append_assoc]
  rw [show (302 : Nat) = 1 + (32 + (32 + (32 + (32 + (8 + (8 + (8 + (8 + (8 + (16 + (32 + (32 +
      (4 + (1 + (16 + (16 + (8 + (2 + (1 + (4 + 1)))))))))))))))))))) from rfl]
  repeat rw [slice_add]

theorem toNat_ofNat {x : Nat} (h : x < 256) : (UInt8.ofNat x).toNat = x := UInt8.toNat_ofNat_of_lt' h

theorem leNat_slice8 (f : Nat → Nat) (a : Nat) (h0 : f a < 256) (h1 : f (a + 1) < 256)
    (h2 : f (a + 2) < 256) (hz : ∀ j, j < 5 → f (a + 3 + j) = 0) :
    leNat (slice f a 8) = f a + 256 * f (a + 1) + 65536 * f (a + 2) := by
  have z0 := hz 0 (by omega); have z1 := hz 1 (by omega); have z2 := hz 2 (by omega)
  have z3 := hz 3 (by omega); have z4 := hz 4 (by omega)
  simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at z0 z1 z2 z3 z4
  simp only [slice, List.range_succ, List.range_zero, List.nil_append, List.map_append, List.map_cons,
    List.map_nil, List.cons_append, List.singleton_append, leNat, Nat.add_zero,
    Nat.add_assoc, Nat.reduceAdd, z0, z1, z2, z3, z4, toNat_ofNat h0, toNat_ofNat h1,
    toNat_ofNat h2, toNat_ofNat (show 0 < 256 by omega)]
  omega

/-- **The `FIN` row gives `FinalOut`.** -/
theorem row_headerOk {hb fi ro rs rsh : Nat → Nat} {n : Nat} (h : RowOK hb fi ro rs rsh n) :
    decodeChunkInner (win hb) = .ok (hdrOf hb) ∧
      headerOk (hdrOf hb) (outputsOf fi ro rs rsh n) = true := by
  constructor
  · have e : win hb = encF1 (slice hb 115 32) (slice hb 147 32) (slice hb 179 32) (slice hb 211 32)
        (slice hb 243 8) (slice hb 251 8) (slice hb 259 8) (slice hb 267 8) (slice hb 275 8)
        (slice hb 283 16) (slice hb 299 32) (slice hb 331 32) (slice hb 368 16) (slice hb 384 16)
        (slice hb 400 8) (slice hb 408 2) := by
      have t1 : slice hb 114 1 = [4] := by rw [slice_one, h.tag]; rfl
      have t2 : slice hb 363 4 = [0, 0, 0, 0] := by rw [slice_zero h.props]; rfl
      have t3 : slice hb 367 1 = [0] := by
        have := h.cong 0 (by omega)
        simp only [Nat.add_zero] at this
        rw [slice_one, this, h.congTag]; rfl
      have t4 : slice hb 410 1 = [0] := by
        have := h.bw 0 (by omega)
        simp only [Nat.add_zero] at this
        rw [slice_one, this]; rfl
      have t5 : slice hb 411 4 = [0, 0, 0, 0] := by
        rw [slice_zero (fun j hj => by
          have := h.bw (1 + j) (by omega)
          rwa [show 410 + (1 + j) = 411 + j by omega] at this)]
        rfl
      have t6 : slice hb 415 1 = [0] := by rw [slice_one, h.split]; rfl
      rw [win_split, t1, t2, t3, t4, t5, t6]
      rfl
    rw [e]
    exact decode_F1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (slice_length _ _ _) (slice_length _ _ _)
      (slice_length _ _ _) (slice_length _ _ _) (slice_length _ _ _) (slice_length _ _ _)
      (slice_length _ _ _) (slice_length _ _ _) (slice_length _ _ _) (slice_length _ _ _)
      (slice_length _ _ _) (slice_length _ _ _) (slice_length _ _ _) (slice_length _ _ _)
      (slice_length _ _ _) (slice_length _ _ _)
  · have psr := slice_congr (n := 32) h.psr
    have por := slice_congr (n := 32) h.por
    have emr := slice_congr (n := 32) h.emr
    have gu := slice_congr (n := 8) h.gu
    have gl := slice_congr (n := 8) h.gl
    have bb := slice_congr (n := 16) h.bb
    have orr := slice_congr (n := 32) h.orr
    have txr := slice_zero (n := 32) h.txr
    have cd := slice_congr (f := hb) (g := fi) (a := 368) (b := 33) (n := 16)
      (fun j hj => by have := h.cong (1 + j) (by omega); rwa [show 367 + (1 + j) = 368 + j by omega,
        show 32 + (1 + j) = 33 + j by omega] at this)
    have cb := slice_congr (f := hb) (g := fi) (a := 384) (b := 49) (n := 16)
      (fun j hj => by have := h.cong (17 + j) (by omega); rwa [show 367 + (17 + j) = 384 + j by omega,
        show 32 + (17 + j) = 49 + j by omega] at this)
    have cr := slice_congr (f := hb) (g := fi) (a := 400) (b := 65) (n := 8)
      (fun j hj => by have := h.cong (33 + j) (by omega); rwa [show 367 + (33 + j) = 400 + j by omega,
        show 32 + (33 + j) = 65 + j by omega] at this)
    have ca := slice_congr (f := hb) (g := fi) (a := 408) (b := 73) (n := 2)
      (fun j hj => by have := h.cong (41 + j) (by omega); rwa [show 367 + (41 + j) = 408 + j by omega,
        show 32 + (41 + j) = 73 + j by omega] at this)
    have el : leNat (slice hb 243 8) = n := by
      rw [leNat_slice8 hb 243 (h.bytes 243 (by omega)) (h.bytes 244 (by omega)) (h.bytes 245 (by omega))
        (fun j hj => by rw [show 243 + 3 + j = 246 + j by omega]; exact h.el0 j hj), h.el]
    simp only [headerOk, hdrOf, hdrF1, outputsOf, psr, por, emr, gu, gl, bb, orr, txr, cd, cb, cr, ca,
      el, beq_self_eq_true, Bool.and_self, zeroHash]

end FinalM5d.Link
