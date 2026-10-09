import ZkFormal.Size.Sched
import ZkFormal.Udr.Np.Commits

/-!
# Size bounds for aligned FRI roll-ins

This is a conditional bound for the existing verifier schedule. It does not
change verifier parameters or assume arbitrary trace heights are aligned.
The honest trace construction must establish `RollAligned` for its header.
-/
namespace ZkFormal.Size

open ArenaCore Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Prover
  ZkFormal.Prover.SizeBound ZkFormal.V2.SizeSched

/-- Every nonfinal roll-in lands on a regular commitment layer. -/
def RollAligned (A : Air) (prm : Params) (hdr : List Nat) : Prop :=
  ∀ i, i < finalLayer A prm hdr → rollInAt A prm hdr i = true →
    max prm.maxArityLog 1 ∣ i

/-- A table-height condition sufficient for alignment. It is checked on each
LDE height, relative to the actual query height, rather than on static maxima. -/
theorem rollAligned_of_layout (A : Air) (prm : Params) (hdr : List Nat)
    (h : ∀ L ∈ layout A prm hdr,
      max prm.maxArityLog 1 ∣ queryLog A prm hdr - L.lde) :
    RollAligned A prm hdr := by
  intro i _ hi
  simp only [rollInAt, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true, beq_iff_eq] at hi
  obtain ⟨L, hL, he⟩ := hi.2
  have hd := h L hL
  have : queryLog A prm hdr - L.lde = i := by omega
  rwa [this] at hd

/-- Aligned roll-ins cannot shorten an ordinary commitment step. -/
theorem aligned_next (A : Air) (prm : Params) (hdr : List Nat) (ℓ c nxt : Nat)
    (ha : ∀ i, i < ℓ → rollInAt A prm hdr i = true → max prm.maxArityLog 1 ∣ i)
    (hc : max prm.maxArityLog 1 ∣ c)
    (hcn : c < nxt) (hn : nxt ≤ ℓ) (hstep : nxt - c ≤ max prm.maxArityLog 1)
    (hstop : nxt = ℓ ∨ rollInAt A prm hdr nxt = true ∨ nxt = c + max prm.maxArityLog 1) :
    nxt = min (c + max prm.maxArityLog 1) ℓ := by
  rcases hstop with h | h | h
  · omega
  · by_cases he : nxt = ℓ
    · omega
    · have hd := Nat.dvd_sub (ha nxt (by omega) h) hc
      have hl := Nat.le_of_dvd (by omega : 0 < nxt - c) hd
      omega
  · omega

/-- The actual commitment schedule has the no-forced-roll-in DP bound when
its header is aligned. The DP's roll-in count is zero, even though aligned
roll-in messages remain present in the protocol. -/
theorem go_aligned (A : Air) (prm : Params) (hdr : List Nat)
    (cost : Nat → Nat → Nat) (fc : Nat × Nat → Nat) (ℓ : Nat)
    (hfc : ∀ c a, c + a ≤ ℓ → fc (c, a) ≤ cost (ℓ - c) a)
    (ha : ∀ i, i < ℓ → rollInAt A prm hdr i = true → max prm.maxArityLog 1 ∣ i) :
    ∀ fuel c, (c < ℓ → max prm.maxArityLog 1 ∣ c) →
      ((friCommits.go A prm hdr ℓ c fuel).map fc).sum ≤
        phiG (max prm.maxArityLog 1) 0 (fun _ => 0) cost (ℓ - c) 0
  | 0, c, _ => by simp [friCommits.go]
  | fuel + 1, c, hc => by
    by_cases hcl : c < ℓ
    · obtain ⟨nxt, hcn, hn, hstep, _, hstop, he⟩ := Udr.Np.go_step A prm hdr ℓ c fuel hcl
      have hnext := aligned_next A prm hdr ℓ c nxt ha (hc hcl) hcn hn hstep hstop
      have harity : nxt - c = min (max prm.maxArityLog 1) (ℓ - c) := by omega
      have ih := go_aligned A prm hdr cost fc ℓ hfc ha fuel nxt (by
        intro hlt
        have : nxt = c + max prm.maxArityLog 1 := by omega
        rw [this]
        exact Nat.dvd_add (hc hcl) (Nat.dvd_refl _))
      have hd := phiG_full (max prm.maxArityLog 1) 0 (fun _ => 0) cost
        (Nat.le_max_right _ _) (ℓ - c) 0 0 (by omega) (by omega) (by omega)
        (Or.inr (Nat.le_refl 0))
      have hf := hfc c (nxt - c) (by omega)
      rw [he, List.map_cons, List.sum_cons]
      rw [← harity] at hd
      have hsub : ℓ - c - (nxt - c) = ℓ - nxt := by omega
      rw [hsub] at hd
      omega
    · rw [go_nil A prm hdr ℓ c (fuel + 1) (by omega)]
      simp

/-- FRI opening bound for an aligned header; no forced commitments are charged. -/
def friAlignedMax (prm : Params) : Nat :=
  phiMaxG (max prm.maxArityLog 1) 0 (fun _ => 0)
    (costD (prm.numChunks * prm.posPerChunk) (prm.logBlowup + prm.finalLog))
    (prm.maxLogLde - prm.logBlowup - prm.finalLog)

theorem friCommits_aligned (A : Air) (prm : Params) (hdr : List Nat) (nq : Nat)
    (h : headerOk A prm hdr = true) (ha : RollAligned A prm hdr) :
    ((friCommits A prm hdr).map (fcostD nq (queryLog A prm hdr))).sum ≤
      phiMaxG (max prm.maxArityLog 1) 0 (fun _ => 0)
        (costD nq (prm.logBlowup + prm.finalLog))
        (prm.maxLogLde - prm.logBlowup - prm.finalLog) := by
  have hq := queryLog_le A prm hdr h
  have hg := go_aligned A prm hdr
    (costD nq (prm.logBlowup + prm.finalLog)) (fcostD nq (queryLog A prm hdr))
    (finalLayer A prm hdr)
    (fun c a hca => fcostD_le nq _ _ _ c a (by unfold finalLayer; omega) hca)
    ha (finalLayer A prm hdr) 0 (fun _ => Nat.dvd_zero _)
  simp only [Nat.sub_zero] at hg
  exact Nat.le_trans hg (phiG_le_phiMaxG _ _ _ _ _ _ (by unfold finalLayer; omega))

theorem fri_open_aligned (A : Air) (prm : Params) (hdr : List Nat) (nq : Nat)
    (h : headerOk A prm hdr = true) (ha : RollAligned A prm hdr) :
    ((schedOracles (friSchedule A prm hdr)).map (openSizeD nq)).sum ≤
      phiMaxG (max prm.maxArityLog 1) 0 (fun _ => 0)
        (costD nq (prm.logBlowup + prm.finalLog))
        (prm.maxLogLde - prm.logBlowup - prm.finalLog) := by
  rw [schedOracles_fri, sum_map_flatMap]
  simp only [openSizeD_friOracleAt]
  have hs := sum_lkSum_le (fun i a => fcostD nq (queryLog A prm hdr) (i, a))
    (List.range (finalLayer A prm hdr)) List.nodup_range (friCommits A prm hdr)
  exact Nat.le_trans hs (friCommits_aligned A prm hdr nq h ha)

/-- Header-free size bound conditional on the honest header's roll-in alignment.
Prefix accounting still includes roll-in messages and challenges. -/
def sizeMaxAligned (A : Air) (prm : Params) : Nat :=
  let nq := prm.numChunks * prm.posPerChunk
  let N := prm.maxLogLde
  prefixMax A prm +
    (4 * rowsMax A prm nq (fun T => T.width) + 64 * dsum nq N) +
    (4 * rowsMax A prm nq (fun T => 8 * T.auxCount prm.auxGroup) + 64 * dsum nq N) +
    (4 * rowsMax A prm nq (fun T => 8 * T.quotCount prm.auxGroup) + 64 * dsum nq N) +
    friAlignedMax prm

theorem sizeBoundD_le_aligned {F K : Type} [Field F] [Field K] [StarkField F K] [DecidableEq F]
    [DecidableEq K] (A : Air) (prm : Params) (hdr : List Nat)
    (h : headerOk A prm hdr = true) (ha : RollAligned A prm hdr) :
    sizeBoundD (Iop.verifier F K A prm) hdr ≤ sizeMaxAligned A prm := by
  show prefixSize (schedule A prm hdr) +
    ((schedOracles (schedule A prm hdr)).map (openSizeD (prm.numChunks * prm.posPerChunk))).sum ≤ _
  rw [schedOracles_schedule]
  simp only [List.cons_append, List.nil_append, List.map_cons, List.sum_cons]
  have hp := prefix_le A prm hdr h
  have h1 := open_layout_leD A prm hdr (prm.numChunks * prm.posPerChunk) h
    (fun T => T.width) (fun L => L.width) (fun _ _ => rfl)
  have h2 := open_layout_leD A prm hdr (prm.numChunks * prm.posPerChunk) h
    (fun T => 8 * T.auxCount prm.auxGroup) (fun L => 8 * L.aux) (fun _ _ => rfl)
  have h3 := open_layout_leD A prm hdr (prm.numChunks * prm.posPerChunk) h
    (fun T => 8 * T.quotCount prm.auxGroup) (fun L => 8 * L.quot) (fun _ _ => rfl)
  have h4 := fri_open_aligned A prm hdr (prm.numChunks * prm.posPerChunk) h ha
  unfold sizeMaxAligned friAlignedMax
  dsimp only at h1 h2 h3 ⊢
  omega

end ZkFormal.Size
