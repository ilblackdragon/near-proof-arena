import ZkFormal.NearV3.Rcpt.Candidates.DedupSegmentTraffic

/-!
# Source-proof accumulator bytes

The accumulator window is exactly the digest registers loaded at the start of
that window. In particular the leaf segment emits all 32 bytes of its RC digest.
-/

namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

open SrcpProof (regsN regsF)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL

/-- An accumulator byte is the corresponding register of its window's first row. -/
theorem accumulator_byte {s ℓ o : Nat} (hu : IsU tr tt s ℓ)
    (hH : s + ℓ ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (ho : o < ℓ) (haw : tr.cell tt (s + o) aw = 1) :
    tr.cell tt (s + o) b = tr.cell tt (s + o - o % 32) (reg (o % 32)) := by
  have hsg := (segRows hL hu hH hrt).2.2.2.2.2.2 o ho
  obtain ⟨-, -, -, -, -, -, -, -, hb, -⟩ := local_nodup hL (r := s + o) (by omega) (segment_nodup hL (by omega) hsg.1)
  rw [hb hsg.1 haw]
  simpa using ((segShape hL hu hH hrt).2 o ho).2.2.2 0 (by omega)

/-- Every leaf byte comes from the RC digest loaded on the first row. -/
theorem leaf_byte {s ℓ o : Nat} (hu : IsU tr tt s ℓ)
    (hH : s + ℓ ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 1) (ho : o < ℓ) :
    tr.cell tt (s + o) b = tr.cell tt s (reg o) := by
  have hshape := (segShape hL hu hH hrt).1
  have h32 : ℓ = 32 := by
    rcases hshape with h | h
    · exact h.2
    · rw [hlf] at h; exact False.elim (by simpa using h.1)
  have hrows := (segRows hL hu hH hrt).2.2.2.2.2.2 o ho
  have hlf' : tr.cell tt (s + o) lf = 1 := by
    rw [hrows.2.2.2.2 lf (by simp [segConst]), hlf]
  obtain ⟨-, -, -, -, -, -, hf, -⟩ := local_nodup hL (r := s + o) (by omega) (segment_nodup hL (by omega) hrows.1)
  rw [accumulator_byte hL hu hH hrt ho (hf hlf').2.2.1,
    Nat.mod_eq_of_lt (by omega : o < 32), show s + o - o = s by omega]

/-- Leaf extraction preserves the entire digest, including byte order. -/
theorem leaf_bytes {s ℓ : Nat} (hu : IsU tr tt s ℓ)
    (hH : s + ℓ ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 1) :
    (List.range ℓ).map (fun o => (tr.cell tt (s + o) b).toNat) = regsN tr tt s := by
  have h32 : ℓ = 32 := by
    rcases (segShape hL hu hH hrt).1 with h | h
    · exact h.2
    · rw [hlf] at h; exact False.elim (by simpa using h.1)
  unfold regsN
  rw [← h32]
  apply List.map_congr_left
  intro o ho
  rw [leaf_byte hL hu hH hrt hlf (List.mem_range.mp ho)]

/-- The direction bit selects the accumulator window: first for right siblings,
second for left siblings, exactly as `rootFromPath` concatenates its inputs. -/
theorem path_accumulator_byte {s ℓ o : Nat} (hu : IsU tr tt s ℓ)
    (hH : s + ℓ ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 0) (d : Bool)
    (hd : tr.cell tt s dir = (if d then 1 else 0)) (ho : o < 32) :
    tr.cell tt (s + (if d then 0 else 32) + o) b =
      tr.cell tt (s + (if d then 0 else 32)) (reg o) := by
  have h64 : ℓ = 64 := by
    rcases (segShape hL hu hH hrt).1 with h | h
    · rw [hlf] at h; exact False.elim (by simpa using h.1)
    · exact h.2
  let w : Nat := if d then 0 else 32
  have hw : w = 0 ∨ w = 32 := by cases d <;> simp [w]
  have hwo : w + o < ℓ := by rcases hw with hw | hw <;> omega
  have hrows := (segRows hL hu hH hrt).2.2.2.2.2.2 (w + o) hwo
  have hlf' : tr.cell tt (s + (w + o)) lf = 0 := by
    rw [hrows.2.2.2.2 lf (by simp [segConst]), hlf]
  have hd' : tr.cell tt (s + (w + o)) dir = (if d then 1 else 0) := by
    rw [hrows.2.2.2.2 dir (by simp [segConst]), hd]
  obtain ⟨-, -, -, -, -, -, -, haw, -⟩ := local_nodup hL (r := s + (w + o)) (by omega) (segment_nodup hL (by omega) hrows.1)
  have haw1 : tr.cell tt (s + (w + o)) aw = 1 := by
    rw [haw hrows.1, hlf', hd', ((segShape hL hu hH hrt).2 (w + o) hwo).2.1]
    cases d <;> simp [w, ho] <;> grind
  have hmod : (w + o) % 32 = o := by rcases hw with hw | hw <;> omega
  have he := accumulator_byte hL hu hH hrt hwo haw1
  rw [hmod, show s + (w + o) - o = s + w by omega] at he
  simpa only [Nat.add_assoc] using he

/-- All 32 accumulator bytes preserve the digest order in either path direction. -/
theorem path_accumulator_bytes {s ℓ : Nat} (hu : IsU tr tt s ℓ)
    (hH : s + ℓ ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 0) (d : Bool)
    (hd : tr.cell tt s dir = (if d then 1 else 0)) :
    (List.range 32).map (fun o =>
      (tr.cell tt (s + (if d then 0 else 32) + o) b).toNat) =
      regsN tr tt (s + (if d then 0 else 32)) := by
  unfold regsN
  apply List.map_congr_left
  intro o ho
  rw [path_accumulator_byte hL hu hH hrt hlf d hd (List.mem_range.mp ho)]

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
