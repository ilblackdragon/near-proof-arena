import ZkFormal.NearV3.Rcpt.Extract.Srcp.Traffic

/-!
# Source-proof accumulator bytes

The accumulator window is exactly the digest registers loaded at the start of
that window. In particular the leaf segment emits all 32 bytes of its RC digest.
-/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

/-- An accumulator byte is the corresponding register of its window's first row. -/
theorem accumulator_byte {s ℓ o : Nat} (hu : IsU tr tt s ℓ)
    (hH : s + ℓ ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (ho : o < ℓ) (haw : tr.cell tt (s + o) aw = 1) :
    tr.cell tt (s + o) b = tr.cell tt (s + o - o % 32) (reg (o % 32)) := by
  have hsg := (segRows hL hu hH hrt).2.2.2.2.2.2 o ho
  obtain ⟨-, -, -, -, -, -, -, -, hb, -⟩ := local_ hL (r := s + o) (by omega)
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
  obtain ⟨-, -, -, -, -, -, hf, -⟩ := local_ hL (r := s + o) (by omega)
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

end ZkFormal.NearV3.SrcpProof
