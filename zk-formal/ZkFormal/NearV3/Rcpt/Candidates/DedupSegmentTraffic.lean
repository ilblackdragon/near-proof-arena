import ZkFormal.NearV3.Rcpt.Candidates.DedupRootTraffic
namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near SrcpV3
open SrcpProof (regsF regsN regsN_toFp c16 bytesEq toFp_digMsg ofNat_msgId)
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL
theorem segRowT {s ℓ : Nat} (hu : IsU tr tt s ℓ) (hH : s + ℓ ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    {o : Nat} (ho : o < ℓ) {bb : Nat} (hb : bb ≠ B_SIZE) (sd : Bool) :
    rowTraffic DedupTable.interactions tr tt (s + o) pub bb sd =
      (if bb = B_BYTES ∧ sd = true then
        [[(K_SRC : Fp) + (16 : Nat) * tr.cell tt s q, ((o : Nat) : Fp), tr.cell tt (s + o) b]] else []) ++
      (if bb = B_DIGEST ∧ sd = false ∧ o % 32 = 0 ∧ tr.cell tt (s + o) aw = 1 then
        [[tr.cell tt (s + o) cId, tr.cell tt (s + o) cLen] ++ regsF tr tt (s + o)] else []) := by
  obtain ⟨-, -, -, -, -, -, hrows⟩ := segRows hL hu hH hrt
  obtain ⟨hsg, hrt0, -, -, hsc⟩ := hrows o ho
  obtain ⟨hshape, hrow⟩ := segShape hL hu hH hrt
  have hℓ : ℓ ≤ 64 := by rcases hshape with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  obtain ⟨hpw, hwn, hwf, -⟩ := hrow o ho
  obtain ⟨-, -, -, -, -, -, -, -, -, hgD, -⟩ := local_nodup hL (r := s + o) (by omega) (rootless_nodup hL (by omega) hrt0)
  have hq := hsc q (by simp [segConst])
  have hawB := isBool hL (r := s + o) (by omega) (x := aw) (by simp [SrcpProof.bools])
  have z1 : ¬ ((0 : Fp) = 1) := by decide
  have hpos : (32 : Nat) * tr.cell tt (s + o) wn + tr.cell tt (s + o) pw = ((o : Nat) : Fp) := by
    rw [hwn, hpw]
    by_cases h : o < 32
    · rw [if_pos h, Nat.mod_eq_of_lt h]; grind
    · rw [if_neg h, show o % 32 = o - 32 by omega, show o = 32 + (o - 32) by omega, natCast_add]
      simp only [show 32 + (o - 32) - 32 = o - 32 by omega]; grind
  have hgDe : tr.cell tt (s + o) gD = 1 ↔ o % 32 = 0 ∧ tr.cell tt (s + o) aw = 1 := by
    rw [hgD, hrt0, hwf]
    by_cases h : o % 32 = 0
    · rw [if_pos h]
      rcases hawB with h' | h' <;> rw [h'] <;> constructor <;> intro e <;>
        first | exact ⟨h, rfl⟩ | (exfalso; grind) | (exfalso; exact z1 e.2) | grind
    · rw [if_neg h]
      constructor
      · intro e; exfalso; grind
      · intro e; exact absurd e.1 h
  rw [DedupRender.candidate_rowT, hsg, hrt0, hq, hpos]
  simp only [z1, hb, and_false, false_and, and_true, ite_false, List.nil_append, List.append_nil, if_false]
  congr 1
  by_cases hD : bb = B_DIGEST ∧ sd = false
  · by_cases hg : o % 32 = 0 ∧ tr.cell tt (s + o) aw = 1
    · rw [if_pos ⟨hD.1, hD.2, hgDe.2 hg⟩, if_pos ⟨hD.1, hD.2, hg⟩]
    · rw [if_neg (fun h => hg (hgDe.1 h.2.2)), if_neg (fun h => hg h.2.2)]
  · rw [if_neg (fun h => hD ⟨h.1, h.2.1⟩), if_neg (fun h => hD ⟨h.1, h.2.1⟩)]

end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
