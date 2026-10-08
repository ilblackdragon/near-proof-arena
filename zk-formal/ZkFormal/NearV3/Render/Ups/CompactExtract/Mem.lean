import ZkFormal.NearV3.Render.Ups.CompactExtract.MemRows
import ZkFormal.NearV3.Render.Ups.CompactExtract.Walk
import ZkFormal.NearV3.Extract.Ups.Mem
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- **The `MEM` field of a part** `(o, ℓ)` with fields `fl`: rows `r0 … r0+7`,
`r0 = o + fl[last].1`. -/
theorem memOf {o ℓ : Nat} {fl : List (Nat × Nat)} {w : Nat} (U : UPartL s o ℓ fl w) :
    let r0 := o + (fl[fl.length - 1]'(by have := U.nonempty; omega)).1
    r0 + 8 = o + ℓ ∧ (∀ i, i < 8 → s.row (r0 + i) sMEM = 1 ∧ s.row (r0 + i) idx = i) ∧
    ((∀ i, i < 8 → inA (s.row (r0 + i)) < 67108864 ∧ inB (s.row (r0 + i)) < 67108864 ∧
        inC (s.row (r0 + i)) < 67108864 ∧ inE (s.row (r0 + i)) < 67108864 ∧ s.row (r0 + i) b < 256) →
      limbs (fun i => s.row (r0 + i) rx) 8 =
        limbs (fun i => inE (s.row (r0 + i))) 8 +
          (limbs (fun i => inA (s.row (r0 + i))) 8 + limbs (fun i => inB (s.row (r0 + i))) 8 -
            limbs (fun i => inC (s.row (r0 + i))) 8) ∧
      (∀ i, i < 7 → s.row (r0 + i) rx = s.row (r0 + i) b) ∧
      limbs (fun i => s.row (r0 + i) b) 8 = limbs (fun i => s.row (r0 + i) rx) 8 % 2 ^ 64) := by
  intro r0
  have hn := U.nonempty
  have hq : fl.length - 1 < fl.length := by omega
  have hrows := U.rows
  have hq' := fun d (hd : d < ℓ) => (⟨(hrows d hd).1, (hrows d hd).2.2.1, (hrows d hd).2.2.2.1⟩ :
    s.row (o + d) qb = 1 ∧ (s.row (o + d) pf = 1 ↔ d = 0) ∧ (s.row (o + d) pl = 1 ↔ d + 1 = ℓ))
  have hpc := fun d (hd : d < ℓ) => (hrows d hd).2.2.2.2
  have ml := (memLast hw hs U.pos U.le hq' hpc U.consec U.cover U.nonempty U.fields hq).2 (by omega)
  have hlen := fLen hw hs U.pos U.le hq' hpc U.consec U.cover U.nonempty U.fields hq
  rw [ml] at hlen
  have hlast := segEnd_last fl 0 U.consec hn
  rw [U.cover] at hlast
  have hF := (U.fields _ hq).1
  have hlen8 : (fl[fl.length - 1]'hq).2 = 8 := by rw [hlen]; rfl
  have hend : r0 + 8 = o + ℓ := by simp only [r0]; omega
  have hm := lenLe hw hs
  have hle := U.le
  -- the eight rows
  have st : ∀ i, i < 8 → s.row (r0 + i) sMEM = 1 ∧ s.row (r0 + i) idx = i ∧
      (s.row (r0 + i) fs = if i = 0 then 1 else 0) ∧ (s.row (r0 + i) fe = if i = 7 then 1 else 0) ∧
      s.row (r0 + i) neg = s.row o neg ∧ r0 + i < s.rows.length := by
    intro i hi
    have hlt : r0 + i < s.rows.length := by omega
    have hqb : s.row (r0 + i) qb = 1 := by
      have := (hq' (r0 + i - o) (by omega)).1; rwa [show o + (r0 + i - o) = r0 + i by omega] at this
    have hoh := oneHot hw hs hlt hqb
    have sti := hF.st i (by omega)
    have e8 : stOf (s.row (r0 + i)) = 8 := by
      have := ml
      unfold stOf at this ⊢
      simp only [r0] at sti ⊢
      rw [sti sHPL (by simp [states]), sti sHPF (by simp [states]), sti sKEY (by simp [states]),
        sti sVLEN (by simp [states]), sti sVH (by simp [states]), sti sBM (by simp [states]),
        sti sCH (by simp [states]), sti sMEM (by simp [states])]
      exact this
    have bfs := le1 (rowBool (okRow hw hs hlt) (rowLt hw hs _) (x := fs) (by decide))
    have bfe := le1 (rowBool (okRow hw hs hlt) (rowLt hw hs _) (x := fe) (by decide))
    have hfs : (s.row (r0 + i) fs = 1 ↔ i = 0) := hF.fs i (by omega)
    have hfe : (s.row (r0 + i) fe = 1 ↔ i + 1 = (fl[fl.length - 1]'hq).2) := hF.fe i (by omega)
    refine ⟨(stOf_inv hoh).2.2.2.2.2.2.2.2 e8, hF.idx i (by omega), ?_, ?_, ?_, hlt⟩
    · split
      · next h => exact hfs.2 h
      · next h => rcases (show s.row (r0 + i) fs = 0 ∨ s.row (r0 + i) fs = 1 by omega) with h' | h'
                  · exact h'
                  · exact absurd (hfs.1 h') h
    · split
      · next h => exact hfe.2 (by omega)
      · next h => rcases (show s.row (r0 + i) fe = 0 ∨ s.row (r0 + i) fe = 1 by omega) with h' | h'
                  · exact h'
                  · exact absurd (hfe.1 h') (by omega)
    · have := hpc (r0 + i - o) (by omega) neg (by decide)
      rwa [show o + (r0 + i - o) = r0 + i by omega] at this
  refine ⟨hend, fun i hi => ⟨(st i hi).1, (st i hi).2.1⟩, fun hB => ?_⟩
  have hng : s.row o neg ≤ 1 := by
    have h0 := (hq' 0 U.pos)
    rw [Nat.add_zero] at h0
    exact partBoolN (okRow hw hs (by omega)) (rowLt hw hs _) (h0.2.1.2 rfl) (x := neg) (by decide)
  have MR : ∀ i, i < 8 → MemRowF (s.row (r0 + i)) (s.next (r0 + i)) := fun i hi =>
    memRow (okRow hw hs (st i hi).2.2.2.2.2) (rowLt hw hs _) (nextLt hw hs _) (st i hi).1
      (by rw [(st i hi).2.2.2.2.1]; exact hng) (by rw [(st i hi).2.2.2.1]; split <;> omega)
  have hcell : ∀ i x, s.row (r0 + i) x < 2013265921 := fun i x => by have := rowLt hw hs (r0 + i) x; rwa [P_lit] at this
  exact memChain (fun i => s.row (r0 + i)) (s.next (r0 + 7)) (s.row o neg) hng
    (fun i hi => by
      have := MR i (by omega)
      rw [compactNext (s:=s) (by have := (st (i + 1) (by omega)).2.2.2.2.2; omega)] at this
      rwa [show r0 + i + 1 = r0 + (i + 1) from by omega] at this)
    (MR 7 (by omega)) (fun i hi => (st i hi).2.2.1) (fun i hi => (st i hi).2.2.2.1) (fun i hi => (st i hi).2.2.2.2.1)
    hcell (fun i hi => (hB i hi).1) (fun i hi => (hB i hi).2.1) (fun i hi => (hB i hi).2.2.1)
    (fun i hi => (hB i hi).2.2.2.1) (fun i hi => (hB i hi).2.2.2.2)

end

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
  {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s ps fls ws)
include hw hs hL

/-- **`memory_usage` of part `k`** (layer 2). -/
theorem ups_mem (k : Nat) (hk : k < ps.length) :
    ∃ r0, r0 + 8 = ps[k].1 + ps[k].2 ∧ (∀ i, i < 8 → s.row (r0 + i) sMEM = 1 ∧ s.row (r0 + i) idx = i) ∧
    ((∀ i, i < 8 → inA (s.row (r0 + i)) < 67108864 ∧ inB (s.row (r0 + i)) < 67108864 ∧
        inC (s.row (r0 + i)) < 67108864 ∧ inE (s.row (r0 + i)) < 67108864 ∧ s.row (r0 + i) b < 256) →
      limbs (fun i => s.row (r0 + i) rx) 8 =
        limbs (fun i => inE (s.row (r0 + i))) 8 +
          (limbs (fun i => inA (s.row (r0 + i))) 8 + limbs (fun i => inB (s.row (r0 + i))) 8 -
            limbs (fun i => inC (s.row (r0 + i))) 8) ∧
      (∀ i, i < 7 → s.row (r0 + i) rx = s.row (r0 + i) b) ∧
      limbs (fun i => s.row (r0 + i) b) 8 = limbs (fun i => s.row (r0 + i) rx) 8 % 2 ^ 64) := by
  obtain ⟨-, U⟩ := hL.part k hk
  exact ⟨_, memOf hw hs U⟩

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
