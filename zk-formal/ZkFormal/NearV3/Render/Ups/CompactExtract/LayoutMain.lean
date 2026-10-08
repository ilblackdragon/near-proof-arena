import ZkFormal.NearV3.Render.Ups.CompactExtract.Shape
import ZkFormal.NearV3.Render.Ups.CompactExtract.MsgRows
import ZkFormal.NearV3.Extract.Ups.LayoutMain
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
structure UpsLayout (s : UpsSeg) (ps : List (Nat × Nat)) (fls : List (List (Nat × Nat)))
    (ws : List Nat) : Prop where
  walk : 4 < s.rows.length ∧ s.row 0 sf = 1 ∧ s.row 1 wt1 = 1 ∧ s.row 2 wt2 = 1 ∧ s.row 3 wt3 = 1
  wk : ∀ i, i < 4 → s.row i wk = 1
  segc : ∀ i, i < s.rows.length → ∀ x ∈ segConst, s.row i x = s.row 0 x
  consec : Consec (4) ps
  cover : segEnd (4) ps = s.rows.length
  nonempty : 0 < ps.length
  lens : fls.length = ps.length ∧ ws.length = ps.length
  part : ∀ k (hk : k < ps.length), s.row ps[k].1 j = k + 1 ∧
    UPartL s ps[k].1 ps[k].2 (fls[k]'(by omega)) (ws[k]'(by omega))
  /-- the messages of every row, by its kind -/
  msgsW : ∀ i, i < 4 → ∀ bb sd, uMsgs (s.row i) (s.next i) bb sd =
      (if B_MIDROOT = bb ∧ false = sd then (if s.row i sf = 1 then [[s.row i tau, s.row i rootRid] ++ regN (s.row i)] else []) else []) ++
      (if B_ROOT = bb ∧ true = sd then
        (if s.row i wt3 = 1 then [[(s.row i tau + 1) % P] ++ regN (s.row i)] else []) else []) ++
      (if B_DIGEST = bb ∧ false = sd then
        (if s.row i wt3 = 1 then [[s.row i dI, s.row i dL] ++ regN (s.row i)] else []) else []) ++
      (if B_S0F = bb ∧ true = sd then
        (if s.row i sf = 1 then [[s.row i tau, s.row i pres, s.row i vid]] else []) else []) ++
      (if B_SPLEN = bb ∧ false = sd then
        (if s.row i sf = 1 then [[s.row i tau, (s.row i L0 + 256 * s.row i L1 + 65536 * s.row i L2) % P]] else [])
        else []) ++
      (if B_EDGE = bb ∧ false = sd then (if s.row i mS + s.row i mK = 1 then
        [[s.row i nN, s.row i nI, s.row i nib, s.row i nN2, s.row i nI2, s.row i ek, s.row i u]] else []) else []) ++
      (if B_EDGE = bb ∧ true = sd then (if s.row i mS + s.row i mK = 1 then
        [[s.row i nN, s.row i nI, s.row i nib, s.row i nN2, s.row i nI2, s.row i ek, (s.row i u + 1) % P]] else [])
        else []) ++
      (if B_BMAP = bb ∧ false = sd then
        (if s.row i mB = 1 then [[s.row i nN, s.row i wbm, s.row i hv, s.row i u]] else []) else []) ++
      (if B_BMAP = bb ∧ true = sd then
        (if s.row i mB = 1 then [[s.row i nN, s.row i wbm, s.row i hv, (s.row i u + 1) % P]] else []) else [])
  msgsQ : ∀ i, 4 ≤ i → i < s.rows.length → ∀ bb sd, uMsgs (s.row i) (s.next i) bb sd =
      (let C := s.row i
       (if B_DIGEST = bb ∧ false = sd then
         (if C gD = 1 then [[C dI, C dL] ++ (List.range 32).map (fun i => C (reg i))] else []) else []) ++
       (if B_BYTES = bb ∧ true = sd then [[upsIdN (C tau) (C j), C qpos, C b]] else []) ++
       (if B_UPB = bb ∧ false = sd then (if C rd = 1 then [upbN C (C u)] else []) else []) ++
       (if B_UPB = bb ∧ true = sd then (if C rd = 1 then [upbN C ((C u + 1) % P)] else []) else []) ++
       (if B_MEMD = bb ∧ true = sd then
         (if C gMs = 1 then [[C tau, C j, C idx, C rx, C rb, C qlen]] else []) else []) ++
       (if B_MEMD = bb ∧ false = sd then
         (if C gMr = 1 then [[C tau, C jm, C idx, C mBv, C mCv, C clen]] else []) else []))

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

theorem wkOf {i : Nat} (hi : i < s.rows.length)
    (h : s.row i sf = 1 ∨ s.row i wt1 = 1 ∨ s.row i wt2 = 1 ∨ s.row i wt3 = 1) : s.row i wk = 1 := by
  have K := kinds (okRow hw hs hi) (rowLt hw hs _) (nextLt hw hs _)
  obtain ⟨-, -, hwk, -, -, -, -, -, -, bwk, -⟩ := K
  rcases bwk with h0 | h0
  · rcases h with h | h | h | h <;> omega
  · exact h0

attribute [local irreducible] UpsSeg.row UpsSeg.next

theorem ups_layout_seg : ∃ ps fls ws, UpsLayout s ps fls ws := by
  obtain ⟨ps, hLm, hc, hcov, hpos, hpart⟩ := nodeParts hw hs
  obtain ⟨h4, hsf, hw1, hw2, hw3, -, -⟩ := walkRows hw hs
  -- each part: its fields and shape
  have hP : ∀ k (hk : k < ps.length), ∃ fl w, UPartL s ps[k].1 ps[k].2 fl w := by
    intro k hk
    obtain ⟨hℓ, -, hr⟩ := hpart k hk
    have hle := consec_mem_lt ps (4) hc k hk
    rw [hcov] at hle
    have hq := fun d (hd : d < ps[k].2) => (⟨(hr d hd).1, (hr d hd).2.2.1, (hr d hd).2.2.2.1⟩ :
      s.row (ps[k].1 + d) qb = 1 ∧ (s.row (ps[k].1 + d) pf = 1 ↔ d = 0) ∧ (s.row (ps[k].1 + d) pl = 1 ↔ d + 1 = ps[k].2))
    have hpc := fun d (hd : d < ps[k].2) => (hr d hd).2.2.2.2
    obtain ⟨fl, fc, fcov, fpos, fF⟩ := partFields hw hs hℓ hle.2 hq
    obtain ⟨w, wsh, wwin⟩ := partShape hw hs hℓ hle.2 hq hpc fc fcov fpos fF
    exact ⟨fl, w, ⟨hℓ, hle.2, hr, fc, fcov, fpos, fF, wsh, wwin⟩⟩
  let F : Nat → List (Nat × Nat) × Nat := fun k =>
    if hk : k < ps.length then
      (Classical.choose (hP k hk), Classical.choose (Classical.choose_spec (hP k hk))) else ([], 0)
  have hF : ∀ k (hk : k < ps.length), UPartL s ps[k].1 ps[k].2 (F k).1 (F k).2 := by
    intro k hk
    simp only [F, dif_pos hk]
    exact Classical.choose_spec (Classical.choose_spec (hP k hk))
  refine ⟨ps, (List.range ps.length).map (fun k => (F k).1), (List.range ps.length).map (fun k => (F k).2),
    ⟨⟨h4, hsf, hw1, hw2, hw3⟩, ?_, fun i hi x hx => segConstAll hw hs hi hx, hc, hcov, hpos,
      by simp, fun k hk => ⟨(hpart k hk).2.1, by simpa using hF k hk⟩, ?_, ?_⟩⟩
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    · exact wkOf hw hs (by omega) (Or.inl hsf)
    · exact wkOf hw hs (by omega) (Or.inr (Or.inl hw1))
    · exact wkOf hw hs (by omega) (Or.inr (Or.inr (Or.inl hw2)))
    · exact wkOf hw hs (by omega) (Or.inr (Or.inr (Or.inr hw3)))
  · intro i hi bb sd
    have hwk : s.row i wk = 1 := by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
      · exact wkOf hw hs (by omega) (Or.inl hsf)
      · exact wkOf hw hs (by omega) (Or.inr (Or.inl hw1))
      · exact wkOf hw hs (by omega) (Or.inr (Or.inr (Or.inl hw2)))
      · exact wkOf hw hs (by omega) (Or.inr (Or.inr (Or.inr hw3)))
    exact msgsW (okRow hw hs (i := i) (by omega)) (rowLt hw hs _) (nextLt hw hs _) hwk bb sd
  · intro i hi1 hi2 bb sd
    have hq : s.row i qb = 1 := by
      have h0 := ((hpart 0 hpos).2.2 0 (hpart 0 hpos).1).1
      rw [Nat.add_zero, consec_head ps (4) hc hpos] at h0
      have := qbRun hw hs h0 (i - (4)) (by omega)
      rwa [show 4 + (i - (4)) = i by omega] at this
    exact msgsQ (okRow hw hs (i := i) hi2) (rowLt hw hs _) (nextLt hw hs _) hq bb sd

end

/-- **Layer 2**: every segment of a well-formed `upsV3` view has a layout. -/
theorem ups_layout {v : List UpsSeg} (hw : Wf v) : ∀ s ∈ v, ∃ ps fls ws, UpsLayout s ps fls ws :=
  fun _ hs => ups_layout_seg hw hs

end ZkFormal.NearV3.Render.UpsRelay.Extract
