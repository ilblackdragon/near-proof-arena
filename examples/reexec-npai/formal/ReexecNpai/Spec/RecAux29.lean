import ReexecNpai.Spec.RecAux28

/-!
# Record parse: the branch body (`pBranch`), partial correctness
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

section
variable {pub cb pb : Bytes} {rs : List Receipt} {R N o : Nat} {A : List Ent} {K S : List Nat} {m m1 : M}

theorem br_body_wp (hs : RecStart cb pb rs R N o A K S m m1)
    (hk : u8At pb o = 4 ∨ u8At pb o = 5 ∨ u8At pb o = 6) :
    wp P (Inp pub cb pb) pBranch m1 (BodyPost cb pb rs R N o A) := by
  have hlt := hs.olt
  have hpl := hs.plen
  have hpl' := hs.inv.st.plen
  simp only [PMAX] at hpl'
  have hcap := hs.cap
  have hrv := hs.rv
  have hpf := hs.pf
  obtain ⟨g5, g7, g8, g14, g15⟩ := hs.regs
  have hPo : o + 1 ≤ brP pb o := by unfold brP; split <;> omega
  have hge := brEnd_ge pb o
  have hRP : brR pb o = brP pb o + 2 + brHdr pb o := rfl
  have hhdr : brHdr pb o = 1 ∨ brHdr pb o = 37 := by unfold brHdr; split <;> simp
  have hEnd : brEnd pb o = brR pb o + 2 + 32 * brNp pb o + 8 := rfl
  have hr0 : m1.regs 0 = u8At pb o := hs.r0
  rw [pBranch_split', rec_wp_seqs_append _ _ (by simp [brL1]) (by simp)]
  -- brL1
  have L1 : wp P (Inp pub cb pb) (seqs brL1) m1 (fun ma =>
      (u8At pb o = 5 → o + 5 ≤ pb.length) ∧ brP pb o ≤ pb.length ∧
      ma.mem = wr4 m1.mem (AR + 24 * A.length + 20) (brVal pb o) ∧ ma.regs 1 = brVal pb o ∧
      ma.regs 10 = PF + brP pb o ∧ ma.regs 5 = revSum pb A + (if u8At pb o = 5 then leAt pb (o + 1) 4 else 0) ∧
      ma.regs 0 = u8At pb o ∧ ma.regs 7 = m1.regs 7 ∧ ma.regs 8 = A.length ∧ ma.regs 9 = PF + pb.length ∧
      ma.regs 14 = 8 ∧ ma.regs 15 = 1) := by
    by_cases h5 : u8At pb o = 5
    · have hp : brP pb o = o + 5 + leAt pb (o + 1) 4 := by simp [brP, h5]
      refine wp_mono (brL1_val_wp (q := PF + o + 1) (E := PF + pb.length) (e := A.length) (rv := revSum pb A)
        hs.k1 hs.k8 (by rw [hr0, h5]) hs.r10 hpl hs.rE (by omega) g8 hcap g5 hrv) ?_
      rintro ma ⟨c1, c2, a0, a1, a2, a10, a5, a0', a7, a8, a9, a14, a15⟩
      have hrd : rd32 m1 (PF + o + 1) = leAt pb (o + 1) 4 := rd_at hpf rfl (by omega) (by omega)
      rw [hrd] at c2 a10 a5
      refine ⟨fun _ => by omega, by omega, by rw [a0]; simp [brVal, h5]; try omega,
        by rw [a1]; simp [brVal, h5]; try omega,
        by rw [a10, hp]; omega, by rw [a5]; simp [h5], by rw [a0', h5], a7, a8, a9, a14, a15⟩
    · refine wp_of_spec (brL1_nov_twp (k := u8At pb o) (q := PF + o + 1) (e := A.length) (rv := revSum pb A)
        hs.k1 hs.k8 hr0 h5 hs.r10 g8 hcap g5 hrv) ?_
      rintro ma ca ⟨a0, a1, a2, a10, a5, a0', a7, a8, a9, a14, a15, hca⟩
      refine ⟨fun h => absurd h h5, by simp [brP, h5]; omega, by rw [a0]; simp [brVal, h5],
        by rw [a1]; simp [brVal, h5],
        by rw [a10]; simp [brP, h5]; omega, by rw [a5]; simp [h5], a0', a7, a8, by rw [a9, hs.rE], a14, a15⟩
  have hvl := brVal_le pb o
  simp only [PF] at hvl
  refine wp_mono L1 ?_
  rintro ma ⟨v5, hbp, a0, a1, a10, a5, a0', a7, a8, a9, a14, a15⟩
  have hfa : MFrame m1.mem ma.mem := by
    rw [a0]; exact (MFrame.refl _).wr4 _ _ (.inl ⟨by omega, by simp only [AR, SH8, NCAP] at *; omega⟩)
  have hpfa : readMem ma.mem PF pb.length = pb := by
    rw [hfa.readMem (by right; right; simp only [PF, SH8]; omega)]; exact hpf
  -- brL2
  rw [rec_wp_seqs_append _ _ (by simp [brL2]) (by simp)]
  refine wp_mono (brL2_wp (k := u8At pb o) (q := PF + brP pb o) (E := PF + pb.length) (e := A.length)
    a15 a14 a0' a10 hpl a9 (by omega) a8 hcap (by simp only [AR, NCAP, PF]; omega)) ?_
  rintro mb ⟨q3, htag, b0, b3, b10, b0', b1, b5, b7, b8, b9, b14, b15⟩
  have tag : u8At pb (brP pb o + 2) = if u8At pb o = 4 then 1 else 2 := by
    rw [← byte_at hpfa (show PF + brP pb o + 2 = PF + (brP pb o + 2) by omega) (by omega)]; exact htag
  have hex : (readMem ma.mem (PF + brP pb o) 2).leToNat = brEx pb o := rdmProof hpfa (by omega)
  rw [hex] at b3
  have hfb : MFrame m1.mem mb.mem := by
    rw [b0]
    exact (hfa.wr4 _ _ (.inl ⟨by omega, by simp only [AR, SH8, NCAP] at *; omega⟩)).wr4 _ _
      (.inl ⟨by omega, by simp only [AR, SH8, NCAP] at *; omega⟩)
  have hpfb : readMem mb.mem PF pb.length = pb := by
    rw [hfb.readMem (by right; right; simp only [PF, SH8]; omega)]; exact hpf
  have hdb : readMem mb.mem 0 168 = dataSeg := by
    rw [hfb.readMem (by left; simp only [C_KC]; omega)]; exact hs.data
  -- brL3
  rw [wp_seqs_cons (by simp)]
  refine wp_mono (brL3_wp (a := brVal pb o) (pr := PF + brP pb o + 2) b15 b14 (by rw [b1, a1]) b10
    (by simp only [PF] at *; omega)
    (by unfold brVal; split
        · rename_i h5; have := v5 h5; simp only [PF] at *; omega
        · left; rfl)) ?_
  rintro mc ⟨hc3, c0, cr⟩
  have hpfc : readMem mc.mem PF pb.length = pb := by rw [c0]; exact hpfb
  have c0' : mc.regs 0 = brHdr pb o := by rw [cr 0 (by omega) (by omega) (by omega) (by omega), b0']; rfl
  have c3 : mc.regs 3 = brEx pb o := by rw [cr 3 (by omega) (by omega) (by omega) (by omega), b3]
  have c10 : mc.regs 10 = PF + brP pb o + 2 := by rw [cr 10 (by omega) (by omega) (by omega) (by omega), b10]
  have hex16 := leAt2_lt pb (brP pb o)
  have hbm16 := leAt2_lt pb (brR pb o)
  -- brL4a
  rw [rec_wp_seqs_append _ _ (by simp [brL4a]) (by simp)]
  refine wp_mono (brL4a_wp (R := PF + brR pb o) (E := PF + pb.length)
    (by rw [cr 15 (by omega) (by omega) (by omega) (by omega), b15])
    (by rw [cr 14 (by omega) (by omega) (by omega) (by omega), b14])
    (by rw [c10, c0', hRP]; omega) (by simp only [PF] at *; omega) hpl
    (by rw [cr 9 (by omega) (by omega) (by omega) (by omega), b9])
    (by rw [c3]; exact hex16)) ?_
  rintro md ⟨hR2, hland, d0, d1, d2, dr⟩
  have hbm : (readMem mc.mem (PF + brR pb o) 2).leToNat = brBm pb o := rdmProof hpfc (by omega)
  rw [hbm] at d1 hland
  rw [c3] at hland
  have sub := (land_iff _ _ hex16).mp hland
  -- popc16
  rw [wp_seqs_cons (by simp)]
  have dk1 : md.regs 15 = 1 := by
    rw [dr 15 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      cr 15 (by omega) (by omega) (by omega) (by omega), b15]
  have dk8 : md.regs 14 = 8 := by
    rw [dr 14 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      cr 14 (by omega) (by omega) (by omega) (by omega), b14]
  refine wp_of_spec (popc16_spec (d := 6) (s := 1) (a := 4) (b := 11) (c := 12) (by decide) (by decide)
    ⟨dk1, dk8⟩ (by rw [d1]; exact Nat.lt_trans hbm16 (by decide))) ?_
  rintro me ce ⟨e6, e0, er, hce⟩
  rw [d1, popcN_eq] at e6
  have g : ∀ j, j ≠ 1 → j ≠ 2 → j ≠ 4 → j ≠ 6 → j ≠ 11 → j ≠ 12 → j ≠ 13 → me.regs j = mb.regs j := by
    intro j h1 h2 h4 h6 h11 h12 h13
    rw [er j (by simp; omega), dr j h1 h2 h6 h11 h12 h13, cr j h2 h11 h12 h13]
  -- brL4b
  rw [rec_wp_seqs_append _ _ (by simp [brL4b]) (by simp)]
  refine wp_mono (brL4b_wp (e := A.length) (hdr := brHdr pb o) (np := brNp pb o) (pre := PF + brP pb o + 2)
    (R := PF + brR pb o) (ex := brEx pb o) (bm := brBm pb o)
    (rv := revSum pb A + (if u8At pb o = 5 then leAt pb (o + 1) 4 else 0)) (E := PF + pb.length)
    (by rw [g 15 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b15])
    (by rw [g 14 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b14])
    (by rw [g 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b0']; rfl)
    (by rw [e6]; rfl)
    (by rw [g 10 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b10])
    (by rw [er 2 (by simp), d2])
    (by rw [g 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b3])
    (by rw [er 1 (by simp), d1])
    (by rw [g 5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b5, a5])
    (by rw [g 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b8])
    (by rw [g 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), b9])
    hcap (by omega) (popc_le _ _) (by simp only [PF] at *; omega) (by simp only [PF] at *; omega)
    hex16 hbm16 (by
      have h1 := revSum_le hs.inv
      have h2 := hs.inv.ole
      split
      · rename_i h5
        have : brP pb o = o + 5 + leAt pb (o + 1) 4 := by simp [brP, h5]
        omega
      · omega)) ?_
  rintro m4 ⟨hend4, r4⟩
  have hend : brEnd pb o ≤ pb.length := by rw [hEnd, hRP]; simp only [brNp] at *; omega
  -- the value header facts
  have hvv : u8At pb o = 5 → sl pb (brP pb o + 3) 4 = sl pb (o + 1) 4 ∧ sl pb (brP pb o + 7) 32 = zeros 32 := by
    intro h5
    have h37 : brHdr pb o = 37 := by simp [brHdr]; omega
    have hval : brVal pb o = PF + o + 5 := by simp [brVal, h5]
    have hne : brVal pb o ≠ 0 := by rw [hval]; simp only [PF]; omega
    obtain ⟨x1, x2⟩ := hc3 hne
    rw [hval, rm_at hpfb (show PF + brP pb o + 2 + 1 = PF + (brP pb o + 3) by omega) (by omega),
      rm_at hpfb (show PF + o + 5 - 4 = PF + (o + 1) by omega) (by omega)] at x1
    rw [rm_at hpfb (show PF + brP pb o + 2 + 5 = PF + (brP pb o + 7) by omega) (by omega), dZero hdb] at x2
    exact ⟨x1, x2⟩
  have hm := brMid_of hs hk v5 tag sub hend (fun h5 => (hvv h5).1) (fun h5 => (hvv h5).2) a0 a5 a7
    (a9.trans hs.rE.symm) b0 b5 b7 (b9.trans a9.symm) c0 cr d0 dr e0 er r4
  -- the slot loop
  rw [wp_seqs_cons (by simp [brL5])]
  refine wp_mono (br_loop_wp hm.static hm.r14 hm.r15 hm.loop0) ?_
  intro m5 hl
  have hz := (zeroB_iff hm.pf hm.data hend).mpr (fun j hj hb he => hl.chk j (by omega) hj hb he)
  exact wp_of_spec (br_fin hm hz hl) (fun m6 c hp => hp.post)

end

end ReexecNpai
