import ReexecNpai.Spec.RcptAux2

/-!
# Receipts phase, part 3: list facts and the receipt loop
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore Interp NearSpec NearSpec.TransferV1

namespace RcptProof

theorem cat_append : ∀ (l1 l2 : List NearSpec.Bytes), concatAll (l1 ++ l2) = concatAll l1 ++ concatAll l2
  | [], _ => rfl
  | a :: l1, l2 => by simp [concatAll, cat_append l1 l2]

theorem rOff_snoc {rs : List Receipt} {r : Receipt} {j : Nat} (h : rs.length = j) :
    rOff (rs ++ [r]) (j + 1) = rOff rs j + r.encode.length := by
  subst h
  simp only [rOff]
  rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp)]
  simp [cat_append, concatAll]
  omega

theorem rOff_snoc_le {rs : List Receipt} {r : Receipt} {i : Nat} (h : i ≤ rs.length) :
    rOff (rs ++ [r]) i = rOff rs i := by
  simp [rOff, List.take_append_of_le_length h]

theorem readMany_snoc {α : Type} {p : Parser α} : ∀ (j : Nat) (bs : NearSpec.Bytes) (rs : List α)
    (rest : NearSpec.Bytes) (a : α) (rest' : NearSpec.Bytes),
    readMany p j bs = some (rs, rest) → p rest = some (a, rest') →
    readMany p (j + 1) bs = some (rs ++ [a], rest')
  | 0, bs, rs, rest, a, rest', h1, h2 => by
    simp only [readMany, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simp [readMany, h2]
  | j + 1, bs, rs, rest, a, rest', h1, h2 => by
    simp only [readMany] at h1
    rw [readMany.eq_def]
    split at h1
    · simp at h1
    · rename_i b bs1 hb
      split at h1
      · simp at h1
      · rename_i bs2 rest2 hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        simp only [hb]
        rw [readMany_snoc j bs1 bs2 rest2 a rest' hr h2]
        simp

theorem rtBytes_length (r : Receipt) (A : Nat) : (rtBytes r A).length = 40 := by
  simp [rtBytes, u32, NearSpec.leN_length]

theorem decRcptPos_next {pb : NearSpec.Bytes} {o o' : Nat} {r : Receipt} (h : decRcptPos pb o = some (r, o')) :
    decReceipt (pb.drop o) = some (r, pb.drop o') ∧ o' = o + r.encode.length ∧ o' ≤ pb.length := by
  have hd := decReceipt_pos pb o
  rw [h] at hd
  simp only [Option.map_some] at hd
  obtain ⟨o1, o2, o5, pred, recv, signer, hf, -, rfl⟩ := decRcptPos_inv h
  have hle : o5 + 1 + (32 + 32 * (pb[o5]?.getD 0).toNat) + 45 ≤ pb.length := hf.2.2.2.2.2.2.2.1
  refine ⟨hd, ?_, hle⟩
  have := congrArg List.length (decReceipt_some hd).1
  simp only [List.length_drop, List.length_append] at this
  have ho : o ≤ pb.length := by
    obtain ⟨h1, -⟩ := hf
    have := (borshAt_some h1).1
    omega
  omega

theorem drop_rOff {pb : NearSpec.Bytes} {rs : List Receipt} {T : NearSpec.Bytes}
    (h : pb.drop 4 = concatAll (rs.map Receipt.encode) ++ T) {k : Nat} :
    pb.drop (rOff rs k) = concatAll ((rs.drop k).map Receipt.encode) ++ T := by
  have e : rs = rs.take k ++ rs.drop k := (List.take_append_drop k rs).symm
  rw [e, List.map_append, cat_append, List.append_assoc] at h
  rw [rOff, ← List.drop_drop, h, List.drop_left]

/-- Facts of the state before the receipt loop that the loop keeps. -/
structure LBase (cb pb : NearSpec.Bytes) (ms : M) : Prop extends ClaimIn cb ms where
  proof : readMem ms.mem PF pb.length = pb
  plen : pb.length ≤ PMAX

/-- Receipt-loop invariant after `j` receipts `rs`. -/
structure LInv (cb pb : NearSpec.Bytes) (ms : M) (j : Nat) (rs : List Receipt) (x : M) : Prop where
  len : rs.length = j
  dec : readMany decReceipt j (pb.drop 4) = some (rs, pb.drop (rOff rs j))
  slice : rs.all Receipt.inSlice = true
  oLe : rOff rs j ≤ pb.length
  r10 : x.regs 10 = PF + rOff rs j
  r6 : x.regs 6 = RT + 64 * j
  rt : ∀ i (h : i < rs.length), readMem x.mem (RT + 64 * i) 40 = rtBytes rs[i] (PF + rOff rs i)
  out : ∀ a, a < RT ∨ RT + 64 * j ≤ a → x.mem a = ms.mem a
  fr : Frame [0, 1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 13] ms x

theorem LInv.pre {cb pb : NearSpec.Bytes} {ms x : M} {j : Nat} {rs : List Receipt} (hb : LBase cb pb ms)
    (h9 : ms.regs 9 = PF + pb.length) (hI : LInv cb pb ms j rs x) (hj : j < 256) :
    RcptPre cb pb (rOff rs j) (RT + 64 * j) x := by
  obtain ⟨⟨⟨hk1, hk8, hd⟩, hcl, hs⟩, hpf, hpl⟩ := hb
  have hr : ∀ a n, a + n ≤ RT ∨ OL ≤ a → readMem x.mem a n = readMem ms.mem a n := by
    intro a n han
    exact readMem_congr (fun i hi => hI.out _ (by simp only [RT, OL] at han ⊢; omega))
  refine ⟨⟨⟨by rw [hI.fr 15 (by decide), hk1], by rw [hI.fr 14 (by decide), hk8],
    by rw [hr _ _ (by simp [RT])]; exact hd⟩, by rw [hr _ _ (by simp [RT, CLM])]; exact hcl, hs⟩,
    by rw [hr _ _ (by simp [OL, PF])]; exact hpf, hpl, hI.r10, by rw [hI.fr 9 (by decide), h9], hI.r6,
    by simp only [RT, OL]; omega, hI.oLe⟩

theorem LInv.next {cb pb : NearSpec.Bytes} {ms x x' : M} {j o' : Nat} {rs : List Receipt} {r : Receipt}
    (hI : LInv cb pb ms j rs x) (hpost : RcptPost pb x (RT + 64 * j) (rOff rs j) r o' x')
    (hd : decRcptPos pb (rOff rs j) = some (r, o')) (hin : r.inSlice = true) :
    LInv cb pb ms (j + 1) (rs ++ [r]) x' := by
  obtain ⟨hm, h10, h6, hF⟩ := hpost
  obtain ⟨hdr, ho', hle⟩ := decRcptPos_next hd
  have hro : rOff (rs ++ [r]) (j + 1) = o' := by rw [rOff_snoc hI.len, ho']
  have hlen := hI.len
  refine ⟨by simp [hI.len], ?_, by simp [hI.slice, hin], by rw [hro]; exact hle, by rw [hro, h10],
    by rw [h6]; omega, ?_, ?_, ?_⟩
  · rw [hro]; exact readMany_snoc j _ rs _ r _ hI.dec hdr
  · intro i hi
    simp only [List.length_append, List.length_cons, List.length_nil] at hi
    rw [rOff_snoc_le (by omega), hm]
    by_cases hij : i < rs.length
    · rw [List.getElem_append_left hij, readMem_writeMem_disjoint _ _ _ _ _ _ (by omega), hI.rt i hij]
    · have hi' : i = j := by omega
      subst hi'
      rw [List.getElem_append_right (by omega)]
      simp only [hlen, Nat.sub_self, List.getElem_cons_zero]
      rw [readMem_writeMem_self _ _ _ _ (by simp [rtBytes_length]),
        List.take_of_length_le (by simp [rtBytes_length])]
  · intro a ha
    rw [hm, writeMem_apply_out _ _ _ _ _ (by omega)]
    exact hI.out a (by omega)
  · intro k hk
    rw [hF k (fun h => hk (by simp at h ⊢; omega)), hI.fr k hk]

theorem rOff_le_total (rs : List Receipt) (k : Nat) :
    rOff rs k ≤ 4 + (concatAll (rs.map Receipt.encode)).length := by
  have e : rs = rs.take k ++ rs.drop k := (List.take_append_drop k rs).symm
  have := congrArg (fun l => (concatAll (l.map Receipt.encode)).length) e
  simp only [List.map_append, cat_append, List.length_append] at this
  simp only [rOff]
  omega

theorem rOff_take (rs : List Receipt) (k : Nat) : rOff (rs.take k) k = rOff rs k := by
  simp [rOff, List.take_take]

theorem nth_dec {pb : NearSpec.Bytes} {n R : Nat} {rsA : List Receipt}
    (hdecA : readMany decReceipt n (pb.drop 4) = some (rsA, pb.drop R)) (hR : R ≤ pb.length)
    (h4 : 4 ≤ pb.length) (hsl : rsA.all Receipt.inSlice = true) {j : Nat} (hj : j < rsA.length) :
    decRcptPos pb (rOff rsA j) = some (rsA[j], rOff rsA (j + 1)) ∧ rsA[j].inSlice = true := by
  obtain ⟨hcat, -⟩ := readMany_decReceipt_some hdecA
  have hin : rsA[j].inSlice = true := List.all_eq_true.mp hsl _ (List.getElem_mem hj)
  have hw : rsA[j].wf = true := by
    simp only [Receipt.inSlice, Bool.and_eq_true] at hin; exact hin.1.1
  have d1 := drop_rOff hcat (k := j)
  have d2 := drop_rOff hcat (k := j + 1)
  rw [List.drop_eq_getElem_cons hj, List.map_cons, concatAll, List.append_assoc, ← d2] at d1
  have hdr := decReceipt_pos pb (rOff rsA j)
  rw [d1, decReceipt_encode _ hw] at hdr
  have htot := congrArg List.length hcat
  simp only [List.length_drop, List.length_append] at htot
  have hle := rOff_le_total rsA (j + 1)
  refine ⟨?_, hin⟩
  cases h : decRcptPos pb (rOff rsA j) with
  | none => rw [h] at hdr; simp at hdr
  | some q =>
    obtain ⟨r', o2⟩ := q
    rw [h] at hdr
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hdr
    obtain ⟨rfl, hdd⟩ := hdr
    have h2 := (decRcptPos_next h).2.2
    have := congrArg List.length hdd
    simp only [List.length_drop] at this
    have : o2 = rOff rsA (j + 1) := by omega
    rw [this]

theorem LInv.regs {cb pb : NearSpec.Bytes} {ms x : M} {j : Nat} {rs : List Receipt} (hI : LInv cb pb ms j rs x)
    (v w : Nat) : LInv cb pb ms j rs { x with regs := setReg (setReg x.regs 8 v) 5 w } :=
  ⟨hI.len, hI.dec, hI.slice, hI.oLe, by simp [setReg_apply, hI.r10], by simp [setReg_apply, hI.r6], hI.rt,
    hI.out, AccountIdProof.fsr (by simp) (AccountIdProof.fsr (by simp) hI.fr)⟩

theorem LInv.zero {cb pb : NearSpec.Bytes} {ms : M} (h4 : 4 ≤ pb.length) (h10 : ms.regs 10 = PF + 4)
    (h6 : ms.regs 6 = RT) : LInv cb pb ms 0 [] ms :=
  ⟨rfl, by simp [readMany, rOff, concatAll], rfl, by simp [rOff, concatAll]; omega,
    by simp [rOff, concatAll, h10], by simp [h6], fun i h => by simp at h, fun _ _ => rfl, Frame.refl _ _⟩

section
variable {pub cb pb : NearSpec.Bytes}

theorem loop_wp {ms : M} {n : Nat} (hb : LBase cb pb ms) (h9 : ms.regs 9 = PF + pb.length) (hn : n ≤ 256)
    (h7 : ms.regs 7 = n) (h8 : ms.regs 8 = 0) (h10 : ms.regs 10 = PF + 4) (h6 : ms.regs 6 = RT)
    (h4 : 4 ≤ pb.length) :
    wp P (Inp pub cb pb) (forUp 8 7 5 pReceipt) ms (fun x => ∃ rs, LInv cb pb ms n rs x ∧ x.regs 7 = n) := by
  refine wp_forUp (i := 8) (n := 7) (t := 5) (by decide) (by decide) (by decide)
    (J := fun j x => ∃ rs, LInv cb pb ms j rs x) (N := n) (by omega) ?_ ⟨[], LInv.zero h4 h10 h6⟩ h8 h7 ?_ ?_
  · intro j x v w ⟨rs, hI⟩; exact ⟨rs, hI.regs v w⟩
  · intro j x hj ⟨rs, hI⟩ hi hn'
    refine wp_mono (receipt_wp (hI.pre hb h9 (by omega))) ?_
    rintro x' ⟨r, o', hd, hin, hpost⟩
    have hF := hpost.2.2.2
    exact ⟨⟨_, hI.next hpost hd hin⟩, by rw [hF 8 (by decide), hi], by rw [hF 7 (by decide), hn']⟩
  · intro x ⟨rs, hI⟩ h7'; exact ⟨rs, hI, h7'⟩

theorem loop_twp {ms : M} {n R : Nat} {rsA : List Receipt} (hb : LBase cb pb ms)
    (h9 : ms.regs 9 = PF + pb.length) (hn : n ≤ 256)
    (h7 : ms.regs 7 = n) (h8 : ms.regs 8 = 0) (h10 : ms.regs 10 = PF + 4) (h6 : ms.regs 6 = RT)
    (h4 : 4 ≤ pb.length) (hdecA : readMany decReceipt n (pb.drop 4) = some (rsA, pb.drop R))
    (hR : R ≤ pb.length) (hsl : rsA.all Receipt.inSlice = true) :
    twp P (Inp pub cb pb) (forUp 8 7 5 pReceipt) ms (fun x c => LInv cb pb ms n rsA x ∧ x.regs 7 = n ∧
      c ≤ n * 8504 + 2) := by
  have hlen := (readMany_decReceipt_some hdecA).2
  refine twp_forUp (i := 8) (n := 7) (t := 5) (by decide) (by decide) (by decide)
    (J := fun j x => LInv cb pb ms j (rsA.take j) x) (N := n) (B := 8500) (by omega) ?_
    (LInv.zero h4 h10 h6) h8 h7 ?_ ?_
  · intro j x v w hI; exact hI.regs v w
  · intro j x hj hI hi hn'
    obtain ⟨hd, hin⟩ := nth_dec hdecA hR h4 hsl (j := j) (by omega)
    rw [← rOff_take rsA j, ← rOff_take rsA (j + 1)] at hd
    have hp := hI.pre hb h9 (by omega)
    refine twp_mono (receipt_twp hp hd hin) ?_
    rintro x' c ⟨hpost, hc⟩
    have hF := hpost.2.2.2
    have hI' := hI.next hpost hd hin
    rw [List.take_succ_eq_append_getElem (by omega)]
    exact ⟨hI', by rw [hF 8 (by decide), hi], by rw [hF 7 (by decide), hn'], hc⟩
  · intro x c hI h7' hc
    rw [List.take_of_length_le (by omega)] at hI
    exact ⟨hI, h7', by omega⟩

end

end RcptProof

end ReexecNpai
