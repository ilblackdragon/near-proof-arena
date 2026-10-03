import ReexecNpai.Spec.RcptAux1

/-!
# Receipts phase, part 2: one receipt (`pReceipt`)
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore Interp NearSpec NearSpec.TransferV1

namespace RcptProof

/-- The receipt `decRcptPos` builds from its field offsets. -/
def rcptOf (pb : NearSpec.Bytes) (o2 o5 : Nat) (pred recv signer : NearSpec.Bytes) : Receipt :=
  let t := (pb[o5]?.getD 0).toNat
  let o7 := o5 + 1 + (32 + 32 * t)
  { predecessorId := pred, receiverId := recv, receiptId := sl pb o2 32, signerId := signer,
    signerPk := ⟨t, sl pb (o5 + 1) (32 + 32 * t)⟩, gasPrice := NearSpec.leNat (sl pb o7 16),
    deposit := NearSpec.leNat (sl pb (o7 + 29) 16) }

/-- The checks of `decRcptPos`, in the order the bytecode performs them. -/
def RFacts (pb : NearSpec.Bytes) (o o1 o2 o5 : Nat) (pred recv signer : NearSpec.Bytes) : Prop :=
  borshAt pb o = some (pred, o1) ∧ borshAt pb o1 = some (recv, o2) ∧ o2 + 33 ≤ pb.length ∧
  (pb[o2 + 32]?.getD 0).toNat = 0 ∧ borshAt pb (o2 + 33) = some (signer, o5) ∧ o5 + 1 ≤ pb.length ∧
  (pb[o5]?.getD 0).toNat ≤ 1 ∧ o5 + 1 + (32 + 32 * (pb[o5]?.getD 0).toNat) + 45 ≤ pb.length ∧
  sl pb (o5 + 1 + (32 + 32 * (pb[o5]?.getD 0).toNat) + 16) 13 = receiptMid

theorem decRcptPos_of {pb pred recv signer : NearSpec.Bytes} {o o1 o2 o5 : Nat}
    (h : RFacts pb o o1 o2 o5 pred recv signer) :
    decRcptPos pb o = some (rcptOf pb o2 o5 pred recv signer,
      o5 + 1 + (32 + 32 * (pb[o5]?.getD 0).toNat) + 45) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  simp only [decRcptPos, h1, h2, h5]
  rw [if_pos (by omega), if_pos ⟨h3, h4⟩, if_pos ⟨h6, h7⟩, if_pos (by omega), if_pos (by omega),
    if_pos ⟨by omega, h9⟩, if_pos h8]
  rfl

theorem decRcptPos_inv {pb : NearSpec.Bytes} {o o' : Nat} {r : Receipt} (h : decRcptPos pb o = some (r, o')) :
    ∃ o1 o2 o5 pred recv signer, RFacts pb o o1 o2 o5 pred recv signer ∧
      r = rcptOf pb o2 o5 pred recv signer ∧ o' = o5 + 1 + (32 + 32 * (pb[o5]?.getD 0).toNat) + 45 := by
  unfold decRcptPos at h
  try dsimp only at h
  split at h; · simp at h
  rename_i pred o1 h1
  try dsimp only at h
  split at h; · simp at h
  rename_i recv o2 h2
  try dsimp only at h
  split at h
  case isFalse => simp at h
  rename_i c3
  try dsimp only at h
  split at h
  case isFalse => simp at h
  rename_i c4
  try dsimp only at h
  split at h; · simp at h
  rename_i signer o5 h5
  try dsimp only at h
  split at h
  case isFalse => simp at h
  rename_i c6
  try dsimp only at h
  split at h
  case isFalse => simp at h
  rename_i c7
  try dsimp only at h
  split at h
  case isFalse => simp at h
  rename_i c8
  try dsimp only at h
  split at h
  case isFalse => simp at h
  rename_i c9
  try dsimp only at h
  split at h
  case isFalse => simp at h
  rename_i c10
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨o1, o2, o5, pred, recv, signer, ⟨h1, h2, c4.1, c4.2, h5, c6.1, c6.2, c10, c9.2⟩, rfl, rfl⟩

theorem rt_eq {pb pred recv signer : NearSpec.Bytes} {o o1 o2 o5 : Nat}
    (h : RFacts pb o o1 o2 o5 pred recv signer) :
    [] ++ (Bytes.leN 4 (PF + o + 4) ++ Bytes.leN 4 pred.length) ++
      (Bytes.leN 4 (PF + o1 + 4) ++ Bytes.leN 4 recv.length) ++ Bytes.leN 4 (PF + o2) ++
      (Bytes.leN 4 (PF + (o2 + 33) + 4) ++ Bytes.leN 4 signer.length) ++ Bytes.leN 4 (PF + o5) ++
      Bytes.leN 4 (PF + (o5 + 1 + (32 + 32 * (pb[o5]?.getD 0).toNat))) ++
      Bytes.leN 4 (PF + (o5 + 1 + (32 + 32 * (pb[o5]?.getD 0).toNat) + 29)) =
    rtBytes (rcptOf pb o2 o5 pred recv signer) (PF + o) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hkl : (rcptOf pb o2 o5 pred recv signer).signerPk.data.length =
      32 + 32 * (pb[o5]?.getD 0).toNat := sl_length_of (by omega)
  simp only [rtBytes]
  rw [hkl]
  obtain ⟨-, -, -, -, rfl⟩ := borshAt_some h1
  obtain ⟨-, -, -, -, rfl⟩ := borshAt_some h2
  obtain ⟨-, -, -, -, rfl⟩ := borshAt_some h5
  simp only [rcptOf, u32, ← leN_eq, List.append_assoc, List.nil_append, Nat.add_assoc, Nat.reduceAdd]

theorem valid_bounds {b : NearSpec.Bytes} (h : NearSpec.AccountId.valid b = true) :
    2 ≤ b.length ∧ b.length ≤ 64 := by
  simp only [NearSpec.AccountId.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

/-- Post-state of one receipt. -/
def RcptPost (pb : NearSpec.Bytes) (m : M) (e o : Nat) (r : Receipt) (o' : Nat) (m' : M) : Prop :=
  m'.mem = writeMem m.mem e 40 (rtBytes r (PF + o)) ∧ m'.regs 10 = PF + o' ∧ m'.regs 6 = e + 64 ∧
    Frame [0, 1, 2, 3, 4, 6, 10, 11, 12, 13] m m'

theorem bst0 {cb pb : NearSpec.Bytes} {o e : Nat} {m : M} (hp : RcptPre cb pb o e m) : BSt cb pb m e o [] m :=
  ⟨hp, by funext j; simp [writeMem]; omega, by simp, Frame.refl _ _⟩

section
variable {pub cb pb : NearSpec.Bytes}

theorem receipt_wp {o e : Nat} {m : M} (hp : RcptPre cb pb o e m) :
    wp P (Inp pub cb pb) pReceipt m (fun m' => ∃ r o', decRcptPos pb o = some (r, o') ∧
      r.inSlice = true ∧ RcptPost pb m e o r o' m') := by
  have hs0 := bst0 hp
  simp only [pReceipt, seqs]
  refine field_wp hs0 rfl (by omega) (fun m1 pred o1 hb1 hv1 hs1 h11 h12 hid1 => ?_)
  refine notSys_wp hs1 (idAt_bound hs1 hb1 h11 h12) (fun m2 hns hs2 => ?_)
  refine field_wp hs2 (by simp [Bytes.leN_length]) (by omega) (fun m3 recv o2 hb2 hv2 hs3 h31 h32 hid3 => ?_)
  have hr3 := valid_bounds hv2
  refine namedSeg_wp hs3 (idAt_bound hs3 hb2 h31 h32) (by omega) (by omega) (fun m4 hnm hs4 => ?_)
  refine rid_wp hs4 (by simp [Bytes.leN_length]) (fun m5 h33 hz hs5 => ?_)
  refine field_wp hs5 (by simp [Bytes.leN_length]) (by omega) (fun m6 signer o5 hb5 hv5 hs6 _ _ _ => ?_)
  refine pk_wp hs6 (by simp [Bytes.leN_length]) (fun m7 hb7 ht hkl hs7 => ?_)
  refine mid_wp hs7 (by simp [Bytes.leN_length]) (fun m8 h29 hmid hs8 => ?_)
  refine wp_mono (fin_wp hs8 (by simp [Bytes.leN_length])) ?_
  rintro m9 ⟨h16, hm9, h10, h6, hF⟩
  have hf : RFacts pb o o1 o2 o5 pred recv signer :=
    ⟨hb1, hb2, h33, hz, hb5, hb7, ht, by omega, hmid⟩
  have hdec := decRcptPos_of hf
  refine ⟨_, _, hdec, ?_, ?_, ?_, by rw [h6], hF⟩
  · have hd := decReceipt_pos pb o
    rw [hdec] at hd
    obtain ⟨-, hpk, hrid, hgp, hdep, -⟩ := decReceipt_some hd
    rw [hid1] at hns
    rw [hid3] at hnm
    have e1 : (rcptOf pb o2 o5 pred recv signer).predecessorId = pred := rfl
    have e2 : (rcptOf pb o2 o5 pred recv signer).receiverId = recv := rfl
    have e3 : (rcptOf pb o2 o5 pred recv signer).signerId = signer := rfl
    simp [Receipt.inSlice, Receipt.wf, e1, e2, e3, hv1, hv2, hv5, hpk, hrid, hgp, hdep, hns, hnm]
  · rw [hm9, rt_eq hf]
  · rw [h10]; simp only [PF]; omega

theorem receipt_twp {o e o' : Nat} {m : M} {r : Receipt} (hp : RcptPre cb pb o e m)
    (hdec : decRcptPos pb o = some (r, o')) (hin : r.inSlice = true) :
    twp P (Inp pub cb pb) pReceipt m (fun m' c => RcptPost pb m e o r o' m' ∧ c ≤ 8500) := by
  obtain ⟨o1, o2, o5, pred, recv, signer, hf, rfl, rfl⟩ := decRcptPos_inv hdec
  have hf' := hf
  obtain ⟨hb1, hb2, h33, hz, hb5, hb7, ht, h8, hmid⟩ := hf'
  have e1 : (rcptOf pb o2 o5 pred recv signer).predecessorId = pred := rfl
  have e2 : (rcptOf pb o2 o5 pred recv signer).receiverId = recv := rfl
  have e3 : (rcptOf pb o2 o5 pred recv signer).signerId = signer := rfl
  simp only [Receipt.inSlice, Receipt.wf, e1, e2, e3, Bool.and_eq_true, bne_iff_ne, ne_eq] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hv1, hv2⟩, hv5⟩, -⟩, -⟩, -⟩, -⟩, hns⟩, hnm⟩ := hin
  have hs0 := bst0 hp
  simp only [pReceipt, seqs]
  refine field_twp hs0 rfl (by omega) hb1 hv1 (fun m1 c1 hs1 h11 h12 hid1 hc1 => ?_)
  refine notSys_twp hs1 (idAt_bound hs1 hb1 h11 h12) (by rw [hid1]; exact hns) (fun m2 c2 hs2 hc2 => ?_)
  refine field_twp hs2 (by simp [Bytes.leN_length]) (by omega) hb2 hv2
    (fun m3 c3 hs3 h31 h32 hid3 hc3 => ?_)
  have hr3 := valid_bounds hv2
  refine namedSeg_twp hs3 (idAt_bound hs3 hb2 h31 h32) (by omega) (by omega) (by rw [hid3]; exact hnm)
    (fun m4 c4 hs4 hc4 => ?_)
  refine rid_twp hs4 (by simp [Bytes.leN_length]) h33 hz (fun m5 c5 hs5 hc5 => ?_)
  refine field_twp hs5 (by simp [Bytes.leN_length]) (by omega) hb5 hv5 (fun m6 c6 hs6 _ _ _ hc6 => ?_)
  refine pk_twp hs6 (by simp [Bytes.leN_length]) hb7 ht (by omega) (fun m7 c7 hs7 hc7 => ?_)
  refine mid_twp hs7 (by simp [Bytes.leN_length]) (by omega) hmid (fun m8 c8 hs8 hc8 => ?_)
  refine twp_mono (fin_twp hs8 (by simp [Bytes.leN_length]) (by omega)) ?_
  rintro m9 c9 ⟨⟨hm9, h10, h6, hF⟩, hc9⟩
  refine ⟨⟨by rw [hm9, rt_eq hf], by rw [h10]; simp only [PF]; omega, by rw [h6], hF⟩, by omega⟩

end

end RcptProof

end ReexecNpai
