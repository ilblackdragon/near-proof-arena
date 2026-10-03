import ReexecNpai.Spec.State
import ReexecNpai.Spec.AccountId

/-!
# Receipts phase, part 1: field macros
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore Interp NearSpec NearSpec.TransferV1

theorem leToNat_eq_leNat : ∀ l : NearSpec.Bytes, Bytes.leToNat l = NearSpec.leNat l
  | [] => rfl
  | x :: xs => by simp [Bytes.leToNat, NearSpec.leNat, leToNat_eq_leNat xs]

/-- Reading the proof copy. -/
theorem rdProof {M0 : Nat → UInt8} {pb : NearSpec.Bytes} (h : readMem M0 PF pb.length = pb) {o n : Nat}
    (hn : o + n ≤ pb.length) : readMem M0 (PF + o) n = sl pb o n := by
  apply List.ext_getElem (by simp [sl]; omega)
  intro i h1 h2
  simp only [readMem_length] at h1
  rw [readMem_getElem]
  have := mem_of_readMem h (o + i) (by omega)
  rw [Nat.add_assoc, this]
  simp [sl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show o + i < pb.length by omega)]

/-- What the receipt loop body needs from the current state. -/
structure RcptPre (cb pb : NearSpec.Bytes) (o e : Nat) (m : M) : Prop extends ClaimIn cb m where
  proof : readMem m.mem PF pb.length = pb
  plen : pb.length ≤ PMAX
  rP : m.regs 10 = PF + o
  rE : m.regs 9 = PF + pb.length
  rT : m.regs 6 = e
  he : RT ≤ e ∧ e + 64 ≤ OL
  ho : o ≤ pb.length

theorem borshField_wp {pub cb pb : NearSpec.Bytes} {o e : Nat} {m : M} (hp : RcptPre cb pb o e m) (off : Nat)
    (hoff : off + 8 ≤ 64) :
    wp P (Inp pub cb pb) (pBorshField off) m (fun m' => ∃ b o', borshAt pb o = some (b, o') ∧
      m'.regs 10 = PF + o' ∧ m'.regs 1 = PF + o + 4 ∧ m'.regs 2 = b.length ∧
      m'.mem = writeMem (writeMem m.mem (e + off) 4 (Bytes.leN 4 (PF + o + 4))) (e + off + 4) 4
        (Bytes.leN 4 b.length) ∧ Frame [1, 2, 3, 10, 12, 13] m m') := by
  obtain ⟨⟨⟨hk1, hk8, hd⟩, hcl, hs⟩, hpf, hpl, hP, hE, hT, he, ho⟩ := hp
  simp only [PMAX, RT, OL] at hpl he
  simp only [pBorshField]
  npai_auto [hk1, hk8, hP, hE, hT]
  rename_i h1 h2
  have hL : (readMem m.mem (8844304 + o) 4).leToNat = NearSpec.leNat (sl pb o 4) := by
    rw [show (8844304 : Nat) = PF from rfl, rdProof hpf (by omega), leToNat_eq_leNat]
  rw [hL] at h2 ⊢
  have hlen : (sl pb (o + 4) (NearSpec.leNat (sl pb o 4))).length = NearSpec.leNat (sl pb o 4) :=
    sl_length_of (by omega)
  refine ⟨sl pb (o + 4) (NearSpec.leNat (sl pb o 4)), o + 4 + NearSpec.leNat (sl pb o 4), ?_, by omega,
    hlen.symm, by rw [hlen, Nat.add_assoc, Nat.add_assoc], ?_⟩
  · simp only [borshAt]
    rw [if_pos (by omega), if_pos (by omega)]
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp only [setReg_apply]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hj
    simp [h1, h2, h3, h4, h5, h6, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6]


namespace RcptProof

/-- Frame goals after straight-line code. -/
macro "rcpt_frame_tac" : tactic => `(tactic| repeat (first | exact fun _ _ => rfl | assumption |
  refine AccountIdProof.fsr (by simp) ?_))

theorem fixed_wp {pub cb pb : NearSpec.Bytes} {o e : Nat} {m : M} (hp : RcptPre cb pb o e m) (off w : Nat)
    (hoff : off + 4 ≤ 64) (hw : w ≤ 64) :
    wp P (Inp pub cb pb) (pFixed off w) m (fun m' => o + w ≤ pb.length ∧ m'.regs 10 = PF + o + w ∧
      m'.mem = writeMem m.mem (e + off) 4 (Bytes.leN 4 (PF + o)) ∧ Frame [3, 10, 12, 13] m m') := by
  obtain ⟨⟨⟨hk1, hk8, hd⟩, hcl, hs⟩, hpf, hpl, hP, hE, hT, he, ho⟩ := hp
  simp only [PMAX, RT, OL] at hpl he
  simp only [pFixed]
  npai_auto [hk1, hk8, hP, hE, hT]
  exact ⟨by omega, by rcpt_frame_tac⟩

theorem fixed_twp {pub cb pb : NearSpec.Bytes} {o e : Nat} {m : M} (hp : RcptPre cb pb o e m) (off w : Nat)
    (hoff : off + 4 ≤ 64) (hw : w ≤ 64) (hb : o + w ≤ pb.length) :
    twp P (Inp pub cb pb) (pFixed off w) m (fun m' c => m'.regs 10 = PF + o + w ∧
      m'.mem = writeMem m.mem (e + off) 4 (Bytes.leN 4 (PF + o)) ∧ Frame [3, 10, 12, 13] m m' ∧ c ≤ 20) := by
  obtain ⟨⟨⟨hk1, hk8, hd⟩, hcl, hs⟩, hpf, hpl, hP, hE, hT, he, ho⟩ := hp
  simp only [PMAX, RT, OL] at hpl he
  simp only [pFixed]
  npai_auto [hk1, hk8, hP, hE, hT]
  exact ⟨by omega, by rcpt_frame_tac⟩

theorem borshAt_some {pb b : NearSpec.Bytes} {o o' : Nat} (h : borshAt pb o = some (b, o')) :
    o + 4 ≤ pb.length ∧ o + 4 + NearSpec.leNat (sl pb o 4) ≤ pb.length ∧ b = sl pb (o + 4) b.length ∧
      b.length = NearSpec.leNat (sl pb o 4) ∧ o' = o + 4 + b.length := by
  unfold borshAt at h
  dsimp only at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hl : (sl pb (o + 4) (NearSpec.leNat (sl pb o 4))).length = NearSpec.leNat (sl pb o 4) :=
        sl_length_of (by omega)
      rw [hl]
      exact ⟨by omega, by omega, rfl, rfl, rfl⟩
    · simp at h
  · simp at h

theorem borshField_twp {pub cb pb : NearSpec.Bytes} {o e : Nat} {m : M} (hp : RcptPre cb pb o e m) (off : Nat)
    (hoff : off + 8 ≤ 64) {b : NearSpec.Bytes} {o' : Nat} (hb : borshAt pb o = some (b, o')) :
    twp P (Inp pub cb pb) (pBorshField off) m (fun m' c =>
      m'.regs 10 = PF + o' ∧ m'.regs 1 = PF + o + 4 ∧ m'.regs 2 = b.length ∧
      m'.mem = writeMem (writeMem m.mem (e + off) 4 (Bytes.leN 4 (PF + o + 4))) (e + off + 4) 4
        (Bytes.leN 4 b.length) ∧ Frame [1, 2, 3, 10, 12, 13] m m' ∧ c ≤ 60) := by
  obtain ⟨⟨⟨hk1, hk8, hd⟩, hcl, hs⟩, hpf, hpl, hP, hE, hT, he, ho⟩ := hp
  obtain ⟨h1, h2, -, hbl, rfl⟩ := borshAt_some hb
  simp only [PMAX, RT, OL] at hpl he
  have hL : (readMem m.mem (8844304 + o) 4).leToNat = b.length := by
    rw [show (8844304 : Nat) = PF from rfl, rdProof hpf (by omega), leToNat_eq_leNat, hbl]
  simp only [pBorshField]
  npai_auto [hk1, hk8, hP, hE, hT, hL]
  exact ⟨by omega, by omega, by omega, by simp only [Nat.add_assoc], by rcpt_frame_tac⟩

/-! ## Receipt body state -/

theorem leN_eq : ∀ (w x : Nat), Bytes.leN w x = NearSpec.leN w x
  | 0, _ => rfl
  | w + 1, x => by simp [Bytes.leN, NearSpec.leN, leN_eq w (x / 256)]

theorem writeMem_append (M0 : Nat → UInt8) (a n k : Nat) (L1 L2 : NearSpec.Bytes) (h1 : L1.length = n) :
    writeMem (writeMem M0 a n L1) (a + n) k L2 = writeMem M0 a (n + k) (L1 ++ L2) := by
  funext j
  simp only [writeMem]
  by_cases c1 : a + n ≤ j ∧ j < a + n + k
  · rw [if_pos c1, if_pos ⟨by omega, by omega⟩]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), h1, show j - a - n = j - (a + n) by omega]
  · rw [if_neg c1]
    by_cases c2 : a ≤ j ∧ j < a + n
    · rw [if_pos c2, if_pos ⟨c2.1, by omega⟩]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    · rw [if_neg c2, if_neg (by omega)]

theorem pre_of {cb pb : NearSpec.Bytes} {o e o' : Nat} {m m' : M} (h : RcptPre cb pb o e m)
    (hm : ∀ j, j < RT ∨ OL ≤ j → m'.mem j = m.mem j)
    (h15 : m'.regs 15 = m.regs 15) (h14 : m'.regs 14 = m.regs 14) (h9 : m'.regs 9 = m.regs 9)
    (h6 : m'.regs 6 = m.regs 6) (h10 : m'.regs 10 = PF + o') (ho : o' ≤ pb.length) : RcptPre cb pb o' e m' := by
  obtain ⟨⟨⟨hk1, hk8, hd⟩, hcl, hs⟩, hpf, hpl, hP, hE, hT, he, ho0⟩ := h
  have hr : ∀ a n, a + n ≤ RT ∨ OL ≤ a → readMem m'.mem a n = readMem m.mem a n := by
    intro a n han
    exact readMem_congr (fun i hi => hm _ (by omega))
  refine ⟨⟨⟨by rw [h15, hk1], by rw [h14, hk8], by rw [hr _ _ (by simp [RT])]; exact hd⟩,
    by rw [hr _ _ (by simp [RT, CLM])]; exact hcl, hs⟩, by rw [hr _ _ (by simp [OL, PF])]; exact hpf, hpl,
    h10, by rw [h9, hE], by rw [h6, hT], he, ho⟩

/-- State inside the receipt body: the RT entry at `e` holds the prefix `L`. -/
structure BSt (cb pb : NearSpec.Bytes) (m0 : M) (e o : Nat) (L : NearSpec.Bytes) (m : M) : Prop where
  pre : RcptPre cb pb o e m
  mem : m.mem = writeMem m0.mem e L.length L
  len : L.length ≤ 40
  fr : Frame [0, 1, 2, 3, 4, 10, 11, 12, 13] m0 m

theorem frame_sub {C : List Nat} {m0 m m' : M} (h0 : Frame [0, 1, 2, 3, 4, 10, 11, 12, 13] m0 m)
    (h : Frame C m m') (hC : ∀ j ∈ C, j ∈ [0, 1, 2, 3, 4, 10, 11, 12, 13]) :
    Frame [0, 1, 2, 3, 4, 10, 11, 12, 13] m0 m' :=
  fun j hj => by rw [h j (fun h' => hj (hC j h')), h0 j hj]

theorem frame_regs {C : List Nat} {m m' : M} (h : Frame C m m')
    (hC : ∀ j ∈ C, j ∈ [0, 1, 2, 3, 4, 10, 11, 12, 13]) :
    m'.regs 15 = m.regs 15 ∧ m'.regs 14 = m.regs 14 ∧ m'.regs 9 = m.regs 9 ∧ m'.regs 6 = m.regs 6 :=
  ⟨h 15 (fun h' => by have := hC _ h'; simp at this), h 14 (fun h' => by have := hC _ h'; simp at this),
   h 9 (fun h' => by have := hC _ h'; simp at this), h 6 (fun h' => by have := hC _ h'; simp at this)⟩

/-- A step that writes 4 bytes at the end of the entry prefix. -/
theorem BSt.write {cb pb : NearSpec.Bytes} {m0 m m' : M} {e o o' : Nat} {L X : NearSpec.Bytes} {C : List Nat}
    (h : BSt cb pb m0 e o L m) {k : Nat} (hX : X.length = k) (hL : L.length + k ≤ 40)
    (hm : m'.mem = writeMem m.mem (e + L.length) k X) (hF : Frame C m m')
    (hC : ∀ j ∈ C, j ∈ [0, 1, 2, 3, 4, 10, 11, 12, 13]) (h10 : m'.regs 10 = PF + o') (ho : o' ≤ pb.length) :
    BSt cb pb m0 e o' (L ++ X) m' := by
  obtain ⟨hp, hmem, -, hfr⟩ := h
  obtain ⟨h15, h14, h9, h6⟩ := frame_regs hF hC
  have he := hp.he
  simp only [RT, OL] at he
  refine ⟨pre_of hp (fun j hj => ?_) h15 h14 h9 h6 h10 ho, ?_, by simp; omega, frame_sub hfr hF hC⟩
  · rw [hm]; apply writeMem_apply_out; simp only [RT, OL] at hj; omega
  · rw [hm, hmem, writeMem_append _ _ _ _ _ _ rfl, List.length_append, hX]

/-- A step that does not write memory. -/
theorem BSt.step {cb pb : NearSpec.Bytes} {m0 m m' : M} {e o o' : Nat} {L : NearSpec.Bytes} {C : List Nat}
    (h : BSt cb pb m0 e o L m) (hm : m'.mem = m.mem) (hF : Frame C m m')
    (hC : ∀ j ∈ C, j ∈ [0, 1, 2, 3, 4, 10, 11, 12, 13]) (h10 : m'.regs 10 = PF + o') (ho : o' ≤ pb.length) :
    BSt cb pb m0 e o' L m' := by
  obtain ⟨hp, hmem, hl, hfr⟩ := h
  obtain ⟨h15, h14, h9, h6⟩ := frame_regs hF hC
  exact ⟨pre_of hp (fun j _ => by rw [hm]) h15 h14 h9 h6 h10 ho, by rw [hm, hmem], hl, frame_sub hfr hF hC⟩

theorem idAt_eq {cb pb b : NearSpec.Bytes} {m0 m : M} {e o o' : Nat} {L : NearSpec.Bytes}
    (h : BSt cb pb m0 e o' L m) (hb : borshAt pb o = some (b, o')) (h1 : m.regs 1 = PF + o + 4)
    (h2 : m.regs 2 = b.length) : idAt m = b := by
  obtain ⟨-, -, hbe, -, ho'⟩ := borshAt_some hb
  have := h.pre.ho
  rw [idAt, h1, h2, Nat.add_assoc, rdProof h.pre.proof (by omega), ← hbe]

theorem idAt_bound {cb pb b : NearSpec.Bytes} {m0 m : M} {e o o' : Nat} {L : NearSpec.Bytes}
    (h : BSt cb pb m0 e o' L m) (hb : borshAt pb o = some (b, o')) (h1 : m.regs 1 = PF + o + 4)
    (h2 : m.regs 2 = b.length) : m.regs 1 + m.regs 2 ≤ P.memSize := by
  obtain ⟨-, -, -, -, ho'⟩ := borshAt_some hb
  have := h.pre.plen
  have := h.pre.ho
  simp only [P_memSize, h1, h2, PF, PMAX] at *
  omega

section
variable {pub cb pb : NearSpec.Bytes} {m0 : M} {e : Nat}

theorem field_wp {K : Stmt} {Q : M → Prop} {o : Nat} {L : NearSpec.Bytes} {m : M} {off : Nat}
    (hs : BSt cb pb m0 e o L m) (hL : L.length = off) (hoff : off + 8 ≤ 40)
    (hK : ∀ m' b o', borshAt pb o = some (b, o') → NearSpec.AccountId.valid b = true →
      BSt cb pb m0 e o' (L ++ (Bytes.leN 4 (PF + o + 4) ++ Bytes.leN 4 b.length)) m' →
      m'.regs 1 = PF + o + 4 → m'.regs 2 = b.length → idAt m' = b → wp P (Inp pub cb pb) K m' Q) :
    wp P (Inp pub cb pb) (.seq (pBorshField off) (.seq pValid K)) m Q := by
  subst hL
  rw [wp_seq]
  refine wp_mono (borshField_wp hs.pre L.length (by omega)) ?_
  rintro m1 ⟨b, o', hb, h10, h1, h2, hmem, hF⟩
  obtain ⟨-, hb2, -, hbl, ho'⟩ := borshAt_some hb
  have hs1 : BSt cb pb m0 e o' (L ++ (Bytes.leN 4 (PF + o + 4) ++ Bytes.leN 4 b.length)) m1 :=
    BSt.write hs (by simp [Bytes.leN_length]) (k := 8) (by omega)
      (by rw [hmem, writeMem_append _ _ _ _ _ _ (Bytes.leN_length _ _)]) hF (by decide) h10
      (by omega)
  have hid := idAt_eq hs1 hb h1 h2
  rw [wp_seq]
  refine wp_mono (valid_wp (hF 15 (by decide) ▸ hs.pre.k1) (hF 14 (by decide) ▸ hs.pre.k8)
    (idAt_bound hs1 hb h1 h2)) ?_
  rintro m2 ⟨hv, hm2, hF2⟩
  rw [hid] at hv
  have e1 : m2.regs 1 = m1.regs 1 := hF2 1 (by decide)
  have e2 : m2.regs 2 = m1.regs 2 := hF2 2 (by decide)
  have hs2 := BSt.step hs1 hm2 hF2 (by decide) (by rw [hF2 10 (by decide), h10]) hs1.pre.ho
  exact hK m2 b o' hb hv hs2 (by rw [e1, h1]) (by rw [e2, h2])
    (by rw [idAt, e1, e2, hm2]; exact hid)

theorem field_twp {K : Stmt} {Q : M → Nat → Prop} {o : Nat} {L : NearSpec.Bytes} {m : M} {off : Nat}
    (hs : BSt cb pb m0 e o L m) (hL : L.length = off) (hoff : off + 8 ≤ 40) {b : NearSpec.Bytes} {o' : Nat}
    (hb : borshAt pb o = some (b, o')) (hv : NearSpec.AccountId.valid b = true)
    (hK : ∀ m' c, BSt cb pb m0 e o' (L ++ (Bytes.leN 4 (PF + o + 4) ++ Bytes.leN 4 b.length)) m' →
      m'.regs 1 = PF + o + 4 → m'.regs 2 = b.length → idAt m' = b → c ≤ 2060 →
      twp P (Inp pub cb pb) K m' (fun m2 c2 => Q m2 (c + c2))) :
    twp P (Inp pub cb pb) (.seq (pBorshField off) (.seq pValid K)) m Q := by
  subst hL
  obtain ⟨-, hb2, -, hbl, ho'⟩ := borshAt_some hb
  rw [twp_seq]
  refine twp_mono (borshField_twp hs.pre L.length (by omega) hb) ?_
  rintro m1 c1 ⟨h10, h1, h2, hmem, hF, hc1⟩
  have hs1 : BSt cb pb m0 e o' (L ++ (Bytes.leN 4 (PF + o + 4) ++ Bytes.leN 4 b.length)) m1 :=
    BSt.write hs (by simp [Bytes.leN_length]) (k := 8) (by omega)
      (by rw [hmem, writeMem_append _ _ _ _ _ _ (Bytes.leN_length _ _)]) hF (by decide) h10 (by omega)
  have hid := idAt_eq hs1 hb h1 h2
  rw [twp_seq]
  refine twp_mono (valid_twp (hF 15 (by decide) ▸ hs.pre.k1) (hF 14 (by decide) ▸ hs.pre.k8)
    (idAt_bound hs1 hb h1 h2) (hid ▸ hv)) ?_
  rintro m2 c2 ⟨hm2, hF2, hc2⟩
  have e1 : m2.regs 1 = m1.regs 1 := hF2 1 (by decide)
  have e2 : m2.regs 2 = m1.regs 2 := hF2 2 (by decide)
  have hs2 := BSt.step hs1 hm2 hF2 (by decide) (by rw [hF2 10 (by decide), h10]) hs1.pre.ho
  refine twp_mono (hK m2 (c1 + c2) hs2 (by rw [e1, h1]) (by rw [e2, h2])
    (by rw [idAt, e1, e2, hm2]; exact hid) (by omega)) ?_
  intro m3 c3 h
  rwa [Nat.add_assoc] at h

theorem readMem_slice {M0 : Nat → UInt8} {a n : Nat} {l : NearSpec.Bytes} (h : readMem M0 a n = l) (k j : Nat)
    (hkj : k + j ≤ n) : readMem M0 (a + k) j = (l.drop k).take j := by
  subst h
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp [readMem, Nat.add_assoc]

theorem sys_data {M0 : Nat → UInt8} (h : readMem M0 0 168 = dataSeg) :
    readMem M0 D_SYS 6 = NearSpec.AccountId.system := by
  have := readMem_slice h 80 6 (by omega)
  rw [Nat.zero_add] at this
  rw [D_SYS, this]
  decide

theorem mid_data {M0 : Nat → UInt8} (h : readMem M0 0 168 = dataSeg) :
    readMem M0 D_MID 13 = receiptMid := by
  have := readMem_slice h 88 13 (by omega)
  rw [Nat.zero_add] at this
  rw [D_MID, this]
  decide

theorem g_data {M0 : Nat → UInt8} (h : readMem M0 0 168 = dataSeg) :
    readMem M0 D_G 8 = NearSpec.u64 Params.G := by
  have := readMem_slice h 120 8 (by omega)
  rw [Nat.zero_add] at this
  rw [D_G, this]
  decide

theorem notSys_wp {K : Stmt} {Q : M → Prop} {o : Nat} {L : NearSpec.Bytes} {m : M}
    (hs : BSt cb pb m0 e o L m) (hb : m.regs 1 + m.regs 2 ≤ P.memSize)
    (hK : ∀ m', idAt m ≠ NearSpec.AccountId.system → BSt cb pb m0 e o L m' → wp P (Inp pub cb pb) K m' Q) :
    wp P (Inp pub cb pb) (.seq pNotSystem K) m Q := by
  rw [wp_seq]
  refine wp_mono (notSystem_wp hs.pre.k1 hs.pre.k8 hb (sys_data hs.pre.data)) ?_
  rintro m1 ⟨hn, hm, hF⟩
  exact hK m1 hn (BSt.step hs hm hF (by decide) (by rw [hF 10 (by decide), hs.pre.rP]) hs.pre.ho)

theorem notSys_twp {K : Stmt} {Q : M → Nat → Prop} {o : Nat} {L : NearSpec.Bytes} {m : M}
    (hs : BSt cb pb m0 e o L m) (hb : m.regs 1 + m.regs 2 ≤ P.memSize)
    (hn : idAt m ≠ NearSpec.AccountId.system)
    (hK : ∀ m' c, BSt cb pb m0 e o L m' → c ≤ 20 → twp P (Inp pub cb pb) K m' (fun m2 c2 => Q m2 (c + c2))) :
    twp P (Inp pub cb pb) (.seq pNotSystem K) m Q := by
  rw [twp_seq]
  refine twp_mono (notSystem_twp hs.pre.k1 hs.pre.k8 hb (sys_data hs.pre.data) hn) ?_
  rintro m1 c1 ⟨hm, hF, hc⟩
  exact hK m1 c1 (BSt.step hs hm hF (by decide) (by rw [hF 10 (by decide), hs.pre.rP]) hs.pre.ho) hc

theorem namedSeg_wp {K : Stmt} {Q : M → Prop} {o : Nat} {L : NearSpec.Bytes} {m : M}
    (hs : BSt cb pb m0 e o L m) (hb : m.regs 1 + m.regs 2 ≤ P.memSize) (h2 : 2 ≤ m.regs 2)
    (h64 : m.regs 2 ≤ 64)
    (hK : ∀ m', NearSpec.AccountId.isNamed (idAt m) = true → BSt cb pb m0 e o L m' →
      wp P (Inp pub cb pb) K m' Q) :
    wp P (Inp pub cb pb) (.seq pNamed K) m Q := by
  rw [wp_seq]
  refine wp_mono (named_wp hs.pre.k1 hs.pre.k8 hb h2 h64) ?_
  rintro m1 ⟨hn, hm, hF⟩
  exact hK m1 hn (BSt.step hs hm hF (by decide) (by rw [hF 10 (by decide), hs.pre.rP]) hs.pre.ho)

theorem namedSeg_twp {K : Stmt} {Q : M → Nat → Prop} {o : Nat} {L : NearSpec.Bytes} {m : M}
    (hs : BSt cb pb m0 e o L m) (hb : m.regs 1 + m.regs 2 ≤ P.memSize) (h2 : 2 ≤ m.regs 2)
    (h64 : m.regs 2 ≤ 64) (hn : NearSpec.AccountId.isNamed (idAt m) = true)
    (hK : ∀ m' c, BSt cb pb m0 e o L m' → c ≤ 2000 →
      twp P (Inp pub cb pb) K m' (fun m2 c2 => Q m2 (c + c2))) :
    twp P (Inp pub cb pb) (.seq pNamed K) m Q := by
  rw [twp_seq]
  refine twp_mono (named_twp hs.pre.k1 hs.pre.k8 hb h2 h64 hn) ?_
  rintro m1 c1 ⟨hm, hF, hc⟩
  exact hK m1 c1 (BSt.step hs hm hF (by decide) (by rw [hF 10 (by decide), hs.pre.rP]) hs.pre.ho) hc

theorem pbyte {M0 : Nat → UInt8} {pb : NearSpec.Bytes} (h : readMem M0 PF pb.length = pb) {i : Nat}
    (hi : i < pb.length) : M0 (PF + i) = pb[i]?.getD 0 := by
  rw [mem_of_readMem h i hi, List.getD_eq_getElem?_getD]

theorem rid_wp {K : Stmt} {Q : M → Prop} {o : Nat} {L : NearSpec.Bytes} {m : M}
    (hs : BSt cb pb m0 e o L m) (hL : L.length = 16)
    (hK : ∀ m', o + 33 ≤ pb.length → (pb[o + 32]?.getD 0).toNat = 0 →
      BSt cb pb m0 e (o + 33) (L ++ Bytes.leN 4 (PF + o)) m' → wp P (Inp pub cb pb) K m' Q) :
    wp P (Inp pub cb pb) (.seq (pFixed 16 32) (.seq (need 10 1 9) (.seq (LD8 3 10) (.seq (assertZ 3)
      (.seq (ADDI 10 10 1) K))))) m Q := by
  rw [wp_seq]
  refine wp_mono (fixed_wp hs.pre 16 32 (by omega) (by omega)) ?_
  rintro m1 ⟨hb, h10, hmem, hF⟩
  have hs1 : BSt cb pb m0 e (o + 32) (L ++ Bytes.leN 4 (PF + o)) m1 :=
    BSt.write hs (Bytes.leN_length _ _) (by omega) (by rw [hmem, hL]) hF (by decide) h10 hb
  have h9 := hs1.pre.rE
  have hpl := hs1.pre.plen
  simp only [PF, PMAX] at h10 h9 hpl
  have hby := pbyte hs1.pre.proof (i := o + 32)
  simp only [PF] at hby
  simp only [wp_seq]
  generalize wp P (Inp pub cb pb) K = W at hK ⊢
  npai_auto [h10, h9]
  rename_i hc1 hc2 heq h3
  subst heq
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at h3
  refine hK _ (by omega) ?_ (BSt.step hs1 rfl (C := [3, 10, 12, 13]) ?_ (by decide) ?_ (by omega))
  · rw [← hby (by omega), ← Nat.add_assoc]; exact h3
  · rcpt_frame_tac
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, h10, PF, wordMod]; omega

theorem rid_twp {K : Stmt} {Q : M → Nat → Prop} {o : Nat} {L : NearSpec.Bytes} {m : M}
    (hs : BSt cb pb m0 e o L m) (hL : L.length = 16) (hb33 : o + 33 ≤ pb.length)
    (hz : (pb[o + 32]?.getD 0).toNat = 0)
    (hK : ∀ m' c, BSt cb pb m0 e (o + 33) (L ++ Bytes.leN 4 (PF + o)) m' → c ≤ 40 →
      twp P (Inp pub cb pb) K m' (fun m2 c2 => Q m2 (c + c2))) :
    twp P (Inp pub cb pb) (.seq (pFixed 16 32) (.seq (need 10 1 9) (.seq (LD8 3 10) (.seq (assertZ 3)
      (.seq (ADDI 10 10 1) K))))) m Q := by
  rw [twp_seq]
  refine twp_mono (fixed_twp hs.pre 16 32 (by omega) (by omega) (by omega)) ?_
  rintro m1 c1 ⟨h10, hmem, hF, hc1⟩
  have hs1 : BSt cb pb m0 e (o + 32) (L ++ Bytes.leN 4 (PF + o)) m1 :=
    BSt.write hs (Bytes.leN_length _ _) (by omega) (by rw [hmem, hL]) hF (by decide) h10 (by omega)
  have h9 := hs1.pre.rE
  have hpl := hs1.pre.plen
  have hz' : (m1.mem (8844304 + o + 32)).toNat = 0 := by
    rw [Nat.add_assoc, show (8844304 : Nat) = PF from rfl, pbyte hs1.pre.proof (by omega)]; exact hz
  simp only [PF, PMAX] at h10 h9 hpl
  simp only [twp_seq]
  generalize twp P (Inp pub cb pb) K = W at hK ⊢
  npai_auto [h10, h9, hz']
  refine ⟨by omega, by omega, ?_⟩
  have e : ∀ c2, c1 + (4 + (1 + (2 + (1 + c2)))) = c1 + 8 + c2 := by intro; omega
  simp only [e]
  refine hK _ _ (BSt.step hs1 rfl (C := [3, 10, 12, 13]) ?_ (by decide) ?_ (by omega)) (by omega)
  · rcpt_frame_tac
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, PF]; omega

theorem forall_cond_eq {α : Sort _} {c : Prop} {x : α} {P : α → Prop} :
    (∀ a, c → x = a → P a) ↔ (c → P x) :=
  ⟨fun h hc => h x hc rfl, fun h a hc e => e ▸ h hc⟩

theorem W_congr {W : M → (M → Nat → Prop) → Prop} {Q : M → Nat → Prop} {x : M} (f g : Nat → Nat)
    (h : ∀ c, f c = g c) (hw : W x (fun m2 c2 => Q m2 (f c2))) : W x (fun m2 c2 => Q m2 (g c2)) := by
  have : f = g := funext h
  subst this; exact hw

theorem evShl5 (x : Nat) (h : x ≤ 1) : BinOp.shl.eval x 5 = x * 32 := by
  rw [eval_shl x 5 (by omega) (by unfold wordMod; rw [show (2:Nat) ^ 5 = 32 from rfl]; omega)]

theorem pk_wp {K : Stmt} {Q : M → Prop} {o : Nat} {L : NearSpec.Bytes} {m : M}
    (hs : BSt cb pb m0 e o L m) (hL : L.length = 28)
    (hK : ∀ m', o + 1 ≤ pb.length → (pb[o]?.getD 0).toNat ≤ 1 →
      o + 1 + (32 + 32 * (pb[o]?.getD 0).toNat) ≤ pb.length →
      BSt cb pb m0 e (o + 1 + (32 + 32 * (pb[o]?.getD 0).toNat)) (L ++ Bytes.leN 4 (PF + o)) m' →
      wp P (Inp pub cb pb) K m' Q) :
    wp P (Inp pub cb pb) (.seq (need 10 1 9) (.seq (ADDI 3 6 28) (.seq (st32 3 10) (.seq (LD8 2 10)
      (.seq (ADDI 10 10 1) (.seq (CST 3 1) (.seq (le 2 3) (.seq (CST 3 5) (.seq (SHL 2 2 3)
      (.seq (ADDI 2 2 32) (.seq (ADD 3 10 2) (.seq (le 3 9) (.seq (ADD 10 10 2) K))))))))))))) m Q := by
  have h10 := hs.pre.rP
  have h9 := hs.pre.rE
  have h6 := hs.pre.rT
  have hk8 := hs.pre.k8
  have hpl := hs.pre.plen
  have he := hs.pre.he
  have ho := hs.pre.ho
  have hby := pbyte hs.pre.proof (i := o)
  simp only [PF, PMAX, RT, OL] at h10 h9 hpl hby he
  simp only [wp_seq]
  generalize wp P (Inp pub cb pb) K = W at hK ⊢
  have hw : writeMem m.mem (e + 28) 4 (Bytes.leN 4 (8844304 + o)) (8844304 + o) = m.mem (8844304 + o) :=
    writeMem_apply_out _ _ _ _ _ (by omega)
  npai_auto [h10, h9, h6, hk8, evShl5, hw, forall_cond_eq]
  rename_i c1 c2 c3 c4
  have hx : m.mem (8844304 + o) = pb[o]?.getD 0 := hby (by omega)
  rw [hx] at c3 c4 ⊢
  refine hK _ (by omega) (by omega) (by omega)
    (BSt.write hs (Bytes.leN_length _ _) (by omega) (by rw [hL]; rfl) (C := [2, 3, 10, 12, 13]) ?_ (by decide) ?_
      (by omega))
  · rcpt_frame_tac
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, PF]; omega

theorem pk_twp {K : Stmt} {Q : M → Nat → Prop} {o : Nat} {L : NearSpec.Bytes} {m : M}
    (hs : BSt cb pb m0 e o L m) (hL : L.length = 28) (hb1 : o + 1 ≤ pb.length)
    (ht : (pb[o]?.getD 0).toNat ≤ 1) (hkl : o + 1 + (32 + 32 * (pb[o]?.getD 0).toNat) ≤ pb.length)
    (hK : ∀ m' c,
      BSt cb pb m0 e (o + 1 + (32 + 32 * (pb[o]?.getD 0).toNat)) (L ++ Bytes.leN 4 (PF + o)) m' → c ≤ 40 →
      twp P (Inp pub cb pb) K m' (fun m2 c2 => Q m2 (c + c2))) :
    twp P (Inp pub cb pb) (.seq (need 10 1 9) (.seq (ADDI 3 6 28) (.seq (st32 3 10) (.seq (LD8 2 10)
      (.seq (ADDI 10 10 1) (.seq (CST 3 1) (.seq (le 2 3) (.seq (CST 3 5) (.seq (SHL 2 2 3)
      (.seq (ADDI 2 2 32) (.seq (ADD 3 10 2) (.seq (le 3 9) (.seq (ADD 10 10 2) K))))))))))))) m Q := by
  have h10 := hs.pre.rP
  have h9 := hs.pre.rE
  have h6 := hs.pre.rT
  have hk8 := hs.pre.k8
  have hpl := hs.pre.plen
  have he := hs.pre.he
  have ho := hs.pre.ho
  have hx : m.mem (8844304 + o) = pb[o]?.getD 0 := pbyte hs.pre.proof (by omega)
  simp only [PF, PMAX, RT, OL] at h10 h9 hpl he
  have hw : writeMem m.mem (e + 28) 4 (Bytes.leN 4 (8844304 + o)) (8844304 + o) = m.mem (8844304 + o) :=
    writeMem_apply_out _ _ _ _ _ (by omega)
  simp only [twp_seq]
  generalize twp P (Inp pub cb pb) K = W at hK ⊢
  npai_auto [h10, h9, h6, hk8, evShl5, hw, forall_cond_eq, hx]
  refine ⟨by omega, by omega, by omega, ?_⟩
  refine W_congr (fun c2 => 30 + c2) _ ?_ (hK _ 30 (BSt.write hs (Bytes.leN_length _ _) (by omega)
    (by rw [hL]; rfl) (C := [2, 3, 10, 12, 13]) ?_ (by decide) ?_ hkl) (by omega))
  · intro c; omega
  · rcpt_frame_tac
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, PF]; omega

theorem mid_wp {K : Stmt} {Q : M → Prop} {o : Nat} {L : NearSpec.Bytes} {m : M}
    (hs : BSt cb pb m0 e o L m) (hL : L.length = 32)
    (hK : ∀ m', o + 29 ≤ pb.length → sl pb (o + 16) 13 = receiptMid →
      BSt cb pb m0 e (o + 29) (L ++ Bytes.leN 4 (PF + o)) m' → wp P (Inp pub cb pb) K m' Q) :
    wp P (Inp pub cb pb) (.seq (pFixed 32 16) (.seq (need 10 13 9) (.seq (CST 3 D_MID) (.seq (CST 4 13)
      (.seq (MEMEQ 2 10 3 4) (.seq (assert 2) (.seq (ADDI 10 10 13) K))))))) m Q := by
  rw [wp_seq]
  refine wp_mono (fixed_wp hs.pre 32 16 (by omega) (by omega)) ?_
  rintro m1 ⟨hb, h10, hmem, hF⟩
  have hs1 : BSt cb pb m0 e (o + 16) (L ++ Bytes.leN 4 (PF + o)) m1 :=
    BSt.write hs (Bytes.leN_length _ _) (by omega) (by rw [hmem, hL]) hF (by decide) h10 hb
  have h9 := hs1.pre.rE
  have hpl := hs1.pre.plen
  have hr1 : o + 29 ≤ pb.length → readMem m1.mem (8844304 + o + 16) 13 = sl pb (o + 16) 13 := fun h =>
    by rw [Nat.add_assoc]; exact rdProof hs1.pre.proof (by omega)
  have hr2 : readMem m1.mem 88 13 = receiptMid := mid_data hs1.pre.data
  simp only [PF, PMAX] at h10 h9 hpl
  simp only [wp_seq]
  generalize wp P (Inp pub cb pb) K = W at hK ⊢
  npai_auto [h10, h9, hr1, hr2, forall_cond_eq]
  rename_i c1 c2 c3
  refine hK _ (by omega) c3 (BSt.step hs1 rfl (C := [2, 3, 4, 10, 12, 13]) ?_ (by decide) ?_ (by omega))
  · rcpt_frame_tac
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, PF]; omega

theorem mid_twp {K : Stmt} {Q : M → Nat → Prop} {o : Nat} {L : NearSpec.Bytes} {m : M}
    (hs : BSt cb pb m0 e o L m) (hL : L.length = 32) (hb29 : o + 29 ≤ pb.length)
    (hmid : sl pb (o + 16) 13 = receiptMid)
    (hK : ∀ m' c, BSt cb pb m0 e (o + 29) (L ++ Bytes.leN 4 (PF + o)) m' → c ≤ 40 →
      twp P (Inp pub cb pb) K m' (fun m2 c2 => Q m2 (c + c2))) :
    twp P (Inp pub cb pb) (.seq (pFixed 32 16) (.seq (need 10 13 9) (.seq (CST 3 D_MID) (.seq (CST 4 13)
      (.seq (MEMEQ 2 10 3 4) (.seq (assert 2) (.seq (ADDI 10 10 13) K))))))) m Q := by
  rw [twp_seq]
  refine twp_mono (fixed_twp hs.pre 32 16 (by omega) (by omega) (by omega)) ?_
  rintro m1 c1 ⟨h10, hmem, hF, hc1⟩
  have hs1 : BSt cb pb m0 e (o + 16) (L ++ Bytes.leN 4 (PF + o)) m1 :=
    BSt.write hs (Bytes.leN_length _ _) (by omega) (by rw [hmem, hL]) hF (by decide) h10 (by omega)
  have h9 := hs1.pre.rE
  have hpl := hs1.pre.plen
  have hr1 : readMem m1.mem (8844304 + o + 16) 13 = sl pb (o + 16) 13 := by
    rw [Nat.add_assoc]; exact rdProof hs1.pre.proof (by omega)
  have hr2 : readMem m1.mem 88 13 = receiptMid := mid_data hs1.pre.data
  simp only [PF, PMAX] at h10 h9 hpl
  simp only [twp_seq]
  generalize twp P (Inp pub cb pb) K = W at hK ⊢
  npai_auto [h10, h9, hr1, hr2, hmid, forall_cond_eq]
  refine ⟨by omega, by omega, ?_⟩
  refine W_congr (fun c2 => (c1 + 11) + c2) _ ?_ (hK _ (c1 + 11) (BSt.step hs1 rfl (C := [2, 3, 4, 10, 12, 13])
    ?_ (by decide) ?_ (by omega)) (by omega))
  · intro c; omega
  · rcpt_frame_tac
  · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, PF]; omega

/-- Post-state of one receipt body. -/
def FinPost (m0 : M) (e : Nat) (L : NearSpec.Bytes) (o : Nat) (m' : M) : Prop :=
  m'.mem = writeMem m0.mem e 40 (L ++ Bytes.leN 4 (PF + o)) ∧ m'.regs 10 = PF + o + 16 ∧
    m'.regs 6 = e + 64 ∧ Frame [0, 1, 2, 3, 4, 6, 10, 11, 12, 13] m0 m'

theorem fin_post {o : Nat} {L : NearSpec.Bytes} {m m1 : M} (hs : BSt cb pb m0 e o L m) (hL : L.length = 36)
    (h10 : m1.regs 10 = PF + o + 16) (hmem : m1.mem = writeMem m.mem (e + 36) 4 (Bytes.leN 4 (PF + o)))
    (hF : Frame [3, 10, 12, 13] m m1) :
    FinPost m0 e L o { m1 with regs := setReg m1.regs 6 ((m1.regs 6 + 64) % wordMod) } := by
  have h6 : m1.regs 6 = e := by rw [hF 6 (by decide)]; exact hs.pre.rT
  have he := hs.pre.he
  simp only [RT, OL] at he
  refine ⟨?_, by simp [setReg_apply, h10], by simp [setReg_apply, h6, wordMod]; omega, ?_⟩
  · simp only
    rw [hmem, hs.mem, hL, writeMem_append _ _ _ _ _ _ hL]
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp only [setReg_apply, if_neg hj.2.2.2.2.2.1]
    rw [hF j (by simp [hj.2.2.2.1, hj.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.2.2])]
    exact hs.fr j (by simp [hj.1, hj.2.1, hj.2.2.1, hj.2.2.2.1, hj.2.2.2.2.1, hj.2.2.2.2.2.2.1,
      hj.2.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.2.1, hj.2.2.2.2.2.2.2.2.2])

theorem fin_wp {o : Nat} {L : NearSpec.Bytes} {m : M} (hs : BSt cb pb m0 e o L m) (hL : L.length = 36) :
    wp P (Inp pub cb pb) (.seq (pFixed 36 16) (ADDI 6 6 64)) m (fun m' =>
      o + 16 ≤ pb.length ∧ FinPost m0 e L o m') := by
  rw [wp_seq]
  refine wp_mono (fixed_wp hs.pre 36 16 (by omega) (by omega)) ?_
  rintro m1 ⟨hb, h10, hmem, hF⟩
  rw [wp_op]
  intro _ m2 h2
  simp only [ins, Option.some.injEq] at h2
  subst h2
  exact ⟨hb, fin_post hs hL h10 hmem hF⟩

theorem fin_twp {o : Nat} {L : NearSpec.Bytes} {m : M} (hs : BSt cb pb m0 e o L m) (hL : L.length = 36)
    (hb : o + 16 ≤ pb.length) :
    twp P (Inp pub cb pb) (.seq (pFixed 36 16) (ADDI 6 6 64)) m (fun m' c => FinPost m0 e L o m' ∧ c ≤ 25) := by
  rw [twp_seq]
  refine twp_mono (fixed_twp hs.pre 36 16 (by omega) (by omega) hb) ?_
  rintro m1 c1 ⟨h10, hmem, hF, hc1⟩
  rw [twp_op]
  exact ⟨rfl, _, rfl, fin_post hs hL h10 hmem hF, by simp only [cost]; omega⟩

end

end RcptProof

end ReexecNpai
