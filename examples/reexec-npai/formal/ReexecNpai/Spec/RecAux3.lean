import ReexecNpai.Spec.RecAux2

/-!
# Record parse: memory and sequencing lemmas
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-! ## Sequencing -/

section
variable {p : Program} {inp : Inputs}

theorem wp_seqs_cons {a : Stmt} {l : List Stmt} (hl : l ≠ []) {m : M} {Q : M → Prop} :
    wp p inp (seqs (a :: l)) m Q ↔ wp p inp a m (fun m1 => wp p inp (seqs l) m1 Q) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b l => simp only [seqs, wp_seq]

theorem twp_seqs_cons {a : Stmt} {l : List Stmt} (hl : l ≠ []) {m : M} {Q : M → Nat → Prop} :
    twp p inp (seqs (a :: l)) m Q ↔
      twp p inp a m (fun m1 c1 => twp p inp (seqs l) m1 (fun m2 c2 => Q m2 (c1 + c2))) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b l => simp only [seqs, twp_seq]

theorem rec_wp_seqs_append : ∀ (l1 l2 : List Stmt), l1 ≠ [] → l2 ≠ [] → ∀ {m : M} {Q : M → Prop},
    wp p inp (seqs (l1 ++ l2)) m Q ↔ wp p inp (seqs l1) m (fun m1 => wp p inp (seqs l2) m1 Q)
  | [], _, h, _, _, _ => absurd rfl h
  | [a], l2, _, h2, m, Q => by
    simp only [List.cons_append, List.nil_append]
    rw [wp_seqs_cons h2]; rfl
  | a :: b :: l, l2, _, h2, m, Q => by
    simp only [List.cons_append]
    rw [wp_seqs_cons (by simp), wp_seqs_cons (by simp)]
    constructor
    · intro h; refine wp_mono h ?_; intro m1 h1
      rw [← List.cons_append] at h1
      exact (rec_wp_seqs_append (b :: l) l2 (by simp) h2).mp h1
    · intro h; refine wp_mono h ?_; intro m1 h1
      rw [← List.cons_append]
      exact (rec_wp_seqs_append (b :: l) l2 (by simp) h2).mpr h1

theorem rec_twp_seqs_append : ∀ (l1 l2 : List Stmt), l1 ≠ [] → l2 ≠ [] → ∀ {m : M} {Q : M → Nat → Prop},
    twp p inp (seqs (l1 ++ l2)) m Q ↔
      twp p inp (seqs l1) m (fun m1 c1 => twp p inp (seqs l2) m1 (fun m2 c2 => Q m2 (c1 + c2)))
  | [], _, h, _, _, _ => absurd rfl h
  | [a], l2, _, h2, m, Q => by
    simp only [List.cons_append, List.nil_append]
    rw [twp_seqs_cons h2]; rfl
  | a :: b :: l, l2, _, h2, m, Q => by
    simp only [List.cons_append]
    rw [twp_seqs_cons (by simp), twp_seqs_cons (by simp)]
    constructor
    · intro h; refine twp_mono h ?_; intro m1 c1 h1
      rw [← List.cons_append] at h1
      have := (rec_twp_seqs_append (b :: l) l2 (by simp) h2).mp h1
      refine twp_mono this ?_; intro m2 c2 h2'
      refine twp_mono h2' ?_; intro m3 c3 h3
      rwa [Nat.add_assoc]
    · intro h; refine twp_mono h ?_; intro m1 c1 h1
      rw [← List.cons_append]
      apply (rec_twp_seqs_append (b :: l) l2 (by simp) h2).mpr
      refine twp_mono h1 ?_; intro m2 c2 h2'
      refine twp_mono h2' ?_; intro m3 c3 h3
      rwa [← Nat.add_assoc]

end

/-! ## Memory -/

/-- `u32` at address `a` of a raw memory. -/
def rdm (M0 : Nat → UInt8) (a : Nat) : Nat := ArenaCore.Bytes.leToNat (readMem M0 a 4)

/-- 4-byte store. -/
def wr4 (M0 : Nat → UInt8) (a v : Nat) : Nat → UInt8 := writeMem M0 a 4 (ArenaCore.Bytes.leN 4 v)

theorem rd32_eq (m : M) (a : Nat) : rd32 m a = rdm m.mem a := rfl

theorem rdm_wr4_same (M0 : Nat → UInt8) (a v : Nat) (h : v < 4294967296) : rdm (wr4 M0 a v) a = v := by
  unfold rdm wr4
  rw [readMem_writeMem_self _ _ _ _ (by simp [ArenaCore.Bytes.leN_length]),
    List.take_of_length_le (by simp [ArenaCore.Bytes.leN_length])]
  exact leToNat_leN 4 v (by simpa using h)

theorem rdm_wr4_other (M0 : Nat → UInt8) (a v b : Nat) (h : b + 4 ≤ a ∨ a + 4 ≤ b) :
    rdm (wr4 M0 a v) b = rdm M0 b := by
  unfold rdm wr4; rw [readMem_writeMem_disjoint _ _ _ _ _ _ h]

theorem readMem_wr4_other (M0 : Nat → UInt8) (a v b n : Nat) (h : b + n ≤ a ∨ a + 4 ≤ b) :
    readMem (wr4 M0 a v) b n = readMem M0 b n := by
  unfold wr4; rw [readMem_writeMem_disjoint _ _ _ _ _ _ h]

theorem wr4_apply_out (M0 : Nat → UInt8) (a v x : Nat) (h : x < a ∨ a + 4 ≤ x) : wr4 M0 a v x = M0 x := by
  unfold wr4; exact writeMem_apply_out _ _ _ _ _ h

/-- Memory outside the arena/child-list/stack regions and the `C_KC` cell is unchanged. -/
def MFrame (M0 M1 : Nat → UInt8) : Prop :=
  ∀ x, (x < AR ∧ (x < C_KC ∨ C_KC + 4 ≤ x)) ∨ SH8 ≤ x → M1 x = M0 x

theorem MFrame.refl (M0 : Nat → UInt8) : MFrame M0 M0 := fun _ _ => rfl

theorem MFrame.trans {M0 M1 M2 : Nat → UInt8} (h1 : MFrame M0 M1) (h2 : MFrame M1 M2) : MFrame M0 M2 :=
  fun x hx => by rw [h2 x hx, h1 x hx]

theorem MFrame.wr4 {M0 M1 : Nat → UInt8} (h : MFrame M0 M1) (a v : Nat)
    (ha : (AR ≤ a ∧ a + 4 ≤ SH8) ∨ a = C_KC) : MFrame M0 (wr4 M1 a v) := by
  intro x hx
  rw [wr4_apply_out _ _ _ _ (by simp only [AR, SH8, C_KC] at ha hx ⊢; omega)]
  exact h x hx

theorem MFrame.readMem {M0 M1 : Nat → UInt8} (h : MFrame M0 M1) {a n : Nat}
    (ha : a + n ≤ C_KC ∨ (C_KC + 4 ≤ a ∧ a + n ≤ AR) ∨ SH8 ≤ a) : readMem M1 a n = readMem M0 a n := by
  apply readMem_congr
  intro i hi
  exact h _ (by simp only [AR, SH8, C_KC] at ha ⊢; omega)

theorem rcpts_frame {cb pb : Bytes} {rs : List Receipt} {R : Nat} {m m' : M} (h : RcptsSt cb pb rs R m)
    (h14 : m'.regs 14 = m.regs 14) (h15 : m'.regs 15 = m.regs 15) (hf : MFrame m.mem m'.mem) :
    RcptsSt cb pb rs R m' := by
  obtain ⟨⟨⟨⟨k1, k8, hd⟩, hcl, hs⟩, ok, hr, hpl, hpe, hn, hre, hrt⟩, hpf⟩ := h
  have hnb := ok.n_max
  simp only [Params.maxBatch] at hnb
  simp only [PMAX] at hpl
  have hRl := ok.Rle
  refine ⟨⟨⟨⟨by rw [h15]; exact k1, by rw [h14]; exact k8, ?_⟩, ?_, hs⟩, ok, ?_, hpl, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hf.readMem (by simp only [C_KC]; omega)]; exact hd
  · rw [hf.readMem (by simp only [C_KC, CLM]; omega)]; exact hcl
  · rw [hf.readMem (by simp only [C_KC, SH8, PF]; omega)]; exact hr
  · simp only [rd32]; rw [hf.readMem (by simp only [C_KC, C_PEND]; omega)]; exact hpe
  · simp only [rd32]; rw [hf.readMem (by simp only [C_KC, C_N]; omega)]; exact hn
  · simp only [rd32]; rw [hf.readMem (by simp only [C_KC, C_REND]; omega)]; exact hre
  · intro i hi; rw [hf.readMem (by simp only [C_KC, RT, AR]; omega)]; exact hrt i hi
  · rw [hf.readMem (by simp only [C_KC, SH8, PF]; omega)]; exact hpf

/-! ## Reading the proof copy -/

theorem leToNat_eq_leNat' : ∀ l : NearSpec.Bytes, ArenaCore.Bytes.leToNat l = NearSpec.leNat l
  | [] => rfl
  | x :: xs => by simp [ArenaCore.Bytes.leToNat, NearSpec.leNat, leToNat_eq_leNat' xs]

theorem rdProof' {M0 : Nat → UInt8} {pb : NearSpec.Bytes} (h : readMem M0 PF pb.length = pb) {o n : Nat}
    (hn : o + n ≤ pb.length) : readMem M0 (PF + o) n = sl pb o n := by
  apply List.ext_getElem (by simp [sl]; omega)
  intro i h1 h2
  simp only [readMem_length] at h1
  rw [readMem_getElem]
  have := mem_of_readMem h (o + i) (by omega)
  rw [Nat.add_assoc, this]
  simp [sl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show o + i < pb.length by omega)]

theorem rdmProof {M0 : Nat → UInt8} {pb : NearSpec.Bytes} (h : readMem M0 PF pb.length = pb) {o w : Nat}
    (hn : o + w ≤ pb.length) : ArenaCore.Bytes.leToNat (readMem M0 (PF + o) w) = leAt pb o w := by
  rw [rdProof' h hn, leToNat_eq_leNat']; rfl

theorem byteProof {M0 : Nat → UInt8} {pb : NearSpec.Bytes} (h : readMem M0 PF pb.length = pb) {o : Nat}
    (hn : o < pb.length) : (M0 (PF + o)).toNat = u8At pb o := by
  have := mem_of_readMem h o hn
  rw [this]; simp [u8At, List.getD_eq_getElem?_getD]

theorem dZero {M0 : Nat → UInt8} (h : readMem M0 0 168 = dataSeg) : readMem M0 136 32 = zeros 32 := by
  have : readMem M0 136 32 = (readMem M0 0 168).drop 136 := by
    apply List.ext_getElem (by simp)
    intro i h1 h2; simp [readMem]
  rw [this, h]; decide

end ReexecNpai
