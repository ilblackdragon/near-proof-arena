import ReexecNpai.Spec.RcptAux3

/-!
# Receipts phase, part 4: the prefix checks
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore Interp NearSpec NearSpec.TransferV1

namespace RcptProof

section
variable {p : Program} {inp : Inputs}

theorem wp_seqs_append : ∀ (l1 l2 : List Stmt) (m : M) (Q : M → Prop), l1 ≠ [] → l2 ≠ [] →
    wp p inp (seqs l1) m (fun m1 => wp p inp (seqs l2) m1 Q) → wp p inp (seqs (l1 ++ l2)) m Q
  | [], _, _, _, h, _, _ => absurd rfl h
  | [a], l2, m, Q, _, h2, h => by
    match l2, h2 with
    | b :: l, _ => simp only [List.cons_append, List.nil_append, seqs, wp_seq]; exact h
  | a :: b :: l1, l2, m, Q, _, h2, h => by
    match l2, h2 with
    | c :: l, _ =>
      simp only [List.cons_append, seqs, wp_seq] at h ⊢
      refine wp_mono h (fun m1 h1 => ?_)
      have := wp_seqs_append (b :: l1) (c :: l) m1 Q (by simp) (by simp) h1
      simpa [seqs] using this

theorem twp_seqs_append : ∀ (l1 l2 : List Stmt) (m : M) (Q : M → Nat → Prop), l1 ≠ [] → l2 ≠ [] →
    twp p inp (seqs l1) m (fun m1 c1 => twp p inp (seqs l2) m1 (fun m2 c2 => Q m2 (c1 + c2))) →
    twp p inp (seqs (l1 ++ l2)) m Q
  | [], _, _, _, h, _, _ => absurd rfl h
  | [a], l2, m, Q, _, h2, h => by
    match l2, h2 with
    | b :: l, _ => simp only [List.cons_append, List.nil_append, seqs, twp_seq]; exact h
  | a :: b :: l1, l2, m, Q, _, h2, h => by
    match l2, h2 with
    | c :: l, _ =>
      simp only [List.cons_append, seqs, twp_seq] at h ⊢
      refine twp_mono h (fun m1 c1 h1 => ?_)
      have := twp_seqs_append (b :: l1) (c :: l) m1 (fun m2 c2 => Q m2 (c1 + c2)) (by simp) (by simp)
        (twp_mono h1 (fun m2 c2 h2 => twp_mono h2 (fun m3 c3 h3 => by rwa [Nat.add_assoc] at h3)))
      simpa [seqs] using this

end

/-- `npai_vc` with a goal-only discharger. -/
syntax "rcpt_vc" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rcpt_vc) => `(tactic| rcpt_vc [])
  | `(tactic| rcpt_vc [$ts,*]) => `(tactic|
      simp (disch := (first | omega | (simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega)))
        only [wp_seq, wp_op, wp_ite, wp_nop, twp_seq, twp_op, twp_ite, twp_nop,
        wp_fail_iff P_mem_le, twp_fail_iff P_mem_le, okInstr, not_true_eq_false, false_and, and_false,
        false_or, or_false, Nat.reduceDiv, Nat.reduceSub, ins, setReg_apply, ite_pos, ite_neg, evAbyte, evAbyte', evA, evS, evM,
        evShl8, evShr8, evAddi, evConst, evEq, evLtu, cost, ↓reduceIte, Nat.reduceAdd, Nat.reduceMul,
        Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceLeDiff, K1, K8, seqs, chkEq, chkLe, chkLt, assert, assertZ,
        need, le, lt, eqc, P_memSize, Bool.true_eq_false, Bool.false_eq_true, Option.some.injEq,
        forall_eq', true_implies, imp_self, implies_true, and_true, true_and, Inp, Inputs.tape,
        Option.ite_none_right_eq_some, and_imp, exists_eq_left', exists_eq_left, and_assoc, exists_and_left,
        not_false_eq_true, Nat.zero_add, Nat.le_refl, ite10_ne_zero, ite10_eq_zero, forall_apply_eq_imp_iff₂, List.drop_zero,
        DATA, SCR, CLM, CELL, RT, OL, RB, AR, KL, STK, SH8, PF, MEMSIZE, PMAX, NCAP,
        D_CPRE, D_SYS, D_MID, D_FF, D_G, D_P519, D_ZERO, C_PEND, C_N, C_REND, C_TOK, C_NREF, C_RBEND,
        C_NODES, C_ROOT, C_I, C_KC, S_KEY, S_HP, S_A, S_B, S_C, S_D, S_E, S_ID, S_OUT, S_LEAF, S_H,
        wp_ld32, twp_ld32, wp_ld16, twp_ld16, wp_ld64, twp_ld64, wp_st32, twp_st32, memsize_lt,
        forall_cond_eq, ldConst64, $ts,*])

syntax "rcpt_auto" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rcpt_auto) => `(tactic| rcpt_auto [])
  | `(tactic| rcpt_auto [$ts,*]) => `(tactic| repeat (first | (rcpt_vc [$ts,*]) | (intro)))

def LPre1 : List Stmt := [CST 4 C_PEND, ld32 9 4, CST 10 PF, need 10 4 9, ld32 7 10, ADDI 10 10 4]
def LPre2 : List Stmt := [CST 4 (CLM + 149), ld32 1 4, eqc 7 1, CST 1 1, le 1 7, CST 1 256, le 7 1]
def LPre3 : List Stmt := [ldConst64 1 D_G, SUB 2 7 15, MUL 2 2 1, CST 4 (CLM + 109), ld64 3 4, lt 2 3]
def LPre4 : List Stmt := [CST 4 C_N, st32 4 7, CST 8 0, CST 6 RT]

def LPre : List Stmt := LPre1 ++ LPre2 ++ LPre3 ++ LPre4

section
variable {pub cb pb : NearSpec.Bytes}

theorem pre1_wp {m : M} (hk8 : m.regs 14 = 8) (hpe : (readMem m.mem 3072 4).leToNat = 8844304 + pb.length)
    (hpl : pb.length ≤ 5000000)
    (hp0 : 4 ≤ pb.length → (readMem m.mem 8844304 4).leToNat = NearSpec.leNat (sl pb 0 4)) :
    wp P (Inp pub cb pb) (seqs LPre1) m (fun m' => 4 ≤ pb.length ∧ m'.mem = m.mem ∧
      m'.regs 9 = PF + pb.length ∧ m'.regs 7 = NearSpec.leNat (sl pb 0 4) ∧ m'.regs 10 = PF + 4 ∧
      Frame [4, 7, 9, 10, 12, 13] m m') := by
  simp only [LPre1]
  rcpt_auto [hk8, hpe, hp0]
  exact ⟨by omega, by rcpt_frame_tac⟩

theorem pre2_wp {m : M} {n : Nat} (hk8 : m.regs 14 = 8) (h7 : m.regs 7 = n)
    (hc1 : (readMem m.mem 2709 4).leToNat = NearSpec.leNat (seg cb 149 4)) :
    wp P (Inp pub cb pb) (seqs LPre2) m (fun m' => n = NearSpec.leNat (seg cb 149 4) ∧ 1 ≤ n ∧ n ≤ 256 ∧
      m'.mem = m.mem ∧ Frame [1, 4, 12, 13] m m') := by
  simp only [LPre2]
  rcpt_auto [hk8, h7, hc1]
  exact ⟨by assumption, by omega, by omega, by rcpt_frame_tac⟩

theorem pre3_wp {m : M} {n : Nat} (hk8 : m.regs 14 = 8) (hk1 : m.regs 15 = 1) (h7 : m.regs 7 = n)
    (h1 : 1 ≤ n) (h256 : n ≤ 256)
    (hg : (readMem m.mem 120 8).leToNat = 223182562500)
    (hc2 : (readMem m.mem 2669 8).leToNat = NearSpec.leNat (seg cb 109 8)) :
    wp P (Inp pub cb pb) (seqs LPre3) m (fun m' => (n - 1) * 223182562500 < NearSpec.leNat (seg cb 109 8) ∧
      m'.mem = m.mem ∧ Frame [1, 2, 3, 4, 11, 12, 13] m m') := by
  simp only [LPre3]
  rcpt_auto [hk8, hk1, h7, hg, hc2]
  exact ⟨by assumption, by rcpt_frame_tac⟩

theorem pre4_wp {m : M} {n : Nat} (hk8 : m.regs 14 = 8) (h7 : m.regs 7 = n) (h256 : n ≤ 256) :
    wp P (Inp pub cb pb) (seqs LPre4) m (fun m' => m'.mem = writeMem m.mem 3076 4 (Bytes.leN 4 n) ∧
      m'.regs 8 = 0 ∧ m'.regs 6 = RT ∧ Frame [4, 6, 8, 12, 13] m m') := by
  simp only [LPre4]
  rcpt_auto [hk8, h7]
  rename_i j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  obtain ⟨a1, a2, a3, a4, a5⟩ := hj
  simp [a1, a2, a3, a4, a5]

end

/-- State after the prefix checks. -/
structure PreSt (cb pb : NearSpec.Bytes) (n : Nat) (ms : M) : Prop extends LBase cb pb ms where
  r9 : ms.regs 9 = PF + pb.length
  r7 : ms.regs 7 = n
  r8 : ms.regs 8 = 0
  r10 : ms.regs 10 = PF + 4
  r6 : ms.regs 6 = RT
  n4 : 4 ≤ pb.length
  count : NearSpec.leNat (sl pb 0 4) = n
  cnt : n = (claimOf cb).receiptCount
  npos : 1 ≤ n
  nmax : n ≤ 256
  gas : (n - 1) * Params.G < (claimOf cb).gasLimit
  pend : rd32 ms C_PEND = PF + pb.length
  nC : rd32 ms C_N = n

theorem seg_claim {M0 : Nat → UInt8} {cb : NearSpec.Bytes} (h : readMem M0 CLM 309 = cb) (k j : Nat)
    (hkj : k + j ≤ 309) : readMem M0 (2560 + k) j = seg cb k j := readMem_slice h k j hkj

theorem G_val : Params.G = 223182562500 := rfl

section
variable {pub cb pb : NearSpec.Bytes}

theorem mem_facts {M0 : Nat → UInt8} (hd : readMem M0 0 168 = dataSeg) (hcl : readMem M0 CLM 309 = cb)
    (hpf : readMem M0 PF pb.length = pb) :
    (readMem M0 2709 4).leToNat = NearSpec.leNat (seg cb 149 4) ∧
    (readMem M0 2669 8).leToNat = NearSpec.leNat (seg cb 109 8) ∧
    (readMem M0 120 8).leToNat = 223182562500 ∧
    (4 ≤ pb.length → (readMem M0 8844304 4).leToNat = NearSpec.leNat (sl pb 0 4)) := by
  refine ⟨?_, ?_, ?_, fun h4 => ?_⟩
  · rw [show (2709 : Nat) = 2560 + 149 from rfl, seg_claim hcl 149 4 (by omega), leToNat_eq_leNat]
  · rw [show (2669 : Nat) = 2560 + 109 from rfl, seg_claim hcl 109 8 (by omega), leToNat_eq_leNat]
  · rw [show (120 : Nat) = D_G from rfl, g_data hd, leToNat_eq_leNat, u64, ← leN_eq, ← G_val]
    rw [← leToNat_eq_leNat, leToNat_leN _ _ (by rw [G_val]; decide)]
  · rw [show (8844304 : Nat) = PF + 0 from rfl, rdProof hpf (by omega), leToNat_eq_leNat]

theorem preSt_of {m m4 : M} {n : Nat} (h : Front cb pb m) (h4 : 4 ≤ pb.length)
    (hm4 : m4.mem = writeMem m.mem 3076 4 (Bytes.leN 4 n)) (hn : NearSpec.leNat (sl pb 0 4) = n)
    (hcnt : n = NearSpec.leNat (seg cb 149 4)) (h1 : 1 ≤ n) (h256 : n ≤ 256)
    (hgas : (n - 1) * 223182562500 < NearSpec.leNat (seg cb 109 8))
    (r15 : m4.regs 15 = m.regs 15) (r14 : m4.regs 14 = m.regs 14) (r9 : m4.regs 9 = PF + pb.length)
    (r7 : m4.regs 7 = n) (r8 : m4.regs 8 = 0) (r10 : m4.regs 10 = PF + 4) (r6 : m4.regs 6 = RT) :
    PreSt cb pb n m4 := by
  obtain ⟨⟨⟨hk1, hk8, hd⟩, hcl, hs⟩, hpf, hpl, hpe⟩ := h
  have hr : ∀ a k, a + k ≤ 3076 ∨ 3080 ≤ a → readMem m4.mem a k = readMem m.mem a k := by
    intro a k hak; rw [hm4, readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]
  refine ⟨⟨⟨⟨by rw [r15, hk1], by rw [r14, hk8], by rw [hr _ _ (by omega)]; exact hd⟩,
    by rw [hr _ _ (by simp [CLM])]; exact hcl, hs⟩, by rw [hr _ _ (by simp [PF])]; exact hpf, hpl⟩,
    r9, r7, r8, r10, r6, h4, hn, by rw [hcnt]; rfl, h1, h256, by rw [G_val]; exact hgas,
    by simp only [rd32, C_PEND] at hpe ⊢; rw [hr _ _ (by omega)]; exact hpe, ?_⟩
  simp only [rd32, C_N]
  rw [hm4, readMem_writeMem_self _ _ _ _ (by simp [Bytes.leN_length]),
    List.take_of_length_le (by simp [Bytes.leN_length]), leToNat_leN _ _ (by omega)]

theorem prefix_wp {m : M} (h : Front cb pb m) :
    wp P (Inp pub cb pb) (seqs LPre) m (fun ms => ∃ n, PreSt cb pb n ms) := by
  have h' := h
  obtain ⟨⟨⟨hk1, hk8, hd⟩, hcl, hs⟩, hpf, hpl, hpe⟩ := h'
  simp only [rd32, C_PEND, PMAX] at hpe hpl
  obtain ⟨hc1, hc2, hg, hp0⟩ := mem_facts hd hcl hpf
  simp only [LPre]
  refine wp_seqs_append _ _ _ _ (by simp [LPre1]) (by simp [LPre4]) ?_
  refine wp_seqs_append _ _ _ _ (by simp [LPre1]) (by simp [LPre3]) ?_
  refine wp_seqs_append _ _ _ _ (by simp [LPre1]) (by simp [LPre2]) ?_
  refine wp_mono (pre1_wp hk8 hpe hpl hp0) ?_
  rintro m1 ⟨h4, hm1, h91, h71, h101, hF1⟩
  rw [← hm1] at hc1 hc2 hg
  refine wp_mono (pre2_wp (by rw [hF1 14 (by decide), hk8]) h71 hc1) ?_
  rintro m2 ⟨hcnt, hn1, hn256, hm2, hF2⟩
  rw [← hm2] at hc2 hg
  refine wp_mono (pre3_wp (by rw [hF2 14 (by decide), hF1 14 (by decide), hk8])
    (by rw [hF2 15 (by decide), hF1 15 (by decide), hk1]) (by rw [hF2 7 (by decide), h71]) hn1 hn256 hg hc2) ?_
  rintro m3 ⟨hgas, hm3, hF3⟩
  refine wp_mono (pre4_wp (by rw [hF3 14 (by decide), hF2 14 (by decide), hF1 14 (by decide), hk8])
    (by rw [hF3 7 (by decide), hF2 7 (by decide), h71]) hn256) ?_
  rintro m4 ⟨hm4, h84, h64, hF4⟩
  refine ⟨_, preSt_of h h4 (by rw [hm4, hm3, hm2, hm1]) rfl hcnt hn1 hn256 hgas
    (by rw [hF4 15 (by decide), hF3 15 (by decide), hF2 15 (by decide), hF1 15 (by decide)])
    (by rw [hF4 14 (by decide), hF3 14 (by decide), hF2 14 (by decide), hF1 14 (by decide)])
    (by rw [hF4 9 (by decide), hF3 9 (by decide), hF2 9 (by decide), h91])
    (by rw [hF4 7 (by decide), hF3 7 (by decide), hF2 7 (by decide), h71]) h84
    (by rw [hF4 10 (by decide), hF3 10 (by decide), hF2 10 (by decide), h101]) h64⟩

theorem pre1_twp {m : M} (hk8 : m.regs 14 = 8) (hpe : (readMem m.mem 3072 4).leToNat = 8844304 + pb.length)
    (hpl : pb.length ≤ 5000000) (h4 : 4 ≤ pb.length)
    (hp0 : 4 ≤ pb.length → (readMem m.mem 8844304 4).leToNat = NearSpec.leNat (sl pb 0 4)) :
    twp P (Inp pub cb pb) (seqs LPre1) m (fun m' c => m'.mem = m.mem ∧
      m'.regs 9 = PF + pb.length ∧ m'.regs 7 = NearSpec.leNat (sl pb 0 4) ∧ m'.regs 10 = PF + 4 ∧
      Frame [4, 7, 9, 10, 12, 13] m m' ∧ c ≤ 60) := by
  have hp0' := hp0 h4
  simp only [LPre1]
  rcpt_auto [hk8, hpe, hp0']
  exact ⟨by omega, by rcpt_frame_tac⟩

theorem pre2_twp {m : M} {n : Nat} (hk8 : m.regs 14 = 8) (h7 : m.regs 7 = n)
    (hc1 : (readMem m.mem 2709 4).leToNat = NearSpec.leNat (seg cb 149 4))
    (hcnt : n = NearSpec.leNat (seg cb 149 4)) (h1 : 1 ≤ n) (h256 : n ≤ 256) :
    twp P (Inp pub cb pb) (seqs LPre2) m (fun m' c => m'.mem = m.mem ∧ Frame [1, 4, 12, 13] m m' ∧ c ≤ 60) := by
  simp only [LPre2]
  rcpt_auto [hk8, h7, hc1]
  exact ⟨hcnt, by omega, by omega, by rcpt_frame_tac⟩

theorem pre3_twp {m : M} {n : Nat} (hk8 : m.regs 14 = 8) (hk1 : m.regs 15 = 1) (h7 : m.regs 7 = n)
    (h1 : 1 ≤ n) (h256 : n ≤ 256)
    (hg : (readMem m.mem 120 8).leToNat = 223182562500)
    (hc2 : (readMem m.mem 2669 8).leToNat = NearSpec.leNat (seg cb 109 8))
    (hgas : (n - 1) * 223182562500 < NearSpec.leNat (seg cb 109 8)) :
    twp P (Inp pub cb pb) (seqs LPre3) m (fun m' c => m'.mem = m.mem ∧ Frame [1, 2, 3, 4, 11, 12, 13] m m' ∧
      c ≤ 100) := by
  simp only [LPre3]
  rcpt_auto [hk8, hk1, h7, hg, hc2]
  exact ⟨hgas, by rcpt_frame_tac⟩

theorem pre4_twp {m : M} {n : Nat} (hk8 : m.regs 14 = 8) (h7 : m.regs 7 = n) (h256 : n ≤ 256) :
    twp P (Inp pub cb pb) (seqs LPre4) m (fun m' c => m'.mem = writeMem m.mem 3076 4 (Bytes.leN 4 n) ∧
      m'.regs 8 = 0 ∧ m'.regs 6 = RT ∧ Frame [4, 6, 8, 12, 13] m m' ∧ c ≤ 20) := by
  simp only [LPre4]
  rcpt_auto [hk8, h7]
  rename_i j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  obtain ⟨a1, a2, a3, a4, a5⟩ := hj
  simp [a1, a2, a3, a4, a5]

theorem prefix_twp {m : M} (h : Front cb pb m) {n : Nat} (h4 : 4 ≤ pb.length)
    (hn : NearSpec.leNat (sl pb 0 4) = n) (hcnt : n = (claimOf cb).receiptCount) (h1 : 1 ≤ n)
    (h256 : n ≤ 256) (hgas : (n - 1) * Params.G < (claimOf cb).gasLimit) :
    twp P (Inp pub cb pb) (seqs LPre) m (fun ms c => PreSt cb pb n ms ∧ c ≤ 300) := by
  have h' := h
  obtain ⟨⟨⟨hk1, hk8, hd⟩, hcl, hs⟩, hpf, hpl, hpe⟩ := h'
  simp only [rd32, C_PEND, PMAX] at hpe hpl
  obtain ⟨hc1, hc2, hg, hp0⟩ := mem_facts hd hcl hpf
  have hcnt' : n = NearSpec.leNat (seg cb 149 4) := hcnt
  have hgas' : (n - 1) * 223182562500 < NearSpec.leNat (seg cb 109 8) := hgas
  subst hn
  simp only [LPre]
  refine twp_seqs_append _ _ _ _ (by simp [LPre1]) (by simp [LPre4]) ?_
  refine twp_seqs_append _ _ _ _ (by simp [LPre1]) (by simp [LPre3]) ?_
  refine twp_seqs_append _ _ _ _ (by simp [LPre1]) (by simp [LPre2]) ?_
  refine twp_mono (pre1_twp hk8 hpe hpl h4 hp0) ?_
  rintro m1 c1 ⟨hm1, h91, h71, h101, hF1, hc1'⟩
  rw [← hm1] at hc1 hc2 hg
  refine twp_mono (pre2_twp (by rw [hF1 14 (by decide), hk8]) h71 hc1 hcnt' h1 h256) ?_
  rintro m2 c2 ⟨hm2, hF2, hc2'⟩
  rw [← hm2] at hc2 hg
  refine twp_mono (pre3_twp (by rw [hF2 14 (by decide), hF1 14 (by decide), hk8])
    (by rw [hF2 15 (by decide), hF1 15 (by decide), hk1]) (by rw [hF2 7 (by decide), h71]) h1 h256 hg hc2
    hgas') ?_
  rintro m3 c3 ⟨hm3, hF3, hc3'⟩
  refine twp_mono (pre4_twp (by rw [hF3 14 (by decide), hF2 14 (by decide), hF1 14 (by decide), hk8])
    (by rw [hF3 7 (by decide), hF2 7 (by decide), h71]) h256) ?_
  rintro m4 c4 ⟨hm4, h84, h64, hF4, hc4'⟩
  refine ⟨preSt_of h h4 (by rw [hm4, hm3, hm2, hm1]) rfl hcnt' h1 h256 hgas'
    (by rw [hF4 15 (by decide), hF3 15 (by decide), hF2 15 (by decide), hF1 15 (by decide)])
    (by rw [hF4 14 (by decide), hF3 14 (by decide), hF2 14 (by decide), hF1 14 (by decide)])
    (by rw [hF4 9 (by decide), hF3 9 (by decide), hF2 9 (by decide), h91])
    (by rw [hF4 7 (by decide), hF3 7 (by decide), hF2 7 (by decide), h71]) h84
    (by rw [hF4 10 (by decide), hF3 10 (by decide), hF2 10 (by decide), h101]) h64, by omega⟩
end

end RcptProof

end ReexecNpai
