import ReexecNpai.Spec.Record
import ReexecNpai.Spec.ParseAux5

/-!
# Phase spec: the trie section (record parse into the arena)
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

namespace ParseProof

/-! ## Splitting `pParse` -/

def pProL : List Stmt := [ldCell 10 C_REND, ldCell 9 C_PEND, need 10 4 9, ld32 0 10, ADDI 10 10 4,
  stCell C_NODES 0, CST 8 0, CST 7 0, CST 5 0, CST 0 0, stCell C_KC 0, LTU 4 10 9]

def pLoop : Stmt := .loop 4 (seqs [pRecord, LTU 4 10 9])

def pEpiL : List Stmt := [ldCell 0 C_NODES, eqc 8 0, CST 0 1, eqc 7 0,
  CST 0 3000000, le 5 0,
  SUB 0 8 15, CST 1 24, MUL 0 0 1, ADDI 0 0 (AR + 8), CST 1 C_ROOT, st32 0 1]

theorem pParse_eq : pParse = seqs (pProL ++ [.seq pLoop (seqs pEpiL)]) := rfl

section
variable {p : Program} {inp : Inputs}

theorem wp_seqs_app : ∀ (l1 : List Stmt) (b : Stmt) {m : M} {Q : M → Prop}, l1 ≠ [] →
    wp p inp (seqs l1) m (fun m1 => wp p inp b m1 Q) → wp p inp (seqs (l1 ++ [b])) m Q
  | [], _, _, _, h, _ => absurd rfl h
  | [a], b, m, Q, _, h => by simpa [seqs] using h
  | a :: a' :: l, b, m, Q, _, h => by
    simp only [List.cons_append, seqs] at h ⊢
    rw [wp_seq] at h ⊢
    exact wp_mono h (fun m1 h1 => wp_seqs_app (a' :: l) b (by simp) h1)

theorem twp_seqs_app : ∀ (l1 : List Stmt) (b : Stmt) {m : M} {Q : M → Nat → Prop}, l1 ≠ [] →
    twp p inp (seqs l1) m (fun m1 c1 => twp p inp b m1 (fun m2 c2 => Q m2 (c1 + c2))) →
    twp p inp (seqs (l1 ++ [b])) m Q
  | [], _, _, _, h, _ => absurd rfl h
  | [a], b, m, Q, _, h => by simpa [seqs] using h
  | a :: a' :: l, b, m, Q, _, h => by
    simp only [List.cons_append, seqs] at h ⊢
    rw [twp_seq] at h ⊢
    refine twp_mono h (fun m1 c1 h1 => ?_)
    refine twp_seqs_app (a' :: l) b (by simp) (twp_mono h1 (fun m2 c2 h2 => ?_))
    exact twp_mono h2 (fun m3 c3 h3 => by rwa [← Nat.add_assoc])

end

section
variable {pub cb pb : Bytes} {rs : List Receipt} {R : Nat}

/-! ## Prologue -/

theorem pinv_init {m : M} (h : RcptsSt cb pb rs R m) (r : Nat → Nat) (hR : R + 4 ≤ pb.length)
    (h14 : r 14 = 8) (h15 : r 15 = 1) (h10 : r 10 = PF + (R + 4)) (h9 : r 9 = PF + pb.length)
    (h8 : r 8 = 0) (h7 : r 7 = 0) (h5 : r 5 = 0) (N : Nat) (hN : N < 4294967296) :
    ParseInv cb pb rs R N (R + 4) [] [] []
      ⟨r, writeMem (writeMem m.mem 3120 4 (ArenaCore.Bytes.leN 4 N)) 3172 4 (ArenaCore.Bytes.leN 4 0)⟩ := by
  have h1 := RcptsSt_write h r 3120 4 (ArenaCore.Bytes.leN 4 N) h14 h15 (by simp [RT])
  have h2 := RcptsSt_write h1 r 3172 4 (ArenaCore.Bytes.leN 4 0) h14 h15 (by simp [RT])
  refine { st := h2, rP := h10, rE := h9, re := h8, rsp := h7, rrv := by simp [h5, revSum],
           kc := ?_, hdr := ?_, oR := Nat.le_refl _, ole := hR, cap := by simp [NCAP],
           dec := by simp [decRecs], wf := by simp, first := by simp, contig := by simp,
           last := by simp, stack := ?_, amem := by simp, kmem := by simp, krange := by simp,
           smem := by simp, klen := rfl }
  · simp only [rd32, C_KC]; exact rd32_write_same _ _ _ (by decide)
  · simp only [rd32, C_NODES]
    rw [readMem_writeMem_disjoint _ _ _ _ _ _ (by omega)]
    exact rd32_write_same _ _ _ hN
  · refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_⟩ <;> simp

theorem pro_wp {m : M} (h : RcptsSt cb pb rs R m) :
    wp P (Inp pub cb pb) (seqs pProL) m (fun m1 => ParseInv cb pb rs R (rd32 m (PF + R)) (R + 4) [] [] [] m1 ∧
      m1.regs 4 = if R + 4 < pb.length then 1 else 0) := by
  have hk1 := h.k1
  have hk8 := h.k8
  have hrend : ArenaCore.Bytes.leToNat (readMem m.mem 3080 4) = 8844304 + R := h.rend
  have hpend : ArenaCore.Bytes.leToNat (readMem m.mem 3072 4) = 8844304 + pb.length := h.pend
  have hpl := h.plen
  have hRl := h.ok.Rle
  have hNl := rd32_lt m.mem (8844304 + R)
  simp only [pProL, ldCell, stCell]
  npai_auto [hk1, hk8, hrend, hpend]
  rename_i hR
  refine ⟨pinv_init h _ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ hNl, by split <;> split <;> omega⟩
  all_goals (simp only [setReg_apply]; simp [hk1, hk8, PF]; try omega)

/-- Opaque wrapper keeping big postconditions away from the VC simp set. -/
@[irreducible] def Wr (P : Prop) : Prop := P

theorem Wr.out {P : Prop} (h : Wr P) : P := by unfold Wr at h; exact h

theorem pro_twp {m : M} (h : RcptsSt cb pb rs R m) (hR : R + 4 ≤ pb.length) :
    twp P (Inp pub cb pb) (seqs pProL) m (fun m1 c => ParseInv cb pb rs R (rd32 m (PF + R)) (R + 4) [] [] [] m1 ∧
      m1.regs 4 = (if R + 4 < pb.length then 1 else 0) ∧ c ≤ 1000) := by
  have hk1 := h.k1
  have hk8 := h.k8
  have hrend : ArenaCore.Bytes.leToNat (readMem m.mem 3080 4) = 8844304 + R := h.rend
  have hpend : ArenaCore.Bytes.leToNat (readMem m.mem 3072 4) = 8844304 + pb.length := h.pend
  have hpl := h.plen
  have hR' : ¬ 8844304 + pb.length < 8844304 + R + 4 := by omega
  suffices hs : twp P (Inp pub cb pb) (seqs pProL) m (fun m1 c =>
      Wr (ParseInv cb pb rs R (rd32 m (PF + R)) (R + 4) [] [] [] m1) ∧
      m1.regs 4 = (if R + 4 < pb.length then 1 else 0) ∧ c ≤ 1000) from
    twp_mono hs (fun m1 c ⟨h1, h2, h3⟩ => ⟨h1.out, h2, h3⟩)
  simp only [pProL, ldCell, stCell]
  npai_vc [hk1, hk8, hrend, hpend, hR']
  have hNl := rd32_lt m.mem (8844304 + R)
  refine ⟨?_, by split <;> split <;> omega⟩
  unfold Wr
  refine pinv_init h _ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ _ hNl
  all_goals (simp only [setReg_apply]; simp [hk1, hk8, PF]; try omega)

/-! ## Epilogue -/

theorem epi_wp {N : Nat} {A : List Ent} {K S : List Nat} {m : M}
    (hI : ParseInv cb pb rs R N pb.length A K S m) (hN : N = leNat (sl pb R 4)) :
    wp P (Inp pub cb pb) (seqs pEpiL) m (fun m' => ∃ A K, TrieSt cb pb rs R A K (vals0 pb A) m') := by
  have hk1 := hI.st.k1
  have hk8 := hI.st.k8
  have hre := hI.re
  have hrsp := hI.rsp
  have hrrv := hI.rrv
  have hcap := hI.cap
  simp only [NCAP] at hcap
  have hhdr : ArenaCore.Bytes.leToNat (readMem m.mem 3120 4) = N := hI.hdr
  suffices hs : wp P (Inp pub cb pb) (seqs pEpiL) m (fun m' => Wr (∃ A K, TrieSt cb pb rs R A K (vals0 pb A) m')) from
    wp_mono hs (fun m' h => h.out)
  simp only [pEpiL, ldCell]
  by_cases hS1 : S.length = 1
  · obtain ⟨s0, rfl⟩ := List.length_eq_one_iff.mp hS1
    obtain ⟨-, hs0, -⟩ := arena_wf' hI rfl
    npai_auto [hk1, hk8, hre, hrsp, hrrv, hhdr]
    rename_i hAN _ hrv
    unfold Wr
    exact ⟨_, K, finish hI hN hAN rfl (by omega) _ (by simp [setReg_apply, hk8]) (by simp [setReg_apply, hk1]) _
      (by simp only [AR]; omega)⟩
  · npai_auto [hk1, hk8, hre, hrsp, hrrv, hhdr]
    all_goals exact absurd ‹_› hS1

theorem epi_twp {N : Nat} {A : List Ent} {K : List Nat} {s0 : Nat} {m : M}
    (hI : ParseInv cb pb rs R N pb.length A K [s0] m) (hN : N = leNat (sl pb R 4)) (hAN : A.length = N)
    (hrv : revSum pb A ≤ 3000000) :
    twp P (Inp pub cb pb) (seqs pEpiL) m (fun m' c => (∃ A K, TrieSt cb pb rs R A K (vals0 pb A) m') ∧ c ≤ 1000) := by
  have hk1 := hI.st.k1
  have hk8 := hI.st.k8
  have hre := hI.re
  have hrsp : m.regs 7 = 1 := hI.rsp
  have hrrv := hI.rrv
  have hcap := hI.cap
  simp only [NCAP] at hcap
  have hhdr : ArenaCore.Bytes.leToNat (readMem m.mem 3120 4) = N := hI.hdr
  obtain ⟨-, hs0, -⟩ := arena_wf' hI rfl
  have hrv' : ¬ 3000000 < revSum pb A := by omega
  suffices hs : twp P (Inp pub cb pb) (seqs pEpiL) m
      (fun m' c => Wr (∃ A K, TrieSt cb pb rs R A K (vals0 pb A) m') ∧ c ≤ 1000) from
    twp_mono hs (fun m' c h => ⟨h.1.out, h.2⟩)
  simp only [pEpiL, ldCell]
  npai_vc [hk1, hk8, hre, hrsp, hrrv, hhdr, hAN, hrv']
  unfold Wr
  exact ⟨_, K, finish hI hN hAN rfl hrv _ (by simp [setReg_apply, hk8]) (by simp [setReg_apply, hk1]) _
    (by simp only [AR]; omega)⟩

/-! ## The record loop -/

theorem parse_leToNat_eq : ∀ l : NearSpec.Bytes, ArenaCore.Bytes.leToNat l = NearSpec.leNat l
  | [] => rfl
  | x :: xs => by simp [ArenaCore.Bytes.leToNat, NearSpec.leNat, parse_leToNat_eq xs]

theorem hdr_eq {m : M} (h : RcptsSt cb pb rs R m) (hR : R + 4 ≤ pb.length) :
    rd32 m (PF + R) = leNat (sl pb R 4) := by
  unfold rd32
  rw [rdP h.proof (by omega) (by omega), parse_leToNat_eq]
  simp [pseg, sl]

theorem loop_wp {N : Nat} {m : M}
    (h0 : ∃ o A K S, ParseInv cb pb rs R N o A K S m ∧ m.regs 4 = if o < pb.length then 1 else 0) :
    wp P (Inp pub cb pb) pLoop m (fun m' => ∃ A K S, ParseInv cb pb rs R N pb.length A K S m') := by
  refine wp_loop (fun m => ∃ o A K S, ParseInv cb pb rs R N o A K S m ∧
    m.regs 4 = if o < pb.length then 1 else 0) h0 ?_ ?_
  · intro m ⟨o, A, K, S, hp, h4⟩ hx
    have hlt : o < pb.length := by
      by_cases h : o < pb.length
      · exact h
      · simp [h] at h4; exact absurd h4 hx
    exact wp_mono (record_wp hp hlt) (fun m' ⟨o', A', K', S', hp', _, _, h4'⟩ => ⟨o', A', K', S', hp', h4'⟩)
  · intro m ⟨o, A, K, S, hp, h4⟩ hz
    have ho : o = pb.length := by
      have := hp.ole
      by_cases h : o < pb.length
      · simp [h] at h4; rw [h4] at hz; exact absurd hz (by decide)
      · omega
    subst ho
    exact ⟨A, K, S, hp⟩

/-! ## Completeness -/

theorem decTrie_inv {t : PTrie} (hd : decTrie (pb.drop R) = some t) :
    R + 4 ≤ pb.length ∧ decRecs (leNat (sl pb R 4)) [] (pb.drop (R + 4)) = some ([t], []) := by
  unfold decTrie at hd
  split at hd
  · simp at hd
  · rename_i n bs h1
    have hR : R + 4 ≤ pb.length := by
      rcases Nat.lt_or_ge pb.length (R + 4) with hc | hc
      · have : takeN 4 (pb.drop R) = none := (takeN_none_iff 4 _).mpr (by simp; omega)
        simp [readU32, readLE, this] at h1
      · exact hc
    refine ⟨hR, ?_⟩
    have h4 : 4 ≤ (pb.drop R).length := by simp; omega
    simp only [readU32, readLE, takeN_eq 4 _ h4, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    split at hd
    · rename_i t' hdr
      simp only [Option.some.injEq] at hd
      subst hd
      rw [List.drop_drop] at hdr
      exact hdr
    · simp at hd

/-- Loop invariant for completeness: the remaining records decode to `t`. -/
def LT (cb pb : Bytes) (rs : List Receipt) (R N : Nat) (t : PTrie) (m : M) : Prop :=
  ∃ o A K S, ParseInv cb pb rs R N o A K S m ∧ m.regs 4 = (if o < pb.length then 1 else 0) ∧
    A.length ≤ N ∧ decRecs (N - A.length) ((S.map (treeAt A K (vals0 pb A))).reverse) (pb.drop o) = some ([t], [])

def potL (pb : Bytes) (m : M) : Nat := 80 * (PF + pb.length - m.regs 10) + 2 * (NCAP - m.regs 8)

theorem loop_twp {N : Nat} {t : PTrie} (hN : N ≤ 272727) {m : M} (h0 : LT cb pb rs R N t m) :
    twp P (Inp pub cb pb) pLoop m (fun m' c => (∃ A K s0, ParseInv cb pb rs R N pb.length A K [s0] m' ∧
      A.length = N ∧ treeAt A K (vals0 pb A) s0 = t) ∧ c + potL pb m' ≤ potL pb m + 1) := by
  refine twp_loop (LT cb pb rs R N t) (potL pb) h0 ?_ ?_
  · intro m ⟨o, A, K, S, hp, h4, hAN, hdr⟩ hx
    have hlt : o < pb.length := by
      by_cases h : o < pb.length
      · exact h
      · simp [h] at h4; exact absurd h4 hx
    have hAN' : A.length < N := by
      rcases Nat.lt_or_ge A.length N with h | h
      · exact h
      · have : N - A.length = 0 := by omega
        rw [this] at hdr
        simp only [decRecs, Option.some.injEq, Prod.mk.injEq] at hdr
        have := hdr.2
        simp at this; omega
    obtain ⟨k, hk⟩ : ∃ k, N - A.length = k + 1 := ⟨N - A.length - 1, by omega⟩
    rw [hk] at hdr
    simp only [decRecs] at hdr
    split at hdr
    · simp at hdr
    · rename_i stk' bs' hrec
      obtain ⟨⟨j0, hj0⟩, -⟩ := decRec_cs hrec
      rw [List.drop_drop] at hj0
      have hj : bs' = pb.drop (o + min j0 (pb.length - o)) := by
        rw [hj0]
        rcases Nat.le_total j0 (pb.length - o) with h | h
        · rw [Nat.min_eq_left h]
        · rw [Nat.min_eq_right h, List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
      have hjle : o + min j0 (pb.length - o) ≤ pb.length := by omega
      generalize min j0 (pb.length - o) = j at hj hjle
      subst hj
      have hcap : A.length < NCAP := by simp only [NCAP]; omega
      refine twp_mono (record_twp hp hlt hcap hrec hjle) ?_
      intro m' c ⟨A', K', S', hp', hlen, h4', hc⟩
      have hd1 := decRecs_add' A.length 1 _ _ _ _ hp.dec
      have hd2 : decRecs 1 ((S.map (treeAt A K (vals0 pb A))).reverse) (pb.drop o) =
          some (stk', pb.drop (o + j)) := by simp [decRecs, hrec]
      rw [hd2] at hd1
      have hstk : (S'.map (treeAt A' K' (vals0 pb A'))).reverse = stk' := by
        have := hp'.dec
        rw [hlen, hd1] at this
        simp only [Option.some.injEq, Prod.mk.injEq] at this
        exact this.1.symm
      refine ⟨⟨o + j, A', K', S', hp', h4', by omega, ?_⟩, ?_⟩
      · rw [hstk, show N - A'.length = k by omega]; exact hdr
      · have h10 := hp.rP
        have h8 := hp.re
        have h10' := hp'.rP
        have h8' := hp'.re
        have hole := hp'.ole
        unfold potL
        rw [h10, h8, h10', h8']
        simp only [NCAP] at hcap ⊢
        have : c ≤ 80 * (o + j - o) := hc
        omega
  · intro m' c ⟨o, A, K, S, hp, h4, hAN, hdr⟩ hz hc
    have ho : o = pb.length := by
      have := hp.ole
      by_cases h : o < pb.length
      · simp [h] at h4; rw [h4] at hz; exact absurd hz (by decide)
      · omega
    subst ho
    rw [List.drop_length] at hdr
    have hAN' : A.length = N := by
      rcases Nat.lt_or_ge A.length N with h | h
      · obtain ⟨k, hk⟩ : ∃ k, N - A.length = k + 1 := ⟨N - A.length - 1, by omega⟩
        rw [hk] at hdr
        simp [decRecs, decRec] at hdr
      · omega
    rw [hAN', Nat.sub_self] at hdr
    simp only [decRecs, Option.some.injEq, Prod.mk.injEq] at hdr
    obtain ⟨hs, -⟩ := hdr
    have hl : S.length = 1 := by
      have := congrArg List.length hs
      simpa using this
    obtain ⟨s0, rfl⟩ := List.length_eq_one_iff.mp hl
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons.injEq, and_true] at hs
    exact ⟨⟨A, K, s0, hp, hAN', hs⟩, hc⟩

end

end ParseProof

open ParseProof

section
variable {pub cb pb : Bytes} {rs : List Receipt} {R : Nat}

/-! ## Soundness -/

theorem parse_wp {m : M} (h : RcptsSt cb pb rs R m) :
    wp P (Inp pub cb pb) pParse m (fun m' => ∃ A K, TrieSt cb pb rs R A K (vals0 pb A) m') := by
  rw [pParse_eq]
  refine wp_seqs_app _ _ (by simp [pProL]) (wp_mono (pro_wp h) (fun m1 ⟨hp, h4⟩ => ?_))
  have hN := hdr_eq h (by have := hp.oR; have := hp.ole; omega)
  rw [wp_seq]
  exact wp_mono (loop_wp ⟨R + 4, [], [], [], hp, h4⟩) (fun m2 ⟨A, K, S, hI⟩ => epi_wp hI hN)

/-! ## Completeness -/

theorem parse_twp {m : M} (h : RcptsSt cb pb rs R m) {t : PTrie}
    (hd : decTrie (pb.drop R) = some t) (hs : t.revealedBytes ≤ Params.maxWitnessBytes) :
    twp P (Inp pub cb pb) pParse m (fun m' c => ∃ A K, TrieSt cb pb rs R A K (vals0 pb A) m' ∧
      rootT A K (vals0 pb A) = t ∧ c ≤ 80 * pb.length + 600000) := by
  obtain ⟨hR, hdr⟩ := decTrie_inv hd
  have hN := hdr_eq h hR
  have hcnt := decRecs_cnt _ _ _ _ _ hdr
  simp only [cntL] at hcnt
  have h11 := cntT_le' t
  simp only [Params.maxWitnessBytes] at hs
  have hNb : leNat (sl pb R 4) ≤ 272727 := by omega
  rw [pParse_eq]
  refine twp_seqs_app _ _ (by simp [pProL]) (twp_mono (pro_twp h hR) (fun m1 c1 ⟨hp, h4, hc1⟩ => ?_))
  rw [twp_seq]
  rw [hN] at hp
  have h0 : LT cb pb rs R (leNat (sl pb R 4)) t m1 :=
    ⟨R + 4, [], [], [], hp, h4, Nat.zero_le _, by simpa using hdr⟩
  refine twp_mono (loop_twp hNb h0) (fun m2 c2 ⟨⟨A, K, s0, hI, hAN, hts⟩, hc2⟩ => ?_)
  have hrv : revSum pb A ≤ 3000000 := by
    rw [rev_root hI rfl, ← (arena_wf' hI rfl).1, hts]; exact hs
  refine twp_mono (epi_twp hI rfl hAN hrv) (fun m3 c3 ⟨⟨A', K', hT⟩, hc3⟩ => ⟨A', K', hT, ?_, ?_⟩)
  · have := hT.tok.dec
    rw [hd] at this
    exact (Option.some.inj this).symm
  · have h10 := hp.rP
    have h8 := hp.re
    unfold potL at hc2
    rw [h10, h8] at hc2
    simp only [NCAP, PF, List.length_nil] at hc2
    omega

end

end ReexecNpai
