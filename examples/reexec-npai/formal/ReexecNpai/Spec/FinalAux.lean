import ReexecNpai.Spec.State

/-!
# Helpers for the outputs phase: the in-place Merkle loop
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore ArenaCore.Interp NearSpec NearSpec.TransferV1

/-! ## Pure Merkle facts -/

theorem merkleLevel_length : ∀ (L : List NearSpec.Bytes), (merkleLevel L).length = (L.length + 1) / 2
  | [] => rfl
  | [_] => by simp [merkleLevel]
  | _ :: _ :: rest => by
    simp only [merkleLevel, List.length_cons, merkleLevel_length rest]; omega

theorem merkleLevel_getD : ∀ (L : List NearSpec.Bytes) (i : Nat), i < L.length / 2 →
    (merkleLevel L).getD i [] = NearSpec.sha256 (L.getD (2 * i) [] ++ L.getD (2 * i + 1) [])
  | [], _, h => by simp at h
  | [_], _, h => by simp at h
  | _ :: _ :: _, 0, _ => by simp [merkleLevel]
  | a :: b :: rest, i + 1, h => by
    simp only [merkleLevel, List.getD_cons_succ]
    rw [merkleLevel_getD rest i (by simp at h; omega), show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
    simp only [List.getD_cons_succ]

theorem merkleLevel_getD_odd : ∀ (L : List NearSpec.Bytes), L.length % 2 = 1 →
    (merkleLevel L).getD (L.length / 2) [] = L.getD (L.length - 1) []
  | [], h => by simp at h
  | [_], _ => by simp [merkleLevel]
  | a :: b :: rest, h => by
    simp only [merkleLevel, List.length_cons] at h ⊢
    rw [show (rest.length + 1 + 1) / 2 = rest.length / 2 + 1 by omega,
      show rest.length + 1 + 1 - 1 = (rest.length - 1) + 1 + 1 by omega]
    simp only [List.getD_cons_succ]
    exact merkleLevel_getD_odd rest (by omega)

theorem merkleLevel_all : ∀ (L : List NearSpec.Bytes), (∀ x ∈ L, x.length = 32) →
    ∀ x ∈ merkleLevel L, x.length = 32
  | [], h => h
  | [_], h => h
  | a :: b :: rest, h => by
    intro x hx
    simp only [merkleLevel, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ArenaCore.sha256_length _
    · exact merkleLevel_all rest (fun y hy => h y (by simp [hy])) x hx

theorem merkleFold_fuel : ∀ (f : Nat) (L : List NearSpec.Bytes), L.length ≤ f →
    merkleFold f L = merkleFold L.length L := by
  intro f
  induction f using Nat.strongRecOn with
  | _ f ih =>
    intro L hL
    match L, f, hL with
    | [], f, _ => cases f <;> rfl
    | [_], f, _ => cases f <;> rfl
    | a :: b :: rest, f + 1, hL =>
      have hlen := merkleLevel_length (a :: b :: rest)
      simp only [List.length_cons] at hlen hL ⊢
      show merkleFold f (merkleLevel (a :: b :: rest)) = merkleFold (rest.length + 1) (merkleLevel (a :: b :: rest))
      rw [ih f (by omega) _ (by omega), ih (rest.length + 1) (by omega) _ (by omega)]

theorem merkleFold_step (L : List NearSpec.Bytes) (h : 2 ≤ L.length) :
    merkleFold L.length L = merkleFold (merkleLevel L).length (merkleLevel L) := by
  match L, h with
  | a :: b :: rest, _ =>
    have hlen := merkleLevel_length (a :: b :: rest)
    simp only [List.length_cons] at hlen ⊢
    show merkleFold (rest.length + 1) (merkleLevel (a :: b :: rest)) = _
    rw [merkleFold_fuel _ _ (by omega)]

/-! ## Blocks of 32 bytes -/

theorem readMem_concatAll (M0 : Nat → UInt8) : ∀ (a : Nat) (L : List NearSpec.Bytes),
    (∀ x ∈ L, x.length = 32) →
    (readMem M0 a (32 * L.length) = concatAll L ↔ ∀ i < L.length, readMem M0 (a + 32 * i) 32 = L.getD i [])
  | a, [], _ => by simp [concatAll, readMem_zero]
  | a, x :: xs, hL => by
    have hx : x.length = 32 := hL x (by simp)
    have ih := readMem_concatAll M0 (a + 32) xs (fun y hy => hL y (by simp [hy]))
    simp only [List.length_cons, concatAll]
    rw [show 32 * (xs.length + 1) = 32 + 32 * xs.length by omega, readMem_add]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := List.append_inj h (by simp [hx])
      intro i hi
      cases i with
      | zero => simpa using h1
      | succ i =>
        simp only [List.getD_cons_succ]
        rw [show a + 32 * (i + 1) = a + 32 + 32 * i by omega]
        exact ih.mp h2 i (by omega)
    · intro h
      have h1 := h 0 (by omega)
      simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at h1
      rw [h1, ih.mpr (fun i hi => by
        have := h (i + 1) (by omega)
        rw [show a + 32 * (i + 1) = a + 32 + 32 * i by omega] at this
        simpa using this)]

/-! ## The Merkle loop -/

def finBlk (M0 : Nat → UInt8) (i : Nat) : NearSpec.Bytes := readMem M0 (OL + 32 * i) 32

theorem blk_write_out (M0 : Nat → UInt8) (d : Nat) (s : NearSpec.Bytes) (i : Nat)
    (h : OL + 32 * i + 32 ≤ d ∨ d + 32 ≤ OL + 32 * i) : finBlk (writeMem M0 d 32 s) i = finBlk M0 i :=
  readMem_writeMem_disjoint _ _ _ _ _ _ h

theorem blk_write_self (M0 : Nat → UInt8) (d : Nat) (s : NearSpec.Bytes) (i : Nat) (hd : d = OL + 32 * i)
    (hs : s.length = 32) : finBlk (writeMem M0 d 32 s) i = s := by
  subst hd
  simp only [finBlk]
  rw [readMem_writeMem_self _ _ _ _ (by omega), List.take_of_length_le (by omega)]

theorem frame_write {M0 mem0 : Nat → UInt8} (d : Nat) (s : NearSpec.Bytes)
    (h : ∀ a, a < OL ∨ OL + 8192 ≤ a → M0 a = mem0 a) (hd : OL ≤ d) (hd' : d + 32 ≤ OL + 8192) :
    ∀ a, a < OL ∨ OL + 8192 ≤ a → writeMem M0 d 32 s a = mem0 a := by
  intro a ha
  rw [writeMem_apply_out _ _ _ _ _ (by omega)]
  exact h a ha

/-- Inner-loop invariant: `j` pairs combined. -/
def FinMJ (L : List NearSpec.Bytes) (mem0 : Nat → UInt8) (j : Nat) (x : M) : Prop :=
  (∀ i < j, finBlk x.mem i = (merkleLevel L).getD i []) ∧
  (∀ i, 2 * j ≤ i → i < L.length → finBlk x.mem i = L.getD i []) ∧
  (∀ a, a < OL ∨ OL + 8192 ≤ a → x.mem a = mem0 a) ∧
  x.regs 0 = L.length ∧ x.regs 14 = 8 ∧ x.regs 15 = 1

theorem merkle_body_twp {pub cb pb : NearSpec.Bytes} {L : List NearSpec.Bytes} {mem0 : Nat → UInt8}
    (hn : L.length ≤ 256) {x : M} {j : Nat} (hj : j < L.length / 2) (hJ : FinMJ L mem0 j x)
    (h4 : x.regs 4 = j) (h3 : x.regs 3 = L.length / 2) :
    twp P (Inp pub cb pb) (seqs [CST 6 32, MUL 6 4 6, ADDI 6 6 OL, CST 7 64, MUL 7 4 7, ADDI 7 7 OL,
      CST 8 64, SHA 6 7 8]) x (fun x' c => FinMJ L mem0 (j + 1) x' ∧ x'.regs 4 = j ∧ x'.regs 3 = L.length / 2 ∧ c ≤ 12) := by
  obtain ⟨hlo, hhi, hfr, h0, h14, h15⟩ := hJ
  npai_vc [h4]
  have hpair : readMem x.mem (j * 64 + 19968) 64 = L.getD (2 * j) [] ++ L.getD (2 * j + 1) [] := by
    rw [show (64 : Nat) = 32 + 32 from rfl, readMem_add]
    have e1 := hhi (2 * j) (by omega) (by omega)
    have e2 := hhi (2 * j + 1) (by omega) (by omega)
    simp only [finBlk, OL] at e1 e2
    rw [show j * 64 + 19968 = 19968 + 32 * (2 * j) by omega, e1,
      show 19968 + 32 * (2 * j) + 32 = 19968 + 32 * (2 * j + 1) by omega, e2]
  rw [hpair]
  refine ⟨by omega, by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, h3⟩
  · intro i hi
    by_cases hij : i = j
    · subst hij
      rw [blk_write_self _ _ _ _ (by simp only [OL]; omega) (ArenaCore.sha256_length _),
        merkleLevel_getD L i hj]
    · rw [blk_write_out _ _ _ _ (by simp only [OL]; omega)]
      exact hlo i (by omega)
  · intro i hi hil
    rw [blk_write_out _ _ _ _ (by simp only [OL]; omega)]
    exact hhi i (by omega) hil
  · exact frame_write _ _ hfr (by simp only [OL]; omega) (by simp only [OL]; omega)
  · simp [setReg_apply, h0]
  · simp [setReg_apply, h14]
  · simp [setReg_apply, h15]

theorem evShr1' (x : Nat) (h : x < 18446744073709551616) : BinOp.shr.eval x 1 = x / 2 := by
  simp only [BinOp.eval, wordMod]
  rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem evAnd1' (x : Nat) : BinOp.and.eval x 1 = x % 2 := by
  simp only [BinOp.eval, Nat.and_one_is_mod]
  exact Nat.mod_eq_of_lt (by have := Nat.mod_lt x (show 2 > 0 by omega); unfold wordMod; omega)

/-- Outer-loop invariant. -/
def FinMI (L0 : List NearSpec.Bytes) (mem0 : Nat → UInt8) (x : M) : Prop :=
  ∃ L : List NearSpec.Bytes, L.length = x.regs 0 ∧ 1 ≤ L.length ∧ L.length ≤ 256 ∧
    (∀ y ∈ L, y.length = 32) ∧ (∀ i < L.length, finBlk x.mem i = L.getD i []) ∧
    merkleFold L.length L = merkleRoot L0 ∧ (∀ a, a < OL ∨ OL + 8192 ≤ a → x.mem a = mem0 a) ∧
    x.regs 2 = (if 1 < x.regs 0 then 1 else 0) ∧ x.regs 14 = 8 ∧ x.regs 15 = 1

theorem FinMI_next {L0 L : List NearSpec.Bytes} {mem0 : Nat → UInt8} {x' : M} (hn2 : 2 ≤ L.length)
    (h256 : L.length ≤ 256) (hall : ∀ y ∈ L, y.length = 32) (hfold : merkleFold L.length L = merkleRoot L0)
    (hb : ∀ i < (L.length + 1) / 2, finBlk x'.mem i = (merkleLevel L).getD i [])
    (hfr : ∀ a, a < OL ∨ OL + 8192 ≤ a → x'.mem a = mem0 a) (h0 : x'.regs 0 = (L.length + 1) / 2)
    (h2 : x'.regs 2 = if 1 < x'.regs 0 then 1 else 0) (h14 : x'.regs 14 = 8) (h15 : x'.regs 15 = 1) :
    FinMI L0 mem0 x' :=
  ⟨merkleLevel L, by rw [merkleLevel_length, h0], by rw [merkleLevel_length]; omega,
    by rw [merkleLevel_length]; omega, merkleLevel_all L hall, by rw [merkleLevel_length]; exact hb,
    by rw [← merkleFold_step L hn2]; exact hfold, hfr, h2, h14, h15⟩

theorem merkle_iter_twp {pub cb pb : NearSpec.Bytes} {L0 : List NearSpec.Bytes} {mem0 : Nat → UInt8} {x : M}
    (hI : FinMI L0 mem0 x) (h2 : x.regs 2 ≠ 0) :
    twp P (Inp pub cb pb) (seqs [
    SHR 3 0 15,
    CST 4 0,
    forUp 4 3 5 (seqs [CST 6 32, MUL 6 4 6, ADDI 6 6 OL, CST 7 64, MUL 7 4 7, ADDI 7 7 OL,
      CST 8 64, SHA 6 7 8]),
    AND 4 0 15,
    .ite 4 (seqs [CST 6 32, MUL 6 3 6, ADDI 6 6 OL, SUB 7 0 15, CST 8 32, MUL 7 7 8, ADDI 7 7 OL,
      CST 8 32, memcpy 6 7 8 9]) nop,
    ADD 0 3 4,
    CST 1 1, LTU 2 1 0]) x (fun x' c => FinMI L0 mem0 x' ∧ c + 2 + 400 * x'.regs 0 ≤ 400 * x.regs 0) := by
  obtain ⟨L, hlen, h1, h256, hall, hblk, hfold, hfr, hr2, h14, h15⟩ := hI
  have hn2 : 2 ≤ L.length := by
    by_cases h : 1 < x.regs 0
    · omega
    · simp [h] at hr2; exact absurd hr2 h2
  npai_vc [evShr1', h15, ← hlen]
  refine twp_forUp (J := FinMJ L mem0) (N := L.length / 2) (B := 12) (by decide) (by decide) (by decide)
    (by omega) ?_ ?_ (by simp [setReg_apply]) (by simp [setReg_apply]) ?_ ?_
  · intro j m v w ⟨a1, a2, a3, a4, a5, a6⟩
    exact ⟨a1, a2, a3, by simp [setReg_apply, a4], by simp [setReg_apply, a5], by simp [setReg_apply, a6]⟩
  · refine ⟨fun i hi => absurd hi (by omega), fun i _ hi => hblk i hi, hfr, ?_, ?_, ?_⟩ <;>
      simp [setReg_apply, h14, h15, hlen]
  · intro j m hj hJ hi hn
    exact merkle_body_twp h256 hj hJ hi hn
  · intro y c ⟨hlo, hhi, hfy, h0y, h14y, h15y⟩ h3y hc
    simp (disch := omega) only [h0y, h15y, h3y, evAnd1', evS, evM, evA, evAddi, setReg_apply]
    by_cases hodd : L.length % 2 = 1
    · right
      refine ⟨by omega, twp_of_spec (memcpy_spec (n := 32) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by simp [setReg_apply, h15y, K1]) (by simp [setReg_apply])
        (by simp [setReg_apply]; omega) (by simp [setReg_apply]; omega) (by simp) (by simp [setReg_apply]; omega)) ?_⟩
      rintro m2 c2 ⟨hmem, -, -, -, hfr2, hc2⟩
      have r3 : m2.regs 3 = L.length / 2 := by rw [hfr2 3 (by decide)]; simp [setReg_apply, h3y]
      have r4 : m2.regs 4 = 1 := by rw [hfr2 4 (by decide)]; simp [setReg_apply]; omega
      have r14 : m2.regs 14 = 8 := by rw [hfr2 14 (by decide)]; simp [setReg_apply, h14y]
      have r15 : m2.regs 15 = 1 := by rw [hfr2 15 (by decide)]; simp [setReg_apply, h15y]
      simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at hmem
      simp only [r3, r4]
      rw [evA _ _ (by omega)]
      refine ⟨FinMI_next hn2 h256 hall hfold ?_ ?_ (by simp [setReg_apply]; omega) (by simp [setReg_apply])
        (by simp [setReg_apply, r14]) (by simp [setReg_apply, r15]), by omega⟩
      · intro i hi
        simp only [hmem]
        by_cases hin : i = L.length / 2
        · subst hin
          rw [blk_write_self _ _ _ _ (by simp only [OL]; omega) (by simp),
            merkleLevel_getD_odd L hodd]
          have := hhi (L.length - 1) (by omega) (by omega)
          simp only [finBlk, OL] at this ⊢
          rw [show (L.length - 1) * 32 + 19968 = 19968 + 32 * (L.length - 1) by omega, this]
        · rw [blk_write_out _ _ _ _ (by simp only [OL]; omega)]
          exact hlo i (by omega)
      · simp only [hmem]
        exact frame_write _ _ hfy (by simp only [OL]; omega) (by simp only [OL]; omega)
    · left
      refine ⟨by omega, FinMI_next hn2 h256 hall hfold ?_ hfy (by simp [setReg_apply]; omega)
        (by simp [setReg_apply]) (by simp [setReg_apply, h14y]) (by simp [setReg_apply, h15y]), by omega⟩
      intro i hi
      exact hlo i (by omega)

theorem merkle_twp {pub cb pb : NearSpec.Bytes} {L0 : List NearSpec.Bytes} {m : M} (h14 : m.regs 14 = 8)
    (h15 : m.regs 15 = 1) (hn : rd32 m C_N = L0.length) (h1 : 1 ≤ L0.length) (h256 : L0.length ≤ 256)
    (hall : ∀ y ∈ L0, y.length = 32) (hb : readMem m.mem OL (32 * L0.length) = concatAll L0) :
    twp P (Inp pub cb pb) pMerkle m (fun m' c => readMem m'.mem OL 32 = merkleRoot L0 ∧ m'.regs 14 = 8 ∧
      m'.regs 15 = 1 ∧ (∀ a, a < OL ∨ OL + 8192 ≤ a → m'.mem a = m.mem a) ∧ c ≤ 110000) := by
  have hb' := (readMem_concatAll m.mem OL L0 hall).mp hb
  simp only [rd32, C_N] at hn
  simp only [pMerkle, ldCell]
  npai_vc [h14, hn]
  refine twp_loop (I := FinMI L0 m.mem) (Pot := fun x => 400 * x.regs 0) ?_ ?_ ?_
  · refine ⟨L0, by simp [setReg_apply], h1, h256, hall, hb', rfl, fun a _ => rfl, ?_, ?_, ?_⟩ <;>
      simp [setReg_apply, h14, h15]
  · intro x hI h2
    exact merkle_iter_twp hI h2
  · intro x c ⟨L, hlen, hl1, _, _, hblk, hfold, hfr, hr2, hx14, hx15⟩ h2 hc
    have hL1 : L.length = 1 := by
      by_cases h : 1 < x.regs 0
      · simp [h] at hr2; omega
      · omega
    match L, hL1 with
    | [y], _ =>
      have := hblk 0 (by simp)
      simp only [finBlk, Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at this
      refine ⟨?_, hx14, hx15, hfr, ?_⟩
      · rw [show (19968 : Nat) = OL from rfl, this, ← hfold]; rfl
      · simp only [setReg_apply] at hc; simp at hc hlen; omega


/-! ## Straight-line tail -/

theorem wp_seqs_append {p : Program} {inp : Inputs} : ∀ (a b : List Stmt) (m : M) (Q : M → Prop), a ≠ [] → b ≠ [] →
    (wp p inp (seqs (a ++ b)) m Q ↔ wp p inp (seqs a) m (fun m1 => wp p inp (seqs b) m1 Q))
  | [], _, _, _, h, _ => absurd rfl h
  | [x], b, m, Q, _, hb => by
    match b, hb with
    | y :: b', _ => simp only [List.cons_append, List.nil_append, seqs, wp_seq]
  | x :: y :: rest, b, m, Q, _, hb => by
    have ih := fun m => wp_seqs_append (p := p) (inp := inp) (y :: rest) b m Q (by simp) hb
    show wp p inp (.seq x (seqs (y :: rest ++ b))) m Q ↔ wp p inp (.seq x (seqs (y :: rest))) m _
    rw [wp_seq, wp_seq]
    exact ⟨fun h => wp_mono h (fun m1 h1 => (ih m1).mp h1), fun h => wp_mono h (fun m1 h1 => (ih m1).mpr h1)⟩

theorem twp_seqs_append {p : Program} {inp : Inputs} : ∀ (a b : List Stmt) (m : M) (Q : M → Nat → Prop),
    a ≠ [] → b ≠ [] → (twp p inp (seqs (a ++ b)) m Q ↔
      twp p inp (seqs a) m (fun m1 c1 => twp p inp (seqs b) m1 (fun m2 c2 => Q m2 (c1 + c2))))
  | [], _, _, _, h, _ => absurd rfl h
  | [x], b, m, Q, _, hb => by
    match b, hb with
    | y :: b', _ => simp only [List.cons_append, List.nil_append, seqs, twp_seq]
  | x :: y :: rest, b, m, Q, _, hb => by
    have ih := fun m (Q : M → Nat → Prop) => twp_seqs_append (p := p) (inp := inp) (y :: rest) b m Q (by simp) hb
    show twp p inp (.seq x (seqs (y :: rest ++ b))) m Q ↔ twp p inp (.seq x (seqs (y :: rest))) m _
    rw [twp_seq, twp_seq]
    constructor
    · intro h
      refine twp_mono h (fun m1 c1 h1 => ?_)
      have := (ih m1 _).mp h1
      refine twp_mono this (fun m2 c2 h2 => twp_mono h2 (fun m3 c3 h3 => ?_))
      rw [Nat.add_assoc]; exact h3
    · intro h
      refine twp_mono h (fun m1 c1 h1 => ?_)
      refine (ih m1 _).mpr (twp_mono h1 (fun m2 c2 h2 => twp_mono h2 (fun m3 c3 h3 => ?_)))
      rw [← Nat.add_assoc]; exact h3

def tA1 : List Stmt := [CST 0 OL, CST 1 (CLM + 217), CST 2 32, MEMEQ 3 0 1 2, assert 3,
  ldCell 0 C_NREF, CST 4 (CLM + 249), ld32 1 4, eqc 0 1]
def tA2 : List Stmt := [CST 1 RB, st32 1 0, ldCell 2 C_RBEND, SUB 3 2 1, CST 4 S_H, SHA 4 1 3,
  CST 1 (CLM + 253), CST 2 32, MEMEQ 3 4 1 2, assert 3]
def tB : List Stmt := [ldCell 0 C_N, ldConst64 1 D_G, MUL 0 0 1, CST 4 (CLM + 285), ld64 1 4, eqc 0 1,
  CST 0 C_TOK, CST 1 (CLM + 293), CST 2 16, MEMEQ 3 0 1 2, assert 3]

theorem pFinal_eq : pFinal = seqs ([pHash, pRootIs (CLM + 185), pMerkle] ++ (tA1 ++ (tA2 ++ tB))) := rfl

section
variable {pub cb pb : NearSpec.Bytes}

theorem tA1_wp {m : M} (h14 : m.regs 14 = 8) (h15 : m.regs 15 = 1) :
    wp P (Inp pub cb pb) (seqs tA1) m (fun m' => readMem m.mem OL 32 = readMem m.mem (CLM + 217) 32 ∧
      rd32 m C_NREF = Bytes.leToNat (readMem m.mem (CLM + 249) 4) ∧ m'.regs 0 = rd32 m C_NREF ∧
      m'.mem = m.mem ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [tA1, ldCell]
  npai_auto [h14, h15]
  simp only [rd32, and_true]
  exact ⟨‹_›, ‹_›⟩

theorem tA1_twp {m : M} (h14 : m.regs 14 = 8) (h15 : m.regs 15 = 1)
    (hO : readMem m.mem OL 32 = readMem m.mem (CLM + 217) 32)
    (hK : rd32 m C_NREF = Bytes.leToNat (readMem m.mem (CLM + 249) 4)) :
    twp P (Inp pub cb pb) (seqs tA1) m (fun m' c => m'.regs 0 = rd32 m C_NREF ∧
      m'.mem = m.mem ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 100) := by
  simp only [rd32, OL, CLM, C_NREF] at hO hK ⊢
  simp only [tA1, ldCell]
  npai_auto [h14, h15, hO, hK]

theorem tA2_wp {m : M} {E : NearSpec.Bytes} (h14 : m.regs 14 = 8) (h15 : m.regs 15 = 1)
    (h0 : m.regs 0 < 4294967296) (hrb : rd32 m C_RBEND = RB + 4 + E.length)
    (hE : readMem m.mem (RB + 4) E.length = E) :
    wp P (Inp pub cb pb) (seqs tA2) m (fun m' =>
      ArenaCore.sha256 (Bytes.leN 4 (m.regs 0) ++ E) = readMem m.mem (CLM + 253) 32 ∧
      (∀ a, a < RB ∨ RB + 4 ≤ a → a < S_H ∨ S_H + 32 ≤ a → m'.mem a = m.mem a) ∧
      m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [rd32, C_RBEND, RB] at hrb hE
  simp only [tA2, ldCell]
  npai_auto [h14, h15, h0, readMem_writeMem_disjoint, hrb]
  rename_i _ heq
  have hkey : readMem (writeMem m.mem 28160 4 (Bytes.leN 4 (m.regs 0))) 28160 (28164 + E.length - 28160) =
      Bytes.leN 4 (m.regs 0) ++ E := by
    rw [show 28164 + E.length - 28160 = 4 + E.length by omega, readMem_add,
      readMem_writeMem_self _ _ _ _ (by simp [Bytes.leN_length]), List.take_of_length_le (by simp [Bytes.leN_length]),
      readMem_writeMem_disjoint _ _ _ _ _ _ (by omega), hE]
  rw [hkey, readMem_writeMem_self _ _ _ _ (by simp [ArenaCore.sha256_length]),
    List.take_of_length_le (by simp [ArenaCore.sha256_length])] at heq
  refine ⟨heq, fun a h1 h2 => ?_⟩
  rw [writeMem_apply_out _ _ _ _ _ (by omega), writeMem_apply_out _ _ _ _ _ (by omega)]

theorem tA2_twp {m : M} {E : NearSpec.Bytes} (h14 : m.regs 14 = 8) (h15 : m.regs 15 = 1)
    (h0 : m.regs 0 < 4294967296) (hrb : rd32 m C_RBEND = RB + 4 + E.length)
    (hE : readMem m.mem (RB + 4) E.length = E) (hcap : RB + 4 + E.length ≤ AR)
    (hS : ArenaCore.sha256 (Bytes.leN 4 (m.regs 0) ++ E) = readMem m.mem (CLM + 253) 32) :
    twp P (Inp pub cb pb) (seqs tA2) m (fun m' c =>
      (∀ a, a < RB ∨ RB + 4 ≤ a → a < S_H ∨ S_H + 32 ≤ a → m'.mem a = m.mem a) ∧
      m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 3000) := by
  simp only [rd32, C_RBEND, RB, AR, CLM] at hrb hE hcap hS
  have hkey : readMem (writeMem m.mem 28160 4 (Bytes.leN 4 (m.regs 0))) 28160 (28164 + E.length - 28160) =
      Bytes.leN 4 (m.regs 0) ++ E := by
    rw [show 28164 + E.length - 28160 = 4 + E.length by omega, readMem_add,
      readMem_writeMem_self _ _ _ _ (by simp [Bytes.leN_length]), List.take_of_length_le (by simp [Bytes.leN_length]),
      readMem_writeMem_disjoint _ _ _ _ _ _ (by omega), hE]
  have hS' : readMem (writeMem (writeMem m.mem 28160 4 (Bytes.leN 4 (m.regs 0))) 1408 32
      (ArenaCore.sha256 (readMem (writeMem m.mem 28160 4 (Bytes.leN 4 (m.regs 0))) 28160
        (28164 + E.length - 28160)))) 1408 32 = readMem m.mem 2813 32 := by
    rw [hkey, readMem_writeMem_self _ _ _ _ (by simp [ArenaCore.sha256_length]),
      List.take_of_length_le (by simp [ArenaCore.sha256_length])]
    exact hS
  simp only [tA2, ldCell]
  npai_auto [h14, h15, h0, readMem_writeMem_disjoint, hrb, hS']
  refine ⟨by omega, fun a h1 h2 => ?_, by omega⟩
  rw [writeMem_apply_out _ _ _ _ _ (by omega), writeMem_apply_out _ _ _ _ _ (by omega)]

theorem tB_wp0 {m : M} (h14 : m.regs 14 = 8) (h15 : m.regs 15 = 1) :
    wp P (Inp pub cb pb) (seqs tB) m (fun m' =>
      BinOp.mul.eval (Bytes.leToNat (readMem m.mem C_N 4)) (Bytes.leToNat (readMem m.mem D_G 8)) =
        Bytes.leToNat (readMem m.mem (CLM + 285) 8) ∧
      readMem m.mem C_TOK 16 = readMem m.mem (CLM + 293) 16 ∧ m'.regs 15 = 1) := by
  simp only [tB, ldCell, ldConst64, C_N, D_G, CLM, C_TOK, Nat.reduceAdd]
  npai_auto [h14, h15]
  rename_i a b
  exact ⟨a, b⟩

theorem tB_twp0 {m : M} (h14 : m.regs 14 = 8) (h15 : m.regs 15 = 1)
    (hg : BinOp.mul.eval (Bytes.leToNat (readMem m.mem C_N 4)) (Bytes.leToNat (readMem m.mem D_G 8)) =
        Bytes.leToNat (readMem m.mem (CLM + 285) 8))
    (ht : readMem m.mem C_TOK 16 = readMem m.mem (CLM + 293) 16) :
    twp P (Inp pub cb pb) (seqs tB) m (fun m' c => m'.regs 15 = 1 ∧ c ≤ 200) := by
  simp only [C_N, D_G, CLM, C_TOK] at hg ht
  simp only [tB, ldCell, ldConst64]
  npai_auto [h14, h15, hg, ht]

end

/-! ## The root comparison (local copy for `CLM + 185`) -/

section
variable {pub cb pb : NearSpec.Bytes}
theorem fin_rootIs_wp {m : M} {d : NearSpec.Bytes} (hk : Base m) (hd : readMem m.mem C_ROOT 32 = d) :
    wp P (Inp pub cb pb) (pRootIs (CLM + 185)) m (fun m' => d = readMem m.mem (CLM + 185) 32 ∧ m'.mem = m.mem ∧
      m'.regs 14 = 8 ∧ m'.regs 15 = 1) := by
  simp only [C_ROOT] at hd
  simp only [pRootIs]
  npai_auto [hk.k1, hk.k8]
  rename_i h
  rw [← hd, h]

theorem fin_rootIs_twp {m : M} {d : NearSpec.Bytes} (hk : Base m) (hd : readMem m.mem C_ROOT 32 = d)
    (he : d = readMem m.mem (CLM + 185) 32) :
    twp P (Inp pub cb pb) (pRootIs (CLM + 185)) m (fun m' c => m'.mem = m.mem ∧ m'.regs 14 = 8 ∧
      m'.regs 15 = 1 ∧ c ≤ 20) := by
  simp only [C_ROOT, CLM] at hd he
  have h' : readMem m.mem 3136 32 = readMem m.mem 2745 32 := by rw [hd, he]
  simp only [pRootIs]
  npai_auto [hk.k1, hk.k8, h']
end

/-! ## Composition (conditional on the hash-pass frame and the refund-buffer bound) -/

theorem fin_leToNat_leNat : ∀ l : NearSpec.Bytes, Bytes.leToNat l = NearSpec.leNat l
  | [] => rfl
  | x :: xs => by simp [Bytes.leToNat, NearSpec.leNat, fin_leToNat_leNat xs]

theorem fin_leN_eq : ∀ (w x : Nat), Bytes.leN w x = NearSpec.leN w x
  | 0, _ => rfl
  | w + 1, x => by simp [Bytes.leN, NearSpec.leN, fin_leN_eq w]

theorem fin_leNat_leN (w x : Nat) (h : x < 256 ^ w) : NearSpec.leNat (NearSpec.leN w x) = x := by
  rw [← fin_leN_eq, ← fin_leToNat_leNat]; exact leToNat_leN w x h

theorem fin_claim_seg {cb : NearSpec.Bytes} {m : M} (h : ClaimIn cb m) (o n : Nat) (hn : o + n ≤ 309) :
    readMem m.mem (CLM + o) n = seg cb o n := by
  have := h.claim
  apply List.ext_getElem (by simp [seg]; have := h.shape.1; omega)
  intro i h1 h2
  simp only [readMem_length] at h1
  rw [readMem_getElem]
  have h3 := mem_of_readMem this (o + i) (by omega)
  rw [Nat.add_assoc, h3]
  have hl := h.shape.1
  simp [seg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show o + i < cb.length by omega)]

theorem fin_rd_eq {M1 M2 : Nat → UInt8} {a n : Nat} (h : ∀ i, a ≤ i → i < a + n → M1 i = M2 i) :
    readMem M1 a n = readMem M2 a n := readMem_congr (fun i hi => h _ (by omega) (by omega))

theorem fin_sub {M0 : Nat → UInt8} {a n : Nat} {l : NearSpec.Bytes} (h : readMem M0 a n = l) (o k : Nat)
    (hk : o + k ≤ n) : readMem M0 (a + o) k = (l.drop o).take k := by
  subst h
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp [readMem, Nat.add_assoc]

theorem fin_dataG : (dataSeg.drop 120).take 8 = u64 Params.G := by decide

theorem u128_leNat_fin (l : NearSpec.Bytes) (h : l.length = 16) : NearSpec.u128 (NearSpec.leNat l) = l := by
  have := leN_leNat l; rw [h] at this; exact this

section
variable {pub cb pb : NearSpec.Bytes}

theorem final_wp_of {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → NearSpec.Bytes}
    {acc : Acc} (h : TrieSt cb pb rs R A K vals m) (hb : BatchMem acc m) (ht : rootT A K vals = acc.trie)
    (hlen : acc.outcomes.length = rs.length) (hgas : acc.gasBurnt = rs.length * Params.G)
    (htok : acc.tokensBurnt < Params.two128)
    (hcap : RB + 4 + (concatAll (acc.refunds.map Receipt.encode)).length ≤ AR)
    (hH : wp P (Inp pub cb pb) pHash m (fun m' => TrieSt cb pb rs R A K vals m' ∧
      readMem m'.mem C_ROOT 32 = (rootT A K vals).hashOf ∧ HashFrame m m')) :
    wp P (Inp pub cb pb) pFinal m (fun m' => Outputs.ofAcc acc = Outputs.ofClaim (claimOf cb) ∧
      m'.regs 15 = 1) := by
  have hmax := h.ok.n_max
  have hpos := h.ok.n_pos
  simp only [Params.maxBatch] at hmax
  rw [pFinal_eq, wp_seqs_append _ _ _ _ (by simp) (by simp [tA1, tA2, tB])]
  simp only [seqs, wp_seq]
  refine wp_mono hH fun m1 ⟨h1, hr1, hf1⟩ => ?_
  refine wp_mono (fin_rootIs_wp h1.toBase hr1) fun m2 ⟨heq, hm2, h142, h152⟩ => ?_
  have hn2 : rd32 m2 C_N = (acc.outcomes.map Outcome.leaf).length := by
    simp only [List.length_map, hlen]; rw [← h1.nC]; simp only [rd32, hm2]
  have hL2 : readMem m2.mem OL (32 * (acc.outcomes.map Outcome.leaf).length) =
      concatAll (acc.outcomes.map Outcome.leaf) := by
    rw [hm2, ← hb.leaves, List.length_map]
    exact fin_rd_eq fun i h1 h2 => hf1 i (by simp only [OL, PF] at *; omega) (by simp only [OL, C_ROOT] at *; omega)
  have hall : ∀ y ∈ acc.outcomes.map Outcome.leaf, y.length = 32 := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨o, -, rfl⟩ := hy
    exact ArenaCore.sha256_length _
  refine wp_of_spec (merkle_twp h142 h152 hn2 (by simp; omega) (by simp; omega) hall hL2)
    fun m3 c3 ⟨hroot, h143, h153, hfr3, _⟩ => ?_
  -- memory of `m3` below `PF`
  have F3 : ∀ a, a < PF → (a < C_ROOT ∨ C_ROOT + 32 ≤ a) → (a < OL ∨ OL + 8192 ≤ a) → m3.mem a = m.mem a := by
    intro a ha hb' hc
    rw [hfr3 a hc, hm2, hf1 a ha hb']
  have F3' : ∀ a, a < PF → (a < C_ROOT ∨ C_ROOT + 32 ≤ a) → (a < OL ∨ OL + 8192 ≤ a) → m3.mem a = m1.mem a := by
    intro a ha hb' hc
    rw [hfr3 a hc, hm2]
  rw [wp_seqs_append tA1 _ _ _ (by simp [tA1]) (by simp [tA2, tB])]
  refine wp_mono (tA1_wp h143 h153) fun m4 ⟨hO, hK, h04, hm4, h144, h154⟩ => ?_
  have hcl : ∀ o n, o + n ≤ 309 → ∀ M0 : Nat → UInt8, (∀ a, CLM ≤ a → a < CLM + 309 → M0 a = m1.mem a) →
      readMem M0 (CLM + o) n = seg cb o n := by
    intro o n hon M0 hM
    rw [← fin_claim_seg h1.toClaimIn o n hon]
    exact fin_rd_eq fun i h1 h2 => hM i (by omega) (by omega)
  have hnref3 : rd32 m3 C_NREF = acc.refunds.length := by
    rw [← hb.nref]
    simp only [rd32]
    rw [fin_rd_eq (a := C_NREF) (n := 4) fun i h1 h2 => F3 i (by simp only [C_NREF, PF] at *; omega)
      (by simp only [C_NREF, C_ROOT] at *; omega) (by simp only [C_NREF, OL] at *; omega)]
  have hm4' : ∀ a, a < PF → (a < C_ROOT ∨ C_ROOT + 32 ≤ a) → (a < OL ∨ OL + 8192 ≤ a) → m4.mem a = m.mem a := by
    intro a h1 h2 h3; rw [hm4]; exact F3 a h1 h2 h3
  have hrb4 : rd32 m4 C_RBEND = RB + 4 + (concatAll (acc.refunds.map Receipt.encode)).length := by
    rw [← hb.refunds.1]
    simp only [rd32]
    rw [fin_rd_eq (a := C_RBEND) (n := 4) fun i h1 h2 => hm4' i (by simp only [C_RBEND, PF] at *; omega)
      (by simp only [C_RBEND, C_ROOT] at *; omega) (by simp only [C_RBEND, OL] at *; omega)]
  have hE4 : readMem m4.mem (RB + 4) (concatAll (acc.refunds.map Receipt.encode)).length =
      concatAll (acc.refunds.map Receipt.encode) := by
    refine (fin_rd_eq fun i h1 h2 => hm4' i (by simp only [RB, AR, PF] at *; omega)
      (by simp only [RB, C_ROOT] at *; omega) (by simp only [RB, OL] at *; omega)).trans hb.refunds.2
  have h04' : m4.regs 0 < 4294967296 := by
    rw [h04]; have := leToNat_readMem_lt m3.mem C_NREF 4; simp only [rd32]; omega
  rw [wp_seqs_append tA2 tB _ _ (by simp [tA2]) (by simp [tB])]
  refine wp_mono (tA2_wp h144 h154 h04' hrb4 hE4) fun m5 ⟨hS, hfr5, h145, h155⟩ => ?_
  refine wp_mono (tB_wp0 h145 h155) fun m6 ⟨hg, htk, h156⟩ => ?_
  refine ⟨?_, h156⟩
  have F5 : ∀ a, a < PF → (a < C_ROOT ∨ C_ROOT + 32 ≤ a) → (a < OL ∨ OL + 8192 ≤ a) →
      (a < RB ∨ RB + 4 ≤ a) → (a < S_H ∨ S_H + 32 ≤ a) → m5.mem a = m.mem a := by
    intro a h1 h2 h3 h4 h5; rw [hfr5 a h4 h5]; exact hm4' a h1 h2 h3
  have F5' : ∀ a, a < PF → (a < C_ROOT ∨ C_ROOT + 32 ≤ a) → (a < OL ∨ OL + 8192 ≤ a) →
      (a < RB ∨ RB + 4 ≤ a) → (a < S_H ∨ S_H + 32 ≤ a) → m5.mem a = m1.mem a := by
    intro a h1 h2 h3 h4 h5; rw [hfr5 a h4 h5, hm4]; exact F3' a h1 h2 h3
  simp only [Outputs.ofAcc, Outputs.ofClaim, claimOf, Outputs.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← ht, heq, fin_claim_seg h1.toClaimIn 185 32 (by decide)]
  · show merkleRoot (acc.outcomes.map Outcome.leaf) = _
    rw [← hroot, hO]
    exact hcl 217 32 (by decide) _ fun a h1 h2 => F3' a (by simp only [CLM, PF] at *; omega)
      (by simp only [CLM, C_ROOT] at *; omega) (by simp only [CLM, OL] at *; omega)
  · rw [← hnref3, hK, hcl 249 4 (by decide) _ fun a h1 h2 => F3' a (by simp only [CLM, PF] at *; omega)
      (by simp only [CLM, C_ROOT] at *; omega) (by simp only [CLM, OL] at *; omega), fin_leToNat_leNat]
  · rw [h04, hnref3, hm4, hcl 253 32 (by decide) _ fun a h1 h2 => F3' a (by simp only [CLM, PF] at *; omega)
      (by simp only [CLM, C_ROOT] at *; omega) (by simp only [CLM, OL] at *; omega)] at hS
    rw [← hS]
    simp only [refundsCommitment, encodeReceipts, u32, fin_leN_eq]
  · have hN : Bytes.leToNat (readMem m5.mem C_N 4) = rs.length := by
      rw [← h1.nC]; simp only [rd32]
      rw [fin_rd_eq (a := C_N) (n := 4) fun i h1 h2 => F5' i (by simp only [C_N, PF] at *; omega)
        (by simp only [C_N, C_ROOT] at *; omega) (by simp only [C_N, OL] at *; omega)
        (by simp only [C_N, RB] at *; omega) (by simp only [C_N, S_H] at *; omega)]
    have hD : Bytes.leToNat (readMem m5.mem D_G 8) = Params.G := by
      rw [fin_rd_eq (a := D_G) (n := 8) fun i h1 h2 => F5' i (by simp only [D_G, PF] at *; omega)
        (by simp only [D_G, C_ROOT] at *; omega) (by simp only [D_G, OL] at *; omega)
        (by simp only [D_G, RB] at *; omega) (by simp only [D_G, S_H] at *; omega)]
      have := fin_sub h1.toBase.data 120 8 (by decide)
      simp only [Nat.zero_add] at this
      rw [show D_G = 120 from rfl, this, fin_dataG, u64, ← fin_leN_eq, leToNat_leN 8 _ (by decide)]
    have hP : Params.G = 223182562500 := by simp only [Params.G, Params.newActionReceiptExec, Params.transferExec]
    rw [hN, hD, hP, evM _ _ (by omega), hcl 285 8 (by decide) _ fun a h1 h2 => F5' a
      (by simp only [CLM, PF] at *; omega) (by simp only [CLM, C_ROOT] at *; omega)
      (by simp only [CLM, OL] at *; omega) (by simp only [CLM, RB] at *; omega)
      (by simp only [CLM, S_H] at *; omega), fin_leToNat_leNat] at hg
    rw [hgas, hP, hg]
  · rw [hcl 293 16 (by decide) _ fun a h1 h2 => F5' a
      (by simp only [CLM, PF] at *; omega) (by simp only [CLM, C_ROOT] at *; omega)
      (by simp only [CLM, OL] at *; omega) (by simp only [CLM, RB] at *; omega)
      (by simp only [CLM, S_H] at *; omega)] at htk
    rw [fin_rd_eq (a := C_TOK) (n := 16) fun i h1 h2 => F5 i (by simp only [C_TOK, PF] at *; omega)
      (by simp only [C_TOK, C_ROOT] at *; omega) (by simp only [C_TOK, OL] at *; omega)
      (by simp only [C_TOK, RB] at *; omega) (by simp only [C_TOK, S_H] at *; omega), hb.tokens] at htk
    rw [← htk, u128, fin_leNat_leN 16 _ htok]
theorem final_twp_of {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → NearSpec.Bytes}
    {acc : Acc} (h : TrieSt cb pb rs R A K vals m) (hb : BatchMem acc m) (ht : rootT A K vals = acc.trie)
    (hlen : acc.outcomes.length = rs.length) (hgas : acc.gasBurnt = rs.length * Params.G)
    (htok : acc.tokensBurnt < Params.two128) (he : Outputs.ofAcc acc = Outputs.ofClaim (claimOf cb))
    (hcap : RB + 4 + (concatAll (acc.refunds.map Receipt.encode)).length ≤ AR)
    (hH : twp P (Inp pub cb pb) pHash m (fun m' c => TrieSt cb pb rs R A K vals m' ∧
      readMem m'.mem C_ROOT 32 = (rootT A K vals).hashOf ∧ HashFrame m m' ∧ c ≤ 20 * pb.length + 10000)) :
    twp P (Inp pub cb pb) pFinal m (fun m' c => m'.regs 15 = 1 ∧ c ≤ 20 * pb.length + 1000000) := by
  have hmax := h.ok.n_max
  have hpos := h.ok.n_pos
  simp only [Params.maxBatch] at hmax
  simp only [Outputs.ofAcc, Outputs.ofClaim, claimOf, Outputs.mk.injEq] at he
  obtain ⟨eT, eO, eN, eC, eG, eTk⟩ := he
  rw [pFinal_eq, twp_seqs_append _ _ _ _ (by simp) (by simp [tA1, tA2, tB])]
  simp only [seqs, twp_seq]
  refine twp_mono hH fun m1 c1 ⟨h1, hr1, hf1, hc1⟩ => ?_
  have hd1 : (rootT A K vals).hashOf = readMem m1.mem (CLM + 185) 32 := by
    rw [fin_claim_seg h1.toClaimIn 185 32 (by decide), ht, eT]
  refine twp_mono (fin_rootIs_twp h1.toBase hr1 hd1) fun m2 c2 ⟨hm2, h142, h152, hc2⟩ => ?_
  have hn2 : rd32 m2 C_N = (acc.outcomes.map Outcome.leaf).length := by
    simp only [List.length_map, hlen]; rw [← h1.nC]; simp only [rd32, hm2]
  have hL2 : readMem m2.mem OL (32 * (acc.outcomes.map Outcome.leaf).length) =
      concatAll (acc.outcomes.map Outcome.leaf) := by
    rw [hm2, ← hb.leaves, List.length_map]
    exact fin_rd_eq fun i h1 h2 => hf1 i (by simp only [OL, PF] at *; omega) (by simp only [OL, C_ROOT] at *; omega)
  have hall : ∀ y ∈ acc.outcomes.map Outcome.leaf, y.length = 32 := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨o, -, rfl⟩ := hy
    exact ArenaCore.sha256_length _
  refine twp_mono (merkle_twp h142 h152 hn2 (by simp; omega) (by simp; omega) hall hL2)
    fun m3 c3 ⟨hroot, h143, h153, hfr3, hc3⟩ => ?_
  have F3 : ∀ a, a < PF → (a < C_ROOT ∨ C_ROOT + 32 ≤ a) → (a < OL ∨ OL + 8192 ≤ a) → m3.mem a = m.mem a := by
    intro a ha hb' hc
    rw [hfr3 a hc, hm2, hf1 a ha hb']
  have F3' : ∀ a, a < PF → (a < C_ROOT ∨ C_ROOT + 32 ≤ a) → (a < OL ∨ OL + 8192 ≤ a) → m3.mem a = m1.mem a := by
    intro a ha hb' hc
    rw [hfr3 a hc, hm2]
  have hcl : ∀ o n, o + n ≤ 309 → ∀ M0 : Nat → UInt8, (∀ a, CLM ≤ a → a < CLM + 309 → M0 a = m1.mem a) →
      readMem M0 (CLM + o) n = seg cb o n := by
    intro o n hon M0 hM
    rw [← fin_claim_seg h1.toClaimIn o n hon]
    exact fin_rd_eq fun i h1 h2 => hM i (by omega) (by omega)
  have hcl3 : ∀ a, CLM ≤ a → a < CLM + 309 → m3.mem a = m1.mem a := fun a h1 h2 =>
    F3' a (by simp only [CLM, PF] at *; omega) (by simp only [CLM, C_ROOT] at *; omega)
      (by simp only [CLM, OL] at *; omega)
  have hnref3 : rd32 m3 C_NREF = acc.refunds.length := by
    rw [← hb.nref]
    simp only [rd32]
    rw [fin_rd_eq (a := C_NREF) (n := 4) fun i h1 h2 => F3 i (by simp only [C_NREF, PF] at *; omega)
      (by simp only [C_NREF, C_ROOT] at *; omega) (by simp only [C_NREF, OL] at *; omega)]
  have hO : readMem m3.mem OL 32 = readMem m3.mem (CLM + 217) 32 := by
    rw [hroot, hcl 217 32 (by decide) _ hcl3]; exact eO
  have hK : rd32 m3 C_NREF = Bytes.leToNat (readMem m3.mem (CLM + 249) 4) := by
    rw [hnref3, hcl 249 4 (by decide) _ hcl3, fin_leToNat_leNat, eN]
  rw [twp_seqs_append tA1 _ _ _ (by simp [tA1]) (by simp [tA2, tB])]
  refine twp_mono (tA1_twp h143 h153 hO hK) fun m4 c4 ⟨h04, hm4, h144, h154, hc4⟩ => ?_
  have hm4' : ∀ a, a < PF → (a < C_ROOT ∨ C_ROOT + 32 ≤ a) → (a < OL ∨ OL + 8192 ≤ a) → m4.mem a = m.mem a := by
    intro a h1 h2 h3; rw [hm4]; exact F3 a h1 h2 h3
  have hrb4 : rd32 m4 C_RBEND = RB + 4 + (concatAll (acc.refunds.map Receipt.encode)).length := by
    rw [← hb.refunds.1]
    simp only [rd32]
    rw [fin_rd_eq (a := C_RBEND) (n := 4) fun i h1 h2 => hm4' i (by simp only [C_RBEND, PF] at *; omega)
      (by simp only [C_RBEND, C_ROOT] at *; omega) (by simp only [C_RBEND, OL] at *; omega)]
  have hE4 : readMem m4.mem (RB + 4) (concatAll (acc.refunds.map Receipt.encode)).length =
      concatAll (acc.refunds.map Receipt.encode) := by
    refine (fin_rd_eq fun i h1 h2 => hm4' i (by simp only [RB, AR, PF] at *; omega)
      (by simp only [RB, C_ROOT] at *; omega) (by simp only [RB, OL] at *; omega)).trans hb.refunds.2
  have h04' : m4.regs 0 < 4294967296 := by
    rw [h04]; have := leToNat_readMem_lt m3.mem C_NREF 4; simp only [rd32]; omega
  have hS : ArenaCore.sha256 (Bytes.leN 4 (m4.regs 0) ++ concatAll (acc.refunds.map Receipt.encode)) =
      readMem m4.mem (CLM + 253) 32 := by
    rw [h04, hnref3, hm4, hcl 253 32 (by decide) _ hcl3, ← eC]
    simp only [refundsCommitment, encodeReceipts, u32, fin_leN_eq]
  rw [twp_seqs_append tA2 tB _ _ (by simp [tA2]) (by simp [tB])]
  refine twp_mono (tA2_twp h144 h154 h04' hrb4 hE4 hcap hS) fun m5 c5 ⟨hfr5, h145, h155, hc5⟩ => ?_
  have F5 : ∀ a, a < PF → (a < C_ROOT ∨ C_ROOT + 32 ≤ a) → (a < OL ∨ OL + 8192 ≤ a) →
      (a < RB ∨ RB + 4 ≤ a) → (a < S_H ∨ S_H + 32 ≤ a) → m5.mem a = m.mem a := by
    intro a h1 h2 h3 h4 h5; rw [hfr5 a h4 h5]; exact hm4' a h1 h2 h3
  have F5' : ∀ a, a < PF → (a < C_ROOT ∨ C_ROOT + 32 ≤ a) → (a < OL ∨ OL + 8192 ≤ a) →
      (a < RB ∨ RB + 4 ≤ a) → (a < S_H ∨ S_H + 32 ≤ a) → m5.mem a = m1.mem a := by
    intro a h1 h2 h3 h4 h5; rw [hfr5 a h4 h5, hm4]; exact F3' a h1 h2 h3
  have hcl5 : ∀ a, CLM ≤ a → a < CLM + 309 → m5.mem a = m1.mem a := fun a h1 h2 =>
    F5' a (by simp only [CLM, PF] at *; omega) (by simp only [CLM, C_ROOT] at *; omega)
      (by simp only [CLM, OL] at *; omega) (by simp only [CLM, RB] at *; omega)
      (by simp only [CLM, S_H] at *; omega)
  have hN : Bytes.leToNat (readMem m5.mem C_N 4) = rs.length := by
    rw [← h1.nC]; simp only [rd32]
    rw [fin_rd_eq (a := C_N) (n := 4) fun i h1 h2 => F5' i (by simp only [C_N, PF] at *; omega)
      (by simp only [C_N, C_ROOT] at *; omega) (by simp only [C_N, OL] at *; omega)
      (by simp only [C_N, RB] at *; omega) (by simp only [C_N, S_H] at *; omega)]
  have hD : Bytes.leToNat (readMem m5.mem D_G 8) = Params.G := by
    rw [fin_rd_eq (a := D_G) (n := 8) fun i h1 h2 => F5' i (by simp only [D_G, PF] at *; omega)
      (by simp only [D_G, C_ROOT] at *; omega) (by simp only [D_G, OL] at *; omega)
      (by simp only [D_G, RB] at *; omega) (by simp only [D_G, S_H] at *; omega)]
    have := fin_sub h1.toBase.data 120 8 (by decide)
    simp only [Nat.zero_add] at this
    rw [show D_G = 120 from rfl, this, fin_dataG, u64, ← fin_leN_eq, leToNat_leN 8 _ (by decide)]
  have hP : Params.G = 223182562500 := by simp only [Params.G, Params.newActionReceiptExec, Params.transferExec]
  have hg : BinOp.mul.eval (Bytes.leToNat (readMem m5.mem C_N 4)) (Bytes.leToNat (readMem m5.mem D_G 8)) =
      Bytes.leToNat (readMem m5.mem (CLM + 285) 8) := by
    rw [hN, hD, hP, evM _ _ (by omega), hcl 285 8 (by decide) _ hcl5, fin_leToNat_leNat, ← eG, hgas, hP]
  have htk : readMem m5.mem C_TOK 16 = readMem m5.mem (CLM + 293) 16 := by
    rw [hcl 293 16 (by decide) _ hcl5, fin_rd_eq (a := C_TOK) (n := 16) fun i h1 h2 => F5 i
      (by simp only [C_TOK, PF] at *; omega)
      (by simp only [C_TOK, C_ROOT] at *; omega) (by simp only [C_TOK, OL] at *; omega)
      (by simp only [C_TOK, RB] at *; omega) (by simp only [C_TOK, S_H] at *; omega), hb.tokens, eTk]
    exact u128_leNat_fin _ (by simp [seg]; have := h1.shape.1; omega)
  refine twp_mono (tB_twp0 h145 h155 hg htk) fun m6 c6 ⟨h156, hc6⟩ => ⟨h156, ?_⟩
  omega
end
end ReexecNpai
