import ReexecNpai.Spec.BatchAux2

/-!
# Batch proofs, part 3: `pRefundOutcome` (byte-buffer building)
-/

set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-- A buffer under construction: `r1` points past the bytes `bs` written at `base`. -/
def Bld (m : M) (base : Nat) (bs : List UInt8) : Prop :=
  m.regs 1 = base + bs.length ∧ readMem m.mem base bs.length = bs

theorem rm_wm_app (M0 : Nat → UInt8) (base : Nat) (bs L : List UInt8)
    (h : readMem M0 base bs.length = bs) :
    readMem (writeMem M0 (base + bs.length) L.length L) base (bs ++ L).length = bs ++ L := by
  rw [List.length_append, readMem_add, rm_wm_out _ _ _ _ _ _ (by omega), h,
    rm_wm_self _ _ _ _ rfl]

theorem twp_cst_cons {inp : Inputs} {m : M} {d v : Nat} {L : List Stmt} {Q : M → Nat → Prop} (hL : L ≠ [])
    (hv : v < 18446744073709551616)
    (h : twp P inp (seqs L) ⟨setReg m.regs d v, m.mem⟩ (fun m' c => Q m' (1 + c))) :
    twp P inp (seqs (CST d v :: L)) m Q := by
  cases L with
  | nil => exact absurd rfl hL
  | cons a L =>
    show twp P inp (.seq (CST d v) (seqs (a :: L))) m Q
    rw [twp_seq, twp_op]
    refine ⟨rfl, _, rfl, ?_⟩
    simp only [ins, evConst v hv, cost]
    exact h

def APPL (src n : Nat) : List Stmt := [CST 2 src, CST 3 n, memcpy 1 2 3 4]

section
variable {pub cb pb : List UInt8}

theorem app_twp {m : M} {base src n : Nat} {bs : List UInt8} (hk1 : m.regs 15 = 1) (hb : Bld m base bs)
    (h1 : base + bs.length + n ≤ 13844304) (h2 : src + n ≤ 13844304)
    (hov : base + bs.length ≤ src ∨ src + n ≤ base + bs.length) :
    twp P (Inp pub cb pb) (seqs (APPL src n)) m (fun m' c => Bld m' base (bs ++ readMem m.mem src n) ∧
      m'.mem = writeMem m.mem (base + bs.length) n (readMem m.mem src n) ∧
      Frame [1, 2, 3, 4] m m' ∧ c ≤ 7 * n + 3) := by
  obtain ⟨hr1, hrd⟩ := hb
  simp only [APPL, seqs]
  bvc
  refine twp_memcpy (n := n) (by simp [setReg_apply, hk1]) (by simp [setReg_apply])
    (by simp [setReg_apply, hr1]; omega) (by simp [setReg_apply]; omega)
    (by simp [setReg_apply, hr1]; omega) (fun m1 c1 hm1 h1' hF hc => ?_)
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hr1] at hm1 h1'
  refine ⟨⟨?_, ?_⟩, hm1, ?_, by omega⟩
  · rw [h1']; simp; omega
  · rw [hm1]
    have := rm_wm_app m.mem base bs (readMem m.mem src n) hrd
    simp only [readMem_length] at this
    exact this
  · intro j hj
    rw [hF j hj]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp [setReg_apply, hj.2.1, hj.2.2.1]

theorem u32app_twp {m : M} {base v x : Nat} {bs : List UInt8} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hb : Bld m base bs) (hv : m.regs v = x) (hx : x < 4294967296) (hv1 : v ≠ 1) (hv12 : v ≠ 12) (hv13 : v ≠ 13)
    (h1 : base + bs.length + 4 ≤ 13844304) :
    twp P (Inp pub cb pb) (seqs [st32 1 v, ADDI 1 1 4]) m (fun m' c => Bld m' base (bs ++ u32 x) ∧
      m'.mem = writeMem m.mem (base + bs.length) 4 (u32 x) ∧
      Frame [1, 12, 13] m m' ∧ c ≤ 20) := by
  obtain ⟨hr1, hrd⟩ := hb
  simp only [seqs]
  bvc [hk8, hr1, hv]
  refine ⟨⟨by simp; omega, ?_⟩, by rw [leN_eq]; rfl, ?_⟩
  · have := rm_wm_app m.mem base bs (u32 x) hrd
    rw [u32_len] at this
    rw [leN_eq]; exact this
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp [setReg_apply, hj.1, hj.2.1, hj.2.2]

theorem byteapp_twp {m : M} {base v x : Nat} {bs : List UInt8} (hb : Bld m base bs) (hv : m.regs v = x)
    (hx : x < 256) (hv1 : v ≠ 1) (h1 : base + bs.length + 1 ≤ 13844304) :
    twp P (Inp pub cb pb) (seqs [ST8 1 v, ADDI 1 1 1]) m (fun m' c => Bld m' base (bs ++ [UInt8.ofNat x]) ∧
      m'.mem = writeMem m.mem (base + bs.length) 1 [UInt8.ofNat x] ∧
      Frame [1] m m' ∧ c ≤ 2) := by
  obtain ⟨hr1, hrd⟩ := hb
  simp only [seqs]
  bvc [hr1, hv, Nat.mod_eq_of_lt hx]
  refine ⟨⟨by simp; omega, ?_⟩, ?_⟩
  · have := rm_wm_app m.mem base bs [UInt8.ofNat x] hrd
    simpa using this
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    simp [setReg_apply, hj]

/-- Append `borsh(bytes)` for the RT field pair at offsets `o` (pointer), `o + 4` (length). -/
def BRL (o : Nat) : List Stmt := [ADDI 4 9 (o + 4), ld32 3 4, st32 1 3, ADDI 1 1 4, ADDI 4 9 o, ld32 2 4,
  ADDI 4 9 (o + 4), ld32 3 4, memcpy 1 2 3 4]

theorem pAppSigner_eq : pAppSigner = seqs (BRL 20) := rfl

theorem sigapp_twp {m : M} {base E sp sl o : Nat} {bs sig : List UInt8} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hb : Bld m base bs) (h9 : m.regs 9 = E) (hE : E + 40 ≤ 19968) (ho : o + 8 ≤ 40)
    (h24 : ArenaCore.Bytes.leToNat (readMem m.mem (E + (o + 4)) 4) = sl)
    (h20 : ArenaCore.Bytes.leToNat (readMem m.mem (E + o) 4) = sp)
    (hsig : readMem m.mem sp sl = sig) (hsl : sl < 4294967296) (hsp : sp + sl ≤ 13844304)
    (h1 : base + bs.length + 4 + sl ≤ 13844304)
    (hbE : E + 40 ≤ base + bs.length ∨ base + bs.length + 4 ≤ E)
    (hov : base + bs.length + 4 ≤ sp ∨ sp + sl ≤ base + bs.length) :
    twp P (Inp pub cb pb) (seqs (BRL o)) m (fun m' c => Bld m' base (bs ++ (u32 sl ++ sig)) ∧
      (∀ a, ¬ (base + bs.length ≤ a ∧ a < base + bs.length + 4 + sl) → m'.mem a = m.mem a) ∧
      m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 7 * sl + 100) := by
  obtain ⟨hr1, hrd⟩ := hb
  simp only [BRL, seqs]
  bvc [hk8, hk1, hr1, h9, h24, h20, rm_wm_out]
  refine twp_memcpy (n := sl) (by simp [setReg_apply, hk1]) (by simp [setReg_apply])
    (by simp [setReg_apply]; omega) (by simp [setReg_apply]; omega)
    (by simp [setReg_apply]; omega) (fun m1 c1 hm1 h1' hF hc => ?_)
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at hm1 h1'
  have hsig' : readMem (writeMem m.mem (base + bs.length) 4 (ArenaCore.Bytes.leN 4 sl)) sp sl = sig := by
    rw [rm_wm_out _ _ _ _ _ _ (by omega), hsig]
  rw [hsig'] at hm1
  have e9 : m1.regs 9 = E := by rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  have hsl' : sig.length = sl := by rw [← hsig]; simp
  refine ⟨⟨?_, ?_⟩, ?_, e9, e14, e15, by omega⟩
  · rw [h1']; simp [u32_len]; omega
  · rw [hm1, ← List.append_assoc]
    have e1 := rm_wm_app m.mem base bs (u32 sl) hrd
    rw [u32_len] at e1
    have e2 := rm_wm_app (writeMem m.mem (base + bs.length) 4 (u32 sl)) base (bs ++ u32 sl) sig
      (by simpa [u32_len] using e1)
    simp only [List.length_append, u32_len, hsl'] at e2 ⊢
    rw [leN_eq]; rw [← Nat.add_assoc] at e2; exact e2
  · intro a ha
    rw [hm1, writeMem_apply_out _ _ _ _ _ (by omega), writeMem_apply_out _ _ _ _ _ (by omega)]

/-- Buffer under construction at `base`, writes confined to `[lo, hi)` since `m0`. -/
def BF (m0 m : M) (base : Nat) (bs : List UInt8) (lo hi : Nat) : Prop :=
  Bld m base bs ∧ (∀ a, (a < lo ∨ hi ≤ a) → m.mem a = m0.mem a) ∧ m.regs 9 = m0.regs 9 ∧
    m.regs 14 = 8 ∧ m.regs 15 = 1

theorem bf_rm {m0 m : M} {base lo hi : Nat} {bs : List UInt8} (h : BF m0 m base bs lo hi) {p n : Nat}
    (hp : p + n ≤ lo ∨ hi ≤ p) : readMem m.mem p n = readMem m0.mem p n :=
  readMem_congr (fun i hi' => h.2.1 _ (by omega))

theorem app_bf {m0 m : M} {base lo hi src n : Nat} {bs : List UInt8} (h : BF m0 m base bs lo hi)
    (hl : lo ≤ base + bs.length) (hh : base + bs.length + n ≤ hi) (hhi : hi ≤ 13844304)
    (h2 : src + n ≤ 13844304) (hs : src + n ≤ lo ∨ hi ≤ src) :
    twp P (Inp pub cb pb) (seqs (APPL src n)) m (fun m' c =>
      BF m0 m' base (bs ++ readMem m0.mem src n) lo hi ∧ c ≤ 7 * n + 3) := by
  obtain ⟨hb, hfr, h9, h14, h15⟩ := h
  refine twp_mono (app_twp h15 hb (by omega) h2 (by omega)) ?_
  rintro m' c ⟨hb', hm, hF, hc⟩
  have hsrc : readMem m.mem src n = readMem m0.mem src n := readMem_congr (fun i hi' => hfr _ (by omega))
  rw [hsrc] at hb'
  refine ⟨⟨hb', ?_, by rw [hF 9 (by decide)]; exact h9, by rw [hF 14 (by decide)]; exact h14,
    by rw [hF 15 (by decide)]; exact h15⟩, hc⟩
  intro a ha
  rw [hm, writeMem_apply_out _ _ _ _ _ (by omega), hfr a ha]

theorem u32_bf {m0 m : M} {base lo hi v x : Nat} {bs : List UInt8} (h : BF m0 m base bs lo hi)
    (hv : m.regs v = x) (hx : x < 4294967296) (hv1 : v ≠ 1) (hv12 : v ≠ 12) (hv13 : v ≠ 13) (hv9 : v ≠ 9)
    (hl : lo ≤ base + bs.length) (hh : base + bs.length + 4 ≤ hi) (hhi : hi ≤ 13844304) :
    twp P (Inp pub cb pb) (seqs [st32 1 v, ADDI 1 1 4]) m (fun m' c =>
      BF m0 m' base (bs ++ u32 x) lo hi ∧ c ≤ 20 ∧ Frame [1, 12, 13] m m') := by
  obtain ⟨hb, hfr, h9, h14, h15⟩ := h
  refine twp_mono (u32app_twp h15 h14 hb hv hx hv1 hv12 hv13 (by omega)) ?_
  rintro m' c ⟨hb', hm, hF, hc⟩
  refine ⟨⟨hb', ?_, by rw [hF 9 (by decide)]; exact h9, by rw [hF 14 (by decide)]; exact h14,
    by rw [hF 15 (by decide)]; exact h15⟩, hc, hF⟩
  intro a ha
  rw [hm, writeMem_apply_out _ _ _ _ _ (by omega), hfr a ha]

theorem byte_bf {m0 m : M} {base lo hi v x : Nat} {bs : List UInt8} (h : BF m0 m base bs lo hi)
    (hv : m.regs v = x) (hx : x < 256) (hv1 : v ≠ 1)
    (hl : lo ≤ base + bs.length) (hh : base + bs.length + 1 ≤ hi) (hhi : hi ≤ 13844304) :
    twp P (Inp pub cb pb) (seqs [ST8 1 v, ADDI 1 1 1]) m (fun m' c =>
      BF m0 m' base (bs ++ [UInt8.ofNat x]) lo hi ∧ c ≤ 2) := by
  obtain ⟨hb, hfr, h9, h14, h15⟩ := h
  refine twp_mono (byteapp_twp hb hv hx hv1 (by omega)) ?_
  rintro m' c ⟨hb', hm, hF, hc⟩
  refine ⟨⟨hb', ?_, by rw [hF 9 (by decide)]; exact h9, by rw [hF 14 (by decide)]; exact h14,
    by rw [hF 15 (by decide)]; exact h15⟩, hc⟩
  intro a ha
  rw [hm, writeMem_apply_out _ _ _ _ _ (by omega), hfr a ha]

theorem brl_bf {m0 m : M} {base lo hi E sp sl o : Nat} {bs sig : List UInt8} (h : BF m0 m base bs lo hi)
    (h9 : m0.regs 9 = E) (hE : E + 40 ≤ 19968) (hlo : E + 40 ≤ lo ∨ hi ≤ E) (ho : o + 8 ≤ 40)
    (h24 : ArenaCore.Bytes.leToNat (readMem m0.mem (E + (o + 4)) 4) = sl)
    (h20 : ArenaCore.Bytes.leToNat (readMem m0.mem (E + o) 4) = sp)
    (hsig : readMem m0.mem sp sl = sig) (hsl : sl < 4294967296) (hsp : sp + sl ≤ 13844304)
    (hs : sp + sl ≤ lo ∨ hi ≤ sp)
    (hl : lo ≤ base + bs.length) (hh : base + bs.length + 4 + sl ≤ hi) (hhi : hi ≤ 13844304) :
    twp P (Inp pub cb pb) (seqs (BRL o)) m (fun m' c =>
      BF m0 m' base (bs ++ (u32 sl ++ sig)) lo hi ∧ c ≤ 7 * sl + 100) := by
  have hb9 := h.2.2.1
  obtain ⟨hb, hfr, -, h14, h15⟩ := h
  have r24 : readMem m.mem (E + (o + 4)) 4 = readMem m0.mem (E + (o + 4)) 4 :=
    readMem_congr (fun i hi' => hfr _ (by omega))
  have r20 : readMem m.mem (E + o) 4 = readMem m0.mem (E + o) 4 := readMem_congr (fun i hi' => hfr _ (by omega))
  have rs : readMem m.mem sp sl = readMem m0.mem sp sl := readMem_congr (fun i hi' => hfr _ (by omega))
  refine twp_mono (sigapp_twp h15 h14 hb (by rw [hb9, h9]) hE ho (by rw [r24, h24]) (by rw [r20, h20])
    (by rw [rs, hsig]) hsl hsp (by omega) (by omega) (by omega)) ?_
  rintro m' c ⟨hb', hm, e9, e14, e15, hc⟩
  exact ⟨⟨hb', fun a ha => by rw [hm a (by omega), hfr a ha], by rw [e9, h9], e14, e15⟩, hc⟩

theorem bf_setReg {m0 m : M} {base lo hi : Nat} {bs : List UInt8} (h : BF m0 m base bs lo hi) {r v : Nat}
    (h1 : r ≠ 1) (h9 : r ≠ 9) (h14 : r ≠ 14) (h15 : r ≠ 15) :
    BF m0 ⟨setReg m.regs r v, m.mem⟩ base bs lo hi := by
  obtain ⟨⟨hb1, hb2⟩, hfr, e9, e14, e15⟩ := h
  exact ⟨⟨by simp [setReg_apply, Ne.symm h1, hb1], hb2⟩, hfr, by simp [setReg_apply, Ne.symm h9, e9],
    by simp [setReg_apply, Ne.symm h14, e14], by simp [setReg_apply, Ne.symm h15, e15]⟩

theorem bf_frame {m0 m m' : M} {base lo hi : Nat} {bs : List UInt8} (h : BF m0 m base bs lo hi)
    (hm : m'.mem = m.mem) (hF : Frame [2, 3, 4, 12, 13] m m') : BF m0 m' base bs lo hi := by
  obtain ⟨⟨hb1, hb2⟩, hfr, e9, e14, e15⟩ := h
  exact ⟨⟨by rw [hF 1 (by decide), hb1], by rw [hm, hb2]⟩, fun a ha => by rw [hm, hfr a ha],
    by rw [hF 9 (by decide), e9], by rw [hF 14 (by decide), e14], by rw [hF 15 (by decide), e15]⟩

def PKL : List Stmt := [ADDI 4 9 28, ld32 2 4, LD8 3 2, CST 4 5, SHL 3 3 4, ADDI 3 3 33, memcpy 1 2 3 4]

theorem pk_bf {m0 m : M} {base lo hi E pp t : Nat} {bs : List UInt8} (h : BF m0 m base bs lo hi)
    (h9 : m0.regs 9 = E) (hE : E + 40 ≤ 19968) (hlo : 19968 ≤ lo)
    (h28 : ArenaCore.Bytes.leToNat (readMem m0.mem (E + 28) 4) = pp)
    (ht : (m0.mem pp).toNat = t) (ht1 : t ≤ 1) (hpp : pp + 65 ≤ 13844304)
    (hs : pp + 65 ≤ lo ∨ hi ≤ pp)
    (hl : lo ≤ base + bs.length) (hh : base + bs.length + 33 + 32 * t ≤ hi) (hhi : hi ≤ 13844304) :
    twp P (Inp pub cb pb) (seqs PKL) m (fun m' c =>
      BF m0 m' base (bs ++ readMem m0.mem pp (33 + 32 * t)) lo hi ∧ c ≤ 500) := by
  have hb9 := h.2.2.1
  have hb1 := h.1.1
  have hfr := h.2.1
  have h14 := h.2.2.2.1
  have h15 := h.2.2.2.2
  have r28 : readMem m.mem (E + 28) 4 = readMem m0.mem (E + 28) 4 := readMem_congr (fun i hi' => hfr _ (by omega))
  have rpp : m.mem pp = m0.mem pp := hfr _ (by omega)
  simp only [PKL, seqs]
  bvc [hb9, h9, h14, h15, r28, h28, rpp, ht]
  have hsh : BinOp.shl.eval t 5 = 32 * t := by
    rw [eval_shl _ _ (by omega) (by unfold wordMod; omega)]; omega
  simp (disch := omega) only [hsh, evAddi]
  refine twp_memcpy (n := 33 + 32 * t) (by simp [setReg_apply, h15]) (by simp [setReg_apply]; omega)
    (by simp [setReg_apply, hb1]; omega) (by simp [setReg_apply]; omega)
    (by simp [setReg_apply, hb1]; omega) (fun m1 c1 hm1 h1' hF hc => ?_)
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, hb1] at hm1 h1'
  have rs : readMem m.mem pp (33 + 32 * t) = readMem m0.mem pp (33 + 32 * t) :=
    readMem_congr (fun i hi' => hfr _ (by omega))
  have hb' := rm_wm_app m.mem base bs (readMem m.mem pp (33 + 32 * t)) h.1.2
  simp only [readMem_length] at hb'
  refine ⟨⟨⟨by rw [h1']; simp; omega, by rw [hm1, ← rs]; simpa using hb'⟩, ?_, ?_, ?_, ?_⟩, by omega⟩
  · intro a ha; rw [hm1, writeMem_apply_out _ _ _ _ _ (by omega), hfr a ha]
  · rw [hF 9 (by decide)]; simp [setReg_apply, hb9]
  · rw [hF 14 (by decide)]; simp [setReg_apply, h14]
  · rw [hF 15 (by decide)]; simp [setReg_apply, h15]

def RA1 : List Stmt := [ADDI 4 9 16, ld32 2 4, CST 1 S_ID, CST 3 32, memcpy 1 2 3 4]
def RA2 : List Stmt := [CST 1 S_ID, CST 2 48, SHA 1 1 2, ldCell 1 C_RBEND]

theorem ra1_twp {m : M} {E rp : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h9 : m.regs 9 = E)
    (hE : E + 40 ≤ 19968) (h16 : ArenaCore.Bytes.leToNat (readMem m.mem (E + 16) 4) = rp)
    (hrp : 1136 ≤ rp) (hrp2 : rp + 32 ≤ 13844304) :
    twp P (Inp pub cb pb) (seqs RA1) m (fun m' c =>
      BF m m' 1088 (readMem m.mem rp 32) 1088 1136 ∧ c ≤ 300) := by
  simp only [RA1, seqs]
  bvc [hk1, hk8, h9, h16]
  refine twp_memcpy (n := 32) (by simp [setReg_apply, hk1]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]; omega)
    (by simp [setReg_apply]; omega) (fun m1 c1 hm1 h1' hF hc => ?_)
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at hm1 h1'
  refine ⟨⟨⟨by rw [h1']; simp, by rw [hm1]; simp only [readMem_length]; exact rm_wm_self _ _ _ _ (by simp)⟩,
    fun a ha => by rw [hm1, writeMem_apply_out _ _ _ _ _ (by omega)], ?_, ?_, ?_⟩, by omega⟩
  · rw [hF 9 (by decide)]; simp [setReg_apply, h9]
  · rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  · rw [hF 15 (by decide)]; simp [setReg_apply, hk1]

theorem refA_twp {m : M} {E rp L : Nat} {r : Receipt} {ht : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hd : readMem m.mem 0 168 = dataSeg) (h9 : m.regs 9 = E)
    (hE : E + 40 ≤ 19968) (h16 : ArenaCore.Bytes.leToNat (readMem m.mem (E + 16) 4) = rp)
    (hrp : 8844304 ≤ rp) (hrp2 : rp + 32 ≤ 13844304) (hrid : readMem m.mem rp 32 = r.receiptId)
    (hh : readMem m.mem 2645 8 = u64 ht) (hrb : ArenaCore.Bytes.leToNat (readMem m.mem 3116 4) = RB + 4 + L) :
    twp P (Inp pub cb pb) (seqs (RA1 ++ (APPL (CLM + 85) 8 ++ (APPL D_ZERO 8 ++ RA2)))) m (fun m' c =>
      readMem m'.mem 1088 32 = receiptIdFrom r.receiptId ht 0 ∧ m'.regs 1 = RB + 4 + L ∧
      (∀ a, (a < 1088 ∨ 1136 ≤ a) → m'.mem a = m.mem a) ∧
      m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 600) := by
  rw [batch_twp_seqs_append _ _ (by simp [RA1]) (by simp [APPL])]
  refine twp_mono (ra1_twp hk1 hk8 h9 hE h16 (by omega) hrp2) ?_
  rintro m1 c1 ⟨hb1, hc1⟩
  rw [batch_twp_seqs_append _ _ (by simp [APPL]) (by simp [APPL])]
  refine twp_mono (app_bf hb1 (by simp) (by simp) (by omega) (by simp [CLM]) (by simp [CLM])) ?_
  rintro m2 c2 ⟨hb2, hc2⟩
  rw [batch_twp_seqs_append _ _ (by simp [APPL]) (by simp [RA2])]
  refine twp_mono (app_bf hb2 (by simp) (by simp) (by omega) (by (try simp only [D_ZERO]); omega) (by (try simp only [D_ZERO]); omega)) ?_
  rintro m3 c3 ⟨hb3, hc3⟩
  obtain ⟨⟨hr1, hr3⟩, hfr, e9, e14, e15⟩ := hb3
  simp only [readMem_length, hrid, CLM, hh, D_ZERO, data_zero hd 8 (by omega)] at hr1 hr3
  have hl : (r.receiptId ++ (u64 ht ++ List.replicate 8 0)).length = 48 := by
    rw [← hrid, ← hh]; simp
  rw [List.append_assoc] at hr3
  have hr3' : readMem m3.mem 1088 48 = r.receiptId ++ (u64 ht ++ List.replicate 8 0) := by
    rw [← hr3, hl]
  have hrb3 : ArenaCore.Bytes.leToNat (readMem m3.mem 3116 4) = RB + 4 + L := by
    rw [readMem_congr (fun i hi => hfr _ (by omega)), hrb]
  simp only [RA2, seqs, ldCell]
  bvc [hr3', e14, e15, hrb3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rm_wm_self _ _ _ _ (ArenaCore.sha256_length _)]
    simp only [receiptIdFrom, List.append_assoc]; rfl
  · rw [rm_wm_out _ _ _ _ _ _ (by omega), hrb3]; rfl
  · intro a ha
    rw [writeMem_apply_out _ _ _ _ _ (by omega), hfr a ha]
  · exact ⟨by rw [e9, h9], by omega⟩

def RBL : List Stmt := [CST 3 6] ++ ([st32 1 3, ADDI 1 1 4] ++ (APPL D_SYS 6 ++ ([seqs (BRL 20)] ++
  (APPL S_ID 32 ++ ([CST 3 0] ++ ([ST8 1 3, ADDI 1 1 1] ++ ([seqs (BRL 20)] ++ (PKL ++ (APPL D_ZERO 16 ++
  (APPL D_MID 13 ++ APPL S_B 16))))))))))

theorem pk_facts {M0 : Nat → UInt8} {p : Nat} {k : PublicKey} (hw : k.wf = true)
    (h : readMem M0 p (1 + k.data.length) = k.encode) :
    (M0 p).toNat = k.tag ∧ k.tag ≤ 1 ∧ 1 + k.data.length = 33 + 32 * k.tag := by
  simp only [PublicKey.wf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hw
  have ht : k.tag ≤ 1 ∧ 1 + k.data.length = 33 + 32 * k.tag := by omega
  refine ⟨?_, ht⟩
  have := mem_of_readMem h 0 (by omega)
  simp only [Nat.add_zero, PublicKey.encode, u8, NearSpec.leN, List.cons_append, List.nil_append,
    List.getD_cons_zero] at this
  rw [this]; simp; omega

set_option maxHeartbeats 2000000 in
theorem refB_twp {m4 : M} {E A L : Nat} {r : Receipt} {refs : List UInt8}
    (hb : BF m4 m4 (RB + 4) refs (RB + 4 + L) AR)
    (h9 : m4.regs 9 = E) (hE : E + 40 ≤ 19968) (hrt : RtMem m4.mem E r A) (hrc : RcptMem m4.mem r A)
    (hA : 8844304 ≤ A) (hAh : pGp r A + 45 ≤ 13844304)
    (hsl : r.signerId.length ≤ 64) (hpk : r.signerPk.wf = true) (hcap : RB + 4 + L + 289 ≤ AR)
    (hrl : refs.length = L) :
    twp P (Inp pub cb pb) (seqs RBL) m4 (fun m' c => BF m4 m' (RB + 4) (refs ++
      (u32 6 ++ readMem m4.mem 80 6 ++ (u32 r.signerId.length ++ r.signerId) ++ readMem m4.mem 1088 32 ++
        [UInt8.ofNat 0] ++ (u32 r.signerId.length ++ r.signerId) ++ r.signerPk.encode ++
        readMem m4.mem 136 16 ++ readMem m4.mem 88 13 ++ readMem m4.mem 928 16)) (RB + 4 + L) AR ∧
      c ≤ 3000) := by
  obtain ⟨ht, ht1, hpl⟩ := pk_facts hpk hrc.pk
  have hsA : A ≤ pSig r A := by simp only [pSig, pRid, pRecv]; omega
  have hsP : pSig r A + r.signerId.length = pPk r A := rfl
  have hpG : pPk r A + 1 + r.signerPk.data.length = pGp r A := rfl
  simp only [RB, AR] at hb hcap ⊢
  simp only [RBL]
  rw [batch_twp_seqs_append _ _ (by simp) (by simp [APPL, PKL])]
  bvc
  have hb0 := bf_setReg (r := 3) (v := 6) hb (by decide) (by decide) (by decide) (by decide)
  rw [batch_twp_seqs_append _ _ (by simp) (by simp [APPL, PKL])]
  refine twp_mono (u32_bf (v := 3) (x := 6) hb0 (by simp [setReg_apply]) (by omega) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega) (by omega)) ?_
  rintro m1 c1 ⟨hb1, hc1, -⟩
  rw [batch_twp_seqs_append _ _ (by simp [APPL, PKL]) (by simp [APPL, PKL])]
  refine twp_mono (app_bf hb1 (by simp <;> omega) (by simp <;> omega) (by omega) (by (try simp only [D_SYS]); omega) (by (try simp only [D_SYS]); omega)) ?_
  rintro m2 c2 ⟨hb2, hc2⟩
  rw [batch_twp_seqs_append _ _ (by simp) (by simp [APPL, PKL])]
  refine twp_mono (brl_bf (o := 20) (sl := r.signerId.length) (sp := pSig r A) hb2 h9 hE (by omega) (by omega) hrt.f24 hrt.f20 hrc.sig
    (by omega) (by omega) (by omega) (by simp <;> omega) (by simp <;> omega) (by omega)) ?_
  rintro m3 c3 ⟨hb3, hc3⟩
  rw [batch_twp_seqs_append _ _ (by simp [APPL, PKL]) (by simp [APPL, PKL])]
  refine twp_mono (app_bf hb3 (by simp <;> omega) (by simp <;> omega) (by omega) (by (try simp only [S_ID]); omega) (by (try simp only [S_ID]); omega)) ?_
  rintro m5 c5 ⟨hb5, hc5⟩
  rw [batch_twp_seqs_append _ _ (by simp) (by simp [APPL, PKL])]
  bvc
  have hb5' := bf_setReg (r := 3) (v := 0) hb5 (by decide) (by decide) (by decide) (by decide)
  rw [batch_twp_seqs_append _ _ (by simp) (by simp [APPL, PKL])]
  refine twp_mono (byte_bf (v := 3) (x := 0) hb5' (by simp [setReg_apply]) (by omega) (by decide)
    (by simp <;> omega) (by simp <;> omega) (by omega)) ?_
  rintro m6 c6 ⟨hb6, hc6⟩
  rw [batch_twp_seqs_append _ _ (by simp) (by simp [APPL, PKL])]
  refine twp_mono (brl_bf (o := 20) (sl := r.signerId.length) (sp := pSig r A) hb6 h9 hE (by omega) (by omega) hrt.f24 hrt.f20 hrc.sig
    (by omega) (by omega) (by omega) (by simp <;> omega) (by simp <;> omega) (by omega)) ?_
  rintro m7 c7 ⟨hb7, hc7⟩
  rw [batch_twp_seqs_append _ _ (by simp [APPL, PKL]) (by simp [APPL, PKL])]
  refine twp_mono (pk_bf (pp := pPk r A) hb7 h9 hE (by omega) hrt.f28 ht ht1 (by omega) (by omega)
    (by simp <;> omega) (by simp <;> omega) (by omega)) ?_
  rintro m8 c8 ⟨hb8, hc8⟩
  rw [← hpl, hrc.pk] at hb8
  have hpe : r.signerPk.encode.length = 33 + 32 * r.signerPk.tag := by
    simp [PublicKey.encode, u8, NearSpec.leN]; omega
  rw [batch_twp_seqs_append _ _ (by simp [APPL, PKL]) (by simp [APPL, PKL])]
  refine twp_mono (app_bf hb8 (by simp [hpe]; omega) (by simp [hpe]; omega) (by omega) (by (try simp only [D_ZERO]); omega) (by (try simp only [D_ZERO]); omega)) ?_
  rintro m9 c9 ⟨hb9, hc9⟩
  rw [batch_twp_seqs_append _ _ (by simp [APPL, PKL]) (by simp [APPL, PKL])]
  refine twp_mono (app_bf hb9 (by simp [hpe]; omega) (by simp [hpe]; omega) (by omega) (by (try simp only [D_MID]); omega) (by (try simp only [D_MID]); omega)) ?_
  rintro m10 c10 ⟨hb10, hc10⟩
  refine twp_mono (app_bf hb10 (by simp [hpe]; omega) (by simp [hpe]; omega) (by omega) (by (try simp only [S_B]); omega) (by (try simp only [S_B]); omega)) ?_
  rintro m11 c11 ⟨hb11, hc11⟩
  refine ⟨?_, by omega⟩
  simp only [List.append_assoc, D_SYS, S_ID, D_ZERO, D_MID, S_B] at hb11 ⊢
  exact hb11

def RENDL : List Stmt := [stCell C_RBEND 1, ldCell 2 C_NREF, ADDI 2 2 1, stCell C_NREF 2, CST 5 1]
def RFL : List Stmt := RA1 ++ (APPL (CLM + 85) 8 ++ (APPL D_ZERO 8 ++ (RA2 ++ (RBL ++ RENDL))))
def R0L : List Stmt := [CST 1 S_B, CST 2 D_ZERO, CST 3 16, MEMEQ 6 1 2 3]
def OUT1 : List Stmt := [CST 1 S_OUT, st32 1 5, ADDI 1 1 4]
def OUT4 : List Stmt := [ADDI 4 9 12, ld32 3 4, st32 1 3, ADDI 1 1 4, ADDI 4 9 8, ld32 2 4, ADDI 4 9 12, ld32 3 4,
  memcpy 1 2 3 4]
def OUT5 : List Stmt := [CST 2 2, ST8 1 2, ADDI 1 1 1, CST 2 0, st32 1 2, ADDI 1 1 4]
def OUT6 : List Stmt := [CST 2 S_OUT, SUB 3 1 2, CST 1 (S_LEAF + 36), SHA 1 2 3]
def OUT7 : List Stmt := [CST 1 S_LEAF, CST 2 2, st32 1 2, ADDI 1 1 4, ADDI 4 9 16, ld32 2 4, CST 3 32, memcpy 1 2 3 4]
def OUT8 : List Stmt := [ldCell 8 C_I, CST 2 32, MUL 2 8 2, ADDI 2 2 OL, CST 1 S_LEAF, CST 3 68, SHA 2 1 3]

end

theorem pRefundOutcome_eq : pRefundOutcome = seqs (R0L ++ (.ite 6 (CST 5 0) (seqs RFL) :: (OUT1 ++
    (.ite 5 (seqs (APPL S_ID 32)) nop :: (APPL D_G 8 ++ (APPL S_A 16 ++ (OUT4 ++ (OUT5 ++ (OUT6 ++
    (OUT7 ++ OUT8)))))))))) := rfl

section
variable {pub cb pb : List UInt8}

theorem refund_encode {M0 : Nat → UInt8} (hd : readMem M0 0 168 = dataSeg) (r : Receipt) (ht s : Nat)
    (hrid : readMem M0 1088 32 = receiptIdFrom r.receiptId ht 0) (hs : readMem M0 928 16 = u128 s) :
    u32 6 ++ readMem M0 80 6 ++ (u32 r.signerId.length ++ r.signerId) ++ readMem M0 1088 32 ++
      [UInt8.ofNat 0] ++ (u32 r.signerId.length ++ r.signerId) ++ r.signerPk.encode ++
      readMem M0 136 16 ++ readMem M0 88 13 ++ readMem M0 928 16 = (gasRefundReceipt r ht s).encode := by
  rw [data_sys hd, data_zero hd 16 (by omega), data_mid hd, hrid, hs]
  simp only [gasRefundReceipt, Receipt.encode, borshBytes, receiptMid, List.append_assoc]
  rfl

theorem refund_len (r : Receipt) (ht s : Nat) (hsl : r.signerId.length ≤ 64) (hpk : r.signerPk.wf = true) :
    (gasRefundReceipt r ht s).encode.length ≤ 289 := by
  simp only [PublicKey.wf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hpk
  simp [gasRefundReceipt, Receipt.encode, borshBytes, PublicKey.encode, u8, u32_len, u128_len,
    receiptIdFrom, ArenaCore.sha256_length, AccountId.system, NearSpec.leN_length]
  omega

set_option maxHeartbeats 2000000 in
theorem refund_twp {m : M} {E A L n ht s : Nat} {r : Receipt} {refs : List UInt8}
    (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (hd : readMem m.mem 0 168 = dataSeg)
    (h9 : m.regs 9 = E) (hE : E + 40 ≤ 19968) (hElo : 3584 ≤ E) (hrt : RtMem m.mem E r A)
    (hrc : RcptMem m.mem r A) (hA : 8844304 ≤ A) (hAh : pGp r A + 45 ≤ 13844304)
    (hsl : r.signerId.length ≤ 64) (hpk : r.signerPk.wf = true) (hridl : r.receiptId.length = 32)
    (hh : readMem m.mem 2645 8 = u64 ht)
    (hrb : ArenaCore.Bytes.leToNat (readMem m.mem 3116 4) = RB + 4 + L)
    (hbuf : readMem m.mem (RB + 4) L = refs) (hrl : refs.length = L) (hcap : RB + 4 + L + 289 ≤ AR)
    (hn : ArenaCore.Bytes.leToNat (readMem m.mem 3112 4) = n) (hnl : n + 1 < 4294967296)
    (hsb : readMem m.mem 928 16 = u128 s) :
    twp P (Inp pub cb pb) (seqs RFL) m (fun m' c =>
      ArenaCore.Bytes.leToNat (readMem m'.mem 3116 4) = RB + 4 + L + (gasRefundReceipt r ht s).encode.length ∧
      readMem m'.mem (RB + 4) (L + (gasRefundReceipt r ht s).encode.length) =
        refs ++ (gasRefundReceipt r ht s).encode ∧
      ArenaCore.Bytes.leToNat (readMem m'.mem 3112 4) = n + 1 ∧
      readMem m'.mem 1088 32 = receiptIdFrom r.receiptId ht 0 ∧ m'.regs 5 = 1 ∧
      (∀ a, ¬ (1088 ≤ a ∧ a < 1136) → ¬ (3112 ≤ a ∧ a < 3120) → ¬ (RB + 4 + L ≤ a ∧ a < AR) →
        m'.mem a = m.mem a) ∧
      m'.regs 9 = E ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 5000) := by
  have hrid : readMem m.mem (pRid r A) 32 = r.receiptId := hrc.rid
  have hpr : pRid r A + 32 ≤ pGp r A := by simp only [pGp, pPk, pSig]; omega
  have hpa : A ≤ pRid r A := by simp only [pRid, pRecv]; omega
  simp only [RFL]
  rw [show RA1 ++ (APPL (CLM + 85) 8 ++ (APPL D_ZERO 8 ++ (RA2 ++ (RBL ++ RENDL)))) =
    (RA1 ++ (APPL (CLM + 85) 8 ++ (APPL D_ZERO 8 ++ RA2))) ++ (RBL ++ RENDL) by simp only [List.append_assoc]]
  rw [batch_twp_seqs_append _ _ (by simp [RA1]) (by simp [RBL])]
  refine twp_mono (refA_twp (r := r) hk1 hk8 hd h9 hE hrt.f16 (by omega) (by omega) hrid hh hrb) ?_
  rintro m4 c4 ⟨hid4, h41, hfr4, e9, e14, e15, hc4⟩
  have hb4 : BF m4 m4 (RB + 4) refs (RB + 4 + L) AR := by
    refine ⟨⟨by rw [h41, hrl], ?_⟩, fun _ _ => rfl, rfl, e14, e15⟩
    rw [hrl, readMem_congr (fun i hi => hfr4 _ (by simp only [RB] at hcap ⊢; omega)), hbuf]
  have hfrm : ∀ a, (a < 1088 ∨ 1136 ≤ a) → m4.mem a = m.mem a := hfr4
  have hrt4 : RtMem m4.mem E r A := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hrt
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (rw [readMem_congr (fun i hi => hfrm _ (by omega))]; assumption)
  have hrc4 : RcptMem m4.mem r A := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hrc
    have hb := hrt.f8
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (rw [readMem_congr (fun i hi => hfrm _ (by simp only [pGp, pPk, pSig, pRid, pRecv] at hAh ⊢; omega))];
       assumption)
  have hd4 : readMem m4.mem 0 168 = dataSeg := by rw [readMem_congr (fun i hi => hfrm _ (by omega)), hd]
  have hsb4 : readMem m4.mem 928 16 = u128 s := by rw [readMem_congr (fun i hi => hfrm _ (by omega)), hsb]
  have henc := refund_encode hd4 r ht s hid4 hsb4
  have hlen := refund_len r ht s hsl hpk
  rw [batch_twp_seqs_append _ _ (by simp [RBL]) (by simp [RENDL])]
  refine twp_mono (refB_twp hb4 e9 hE hrt4 hrc4 hA hAh hsl hpk hcap hrl) ?_
  rintro m5 c5 ⟨hb5, hc5⟩
  rw [henc] at hb5
  obtain ⟨⟨hr1, hrd⟩, hfr5, e9', e14', e15'⟩ := hb5
  simp only [List.length_append, hrl] at hr1 hrd
  have hn5 : ArenaCore.Bytes.leToNat (readMem m5.mem 3112 4) = n := by
    rw [readMem_congr (fun i hi => hfr5 _ (by simp only [RB] at *; omega)),
      readMem_congr (fun i hi => hfrm _ (by omega)), hn]
  simp only [RENDL, seqs, ldCell, stCell]
  have hr1' : m5.regs 1 = 28164 + L + (gasRefundReceipt r ht s).encode.length := by
    simp only [RB] at hr1; omega
  simp only [RB, AR] at hcap
  bvc [e14', e15', hr1', hn5, rm_wm_out]
  refine ⟨?_, by simpa only [RB] using hrd, ?_, ?_, ?_, by rw [e9', e9], by omega⟩
  · rw [rm_wm_leN, leToNat_leN' (by omega)]
  · rw [rm_wm_leN, leToNat_leN' (by omega)]
  · rw [readMem_congr (fun i hi => hfr5 _ (by omega)), hid4]
  · intro a h1 h2 h3
    rw [writeMem_apply_out _ _ _ _ _ (by omega), writeMem_apply_out _ _ _ _ _ (by omega),
      hfr5 a (by simp only [RB, AR]; omega), hfrm a (by omega)]

theorem bf_refl {m : M} {base : Nat} (h1 : m.regs 1 = base) (h14 : m.regs 14 = 8) (h15 : m.regs 15 = 1)
    (lo hi : Nat) : BF m m base [] lo hi :=
  ⟨⟨by simp [h1], by simp [readMem_zero]⟩, fun _ _ => rfl, rfl, h14, h15⟩

set_option maxHeartbeats 2000000 in
theorem outB_twp {mo m : M} {E A : Nat} {r : Receipt} {bs : List UInt8}
    (hb : BF mo m S_OUT bs 1152 1285) (hbl : bs.length ≤ 36)
    (h9 : mo.regs 9 = E) (hE : E + 40 ≤ 19968) (hElo : 3584 ≤ E)
    (hrt : RtMem mo.mem E r A) (hrc : RcptMem mo.mem r A) (hA : 8844304 ≤ A) (hAh : pGp r A + 45 ≤ 13844304)
    (hrl : r.receiverId.length ≤ 64) :
    twp P (Inp pub cb pb) (seqs (APPL D_G 8 ++ (APPL S_A 16 ++ (OUT4 ++ OUT5)))) m (fun m' c =>
      BF mo m' S_OUT (bs ++ readMem mo.mem 120 8 ++ readMem mo.mem 896 16 ++
        (u32 r.receiverId.length ++ r.receiverId) ++ [UInt8.ofNat 2] ++ u32 0) 1152 1285 ∧ c ≤ 1500) := by
  have hpa : A ≤ pRecv r A := by simp only [pRecv]; omega
  have hpr : pRecv r A + r.receiverId.length = pRid r A := rfl
  have hpg : pRid r A + 32 ≤ pGp r A := by simp only [pGp, pPk, pSig]; omega
  have hbl1 := hb.1.1
  simp only [S_OUT] at hb ⊢
  rw [batch_twp_seqs_append _ _ (by simp [APPL]) (by simp [APPL])]
  refine twp_mono (app_bf hb (by simp) (by simp <;> omega) (by omega) (by simp [D_G]) (by simp [D_G])) ?_
  rintro m1 c1 ⟨hb1, hc1⟩
  rw [batch_twp_seqs_append _ _ (by simp [APPL]) (by simp [OUT4])]
  refine twp_mono (app_bf hb1 (by simp) (by simp <;> omega) (by omega) (by simp [S_A]) (by simp [S_A])) ?_
  rintro m2 c2 ⟨hb2, hc2⟩
  rw [batch_twp_seqs_append _ _ (by simp [OUT4]) (by simp [OUT5])]
  have hO4 : OUT4 = BRL 8 := rfl
  rw [hO4]
  refine twp_mono (brl_bf (o := 8) (sl := r.receiverId.length) (sp := pRecv r A) hb2 h9 hE (by omega) (by omega)
    hrt.f12 hrt.f8 hrc.recv (by omega) (by omega) (by omega) (by simp <;> omega) (by simp <;> omega) (by omega)
    ) ?_
  rintro m3 c3 ⟨hb3, hc3⟩
  simp only [OUT5]
  refine twp_cst_cons (by simp) (by omega) ?_
  have hb3' := bf_setReg (r := 2) (v := 2) hb3 (by decide) (by decide) (by decide) (by decide)
  rw [show [ST8 1 2, ADDI 1 1 1, CST 2 0, st32 1 2, ADDI 1 1 4] =
    [ST8 1 2, ADDI 1 1 1] ++ (CST 2 0 :: [st32 1 2, ADDI 1 1 4]) from rfl,
    batch_twp_seqs_append _ _ (by simp) (by simp)]
  refine twp_mono (byte_bf (v := 2) (x := 2) hb3' (by simp [setReg_apply]) (by omega) (by decide)
    (by simp <;> omega) (by simp <;> omega) (by omega)) ?_
  rintro m4 c4 ⟨hb4, hc4⟩
  refine twp_cst_cons (by simp) (by omega) ?_
  have hb4' := bf_setReg (r := 2) (v := 0) hb4 (by decide) (by decide) (by decide) (by decide)
  refine twp_mono (u32_bf (v := 2) (x := 0) hb4' (by simp [setReg_apply]) (by omega) (by decide) (by decide)
    (by decide) (by decide) (by simp <;> omega) (by simp <;> omega) (by omega)) ?_
  rintro m5 c5 ⟨hb5, hc5, -⟩
  refine ⟨?_, by omega⟩
  simp only [List.append_assoc, D_G, S_A] at hb5 ⊢
  exact hb5

set_option maxHeartbeats 2000000 in
theorem outA_twp {mo : M} {E A k : Nat} {r : Receipt} {idb : List UInt8}
    (hk1 : mo.regs 15 = 1) (hk8 : mo.regs 14 = 8) (h9 : mo.regs 9 = E) (hE : E + 40 ≤ 19968) (hElo : 3584 ≤ E)
    (hrt : RtMem mo.mem E r A) (hrc : RcptMem mo.mem r A) (hA : 8844304 ≤ A) (hAh : pGp r A + 45 ≤ 13844304)
    (h5 : mo.regs 5 = k) (hk : (k = 0 ∧ idb = []) ∨ (k = 1 ∧ readMem mo.mem 1088 32 = idb))
    (hrl : r.receiverId.length ≤ 64) :
    twp P (Inp pub cb pb) (seqs (OUT1 ++ (.ite 5 (seqs (APPL S_ID 32)) nop :: (APPL D_G 8 ++ (APPL S_A 16 ++
      (OUT4 ++ OUT5)))))) mo (fun m' c => BF mo m' S_OUT (u32 k ++ idb ++ readMem mo.mem 120 8 ++
        readMem mo.mem 896 16 ++ (u32 r.receiverId.length ++ r.receiverId) ++ [UInt8.ofNat 2] ++ u32 0) 1152 1285 ∧
      c ≤ 2000) := by
  have hpa : A ≤ pRecv r A := by simp only [pRecv]; omega
  have hpr : pRecv r A + r.receiverId.length = pRid r A := rfl
  have hpg : pRid r A + 32 ≤ pGp r A := by simp only [pGp, pPk, pSig]; omega
  have hk1' : k ≤ 1 := by rcases hk with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  simp only [OUT1]
  rw [batch_twp_seqs_append _ _ (by simp) (by simp)]
  refine twp_cst_cons (by simp) (by simp [S_OUT]) ?_
  have hb0 : BF mo ⟨setReg mo.regs 1 S_OUT, mo.mem⟩ 1152 [] 1152 1285 :=
    ⟨⟨by simp [setReg_apply, S_OUT], by simp [readMem_zero]⟩, fun _ _ => rfl, by simp [setReg_apply],
      by simp [setReg_apply, hk8], by simp [setReg_apply, hk1]⟩
  refine twp_mono (u32_bf (v := 5) (x := k) hb0 (by simp [setReg_apply, h5]) (by omega) (by decide) (by decide)
    (by decide) (by decide) (by simp) (by simp) (by omega)) ?_
  rintro m1 c1 ⟨hb1, hc1, hF1⟩
  have h51 : m1.regs 5 = k := by rw [hF1 5 (by decide)]; simp [setReg_apply, h5]
  rw [← List.singleton_append, batch_twp_seqs_append _ _ (by simp) (by simp [APPL])]
  simp only [seqs]
  have hm19 : m1.regs 9 = E := by rw [hb1.2.2.1, h9]
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, hid⟩
  · refine twp_ite_zero h51 ?_
    rw [twp_nop]
    refine twp_mono (outB_twp (r := r) hb1 (by simp) h9 hE hElo hrt hrc hA hAh hrl) ?_
    rintro m' c ⟨hb', hc⟩
    refine ⟨by simpa using hb', by omega⟩
  · refine twp_ite_ne (by rw [h51]; decide) ?_
    refine twp_mono (app_bf hb1 (by simp [S_OUT]) (by simp [S_OUT]) (by omega) (by simp [S_ID])
      (by simp [S_ID])) ?_
    rintro m2 c2 ⟨hb2, hc2⟩
    refine twp_mono (outB_twp (r := r) hb2 (by simp [S_ID]) h9 hE hElo hrt hrc hA hAh hrl) ?_
    rintro m' c ⟨hb', hc⟩
    refine ⟨by simpa [S_ID, hid] using hb', by omega⟩

set_option maxHeartbeats 2000000 in
theorem outC_twp {mo m : M} {E A i : Nat} {r : Receipt} {bs : List UInt8}
    (hb : BF mo m S_OUT bs 1152 1285) (h9 : mo.regs 9 = E) (hE : E + 40 ≤ 19968) (hElo : 3584 ≤ E)
    (hrt : RtMem mo.mem E r A) (hrc : RcptMem mo.mem r A) (hA : 8844304 ≤ A) (hAh : pGp r A + 45 ≤ 13844304)
    (hci : ArenaCore.Bytes.leToNat (readMem mo.mem 3168 4) = i) (hi : i < 256) (hbl : bs.length ≤ 133) :
    twp P (Inp pub cb pb) (seqs (OUT6 ++ (OUT7 ++ OUT8))) m (fun m' c =>
      readMem m'.mem (OL + 32 * i) 32 = ArenaCore.sha256 (u32 2 ++ r.receiptId ++ ArenaCore.sha256 bs) ∧
      (∀ a, ¬ (1152 ≤ a ∧ a < 1380) → ¬ (OL + 32 * i ≤ a ∧ a < OL + 32 * i + 32) → m'.mem a = mo.mem a) ∧
      m'.regs 8 = i ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 500) := by
  obtain ⟨⟨hr1, hrd⟩, hfr, e9, e14, e15⟩ := hb
  have hpr : pRid r A + 32 ≤ pGp r A := by simp only [pGp, pPk, pSig]; omega
  have hpa : A ≤ pRid r A := by simp only [pRid, pRecv]; omega
  have h16 : ArenaCore.Bytes.leToNat (readMem m.mem (E + 16) 4) = pRid r A := by
    rw [readMem_congr (fun j hj => hfr _ (by omega))]; exact hrt.f16
  simp only [OUT6, OUT7, OUT8, List.cons_append, List.nil_append, seqs, ldCell, S_OUT] at hr1 hrd ⊢
  bvc [hr1, e9, h9, e14, e15, h16, Nat.add_sub_cancel_left, rm_wm_out]
  refine ⟨by omega, ?_⟩
  refine twp_memcpy (n := 32) (by simp [setReg_apply, e15]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]; omega)
    (by simp [setReg_apply]; omega) (fun m1 c1 hm1 h1' hF hc => ?_)
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at hm1 h1'
  have f14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, e14]
  have f15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, e15]
  have hci1 : ArenaCore.Bytes.leToNat (readMem m1.mem 3168 4) = i := by
    rw [hm1, rm_wm_out _ _ _ _ _ _ (by omega), rm_wm_out _ _ _ _ _ _ (by omega), rm_wm_out _ _ _ _ _ _ (by omega),
      readMem_congr (fun j hj => hfr _ (by omega)), hci]
  have hleaf : readMem m1.mem 1312 68 = u32 2 ++ r.receiptId ++ ArenaCore.sha256 bs := by
    rw [show (68 : Nat) = 4 + 32 + 32 from rfl, readMem_add, readMem_add, hm1,
      rm_wm_out _ _ _ _ _ _ (by omega), rm_wm_self _ _ _ _ (ArenaCore.Bytes.leN_length _ _), rm_wm_self _ _ _ _ (by simp),
      rm_wm_out _ _ _ _ _ _ (by omega), rm_wm_out _ _ _ _ _ _ (by omega),
      readMem_congr (fun j hj => hfr _ (by omega)), hrc.rid,
      rm_wm_out _ _ _ _ _ _ (by omega), rm_wm_out _ _ _ _ _ _ (by omega),
      rm_wm_self _ _ _ _ (ArenaCore.sha256_length _), hrd, leN_eq]
    rfl
  bvc [f14, f15, hci1, hleaf]
  refine ⟨by omega, ?_, ?_, ?_⟩
  · rw [show 19968 + 32 * i = i * 32 + 19968 by omega, rm_wm_self _ _ _ _ (ArenaCore.sha256_length _)]
  · intro a h1 h2
    rw [writeMem_apply_out _ _ _ _ _ (by omega), hm1, writeMem_apply_out _ _ _ _ _ (by omega),
      writeMem_apply_out _ _ _ _ _ (by omega), writeMem_apply_out _ _ _ _ _ (by omega), hfr a (by omega)]
  · have : bs.length / 64 ≤ 2 := by omega
    omega

def OUTL : List Stmt := OUT1 ++ (.ite 5 (seqs (APPL S_ID 32)) nop :: (APPL D_G 8 ++ (APPL S_A 16 ++
  (OUT4 ++ (OUT5 ++ (OUT6 ++ (OUT7 ++ OUT8)))))))

set_option maxHeartbeats 2000000 in
theorem out_twp {mo : M} {E A k i : Nat} {r : Receipt} {idb : List UInt8}
    (hk1 : mo.regs 15 = 1) (hk8 : mo.regs 14 = 8) (h9 : mo.regs 9 = E) (hE : E + 40 ≤ 19968) (hElo : 3584 ≤ E)
    (hrt : RtMem mo.mem E r A) (hrc : RcptMem mo.mem r A) (hA : 8844304 ≤ A) (hAh : pGp r A + 45 ≤ 13844304)
    (h5 : mo.regs 5 = k) (hk : (k = 0 ∧ idb = []) ∨ (k = 1 ∧ readMem mo.mem 1088 32 = idb))
    (hrl : r.receiverId.length ≤ 64)
    (hci : ArenaCore.Bytes.leToNat (readMem mo.mem 3168 4) = i) (hi : i < 256) :
    twp P (Inp pub cb pb) (seqs OUTL) mo (fun m' c =>
      readMem m'.mem (OL + 32 * i) 32 = ArenaCore.sha256 (u32 2 ++ r.receiptId ++ ArenaCore.sha256
        (u32 k ++ idb ++ readMem mo.mem 120 8 ++ readMem mo.mem 896 16 ++
          (u32 r.receiverId.length ++ r.receiverId) ++ [UInt8.ofNat 2] ++ u32 0)) ∧
      (∀ a, ¬ (1152 ≤ a ∧ a < 1380) → ¬ (OL + 32 * i ≤ a ∧ a < OL + 32 * i + 32) → m'.mem a = mo.mem a) ∧
      m'.regs 8 = i ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 3000) := by
  have hidl : idb.length ≤ 32 := by
    rcases hk with ⟨-, rfl⟩ | ⟨-, h⟩
    · simp
    · rw [← h]; simp
  rw [show OUTL = (OUT1 ++ (.ite 5 (seqs (APPL S_ID 32)) nop :: (APPL D_G 8 ++ (APPL S_A 16 ++
    (OUT4 ++ OUT5))))) ++ (OUT6 ++ (OUT7 ++ OUT8)) by simp [OUTL],
    batch_twp_seqs_append _ _ (by simp [OUT1]) (by simp [OUT6])]
  refine twp_mono (outA_twp hk1 hk8 h9 hE hElo hrt hrc hA hAh h5 hk hrl) ?_
  rintro m1 c1 ⟨hb1, hc1⟩
  refine twp_mono (outC_twp hb1 h9 hE hElo hrt hrc hA hAh hci hi (by simp [u32_len]; omega)) ?_
  rintro m' c ⟨h1, h2, h3, h4, h5', hc⟩
  exact ⟨h1, h2, h3, h4, h5', by omega⟩

end

theorem pRefundOutcome_eq2 : pRefundOutcome = seqs (R0L ++ (.ite 6 (CST 5 0) (seqs RFL) :: OUTL)) := rfl

/-- What `pRefundOutcome` needs at entry. -/
structure RefPre (m : M) (E A L n i : Nat) (r : Receipt) (ctx : Ctx) (refs leaves : List UInt8) : Prop where
  k1 : m.regs 15 = 1
  k8 : m.regs 14 = 8
  data : readMem m.mem 0 168 = dataSeg
  r9 : m.regs 9 = E
  hE : E + 40 ≤ 19968
  Elo : 3584 ≤ E
  rt : RtMem m.mem E r A
  rc : RcptMem m.mem r A
  Alo : 8844304 ≤ A
  Ahi : pGp r A + 45 ≤ 13844304
  sigl : r.signerId.length ≤ 64
  pkwf : r.signerPk.wf = true
  ridl : r.receiptId.length = 32
  recvl : r.receiverId.length ≤ 64
  hgt : readMem m.mem 2645 8 = u64 ctx.blockHeight
  sa : readMem m.mem 896 16 = u128 (Params.G * burnP ctx r)
  sb : readMem m.mem 928 16 = u128 (surplusOf ctx r)
  surl : surplusOf ctx r < Params.two128
  rbend : ArenaCore.Bytes.leToNat (readMem m.mem 3116 4) = RB + 4 + L
  rbuf : readMem m.mem (RB + 4) L = refs
  rl : refs.length = L
  cap : RB + 4 + L + 289 ≤ AR
  nref : ArenaCore.Bytes.leToNat (readMem m.mem 3112 4) = n
  nl : n + 1 < 4294967296
  ci : ArenaCore.Bytes.leToNat (readMem m.mem 3168 4) = i
  il : i < 256
  ol : readMem m.mem OL (32 * i) = leaves

theorem data_gb {M0 : Nat → UInt8} (h : readMem M0 0 168 = dataSeg) : readMem M0 120 8 = u64 Params.G := by
  rw [data_sub h 120 8 (by decide)]; rfl

theorem u128_zero_iff {s : Nat} (h : s < Params.two128) : u128 s = List.replicate 16 0 ↔ s = 0 := by
  constructor
  · intro e
    have := NearSpec.leNat_leN 16 s (by simpa [Params.two128] using h)
    rw [show leN 16 s = u128 s from rfl, e] at this
    rw [← this]; decide
  · rintro rfl; decide

theorem leaf_eq (ctx : Ctx) (r : Receipt) (k : Nat) (idb g8 b16 : List UInt8)
    (hk : (k = 0 ∧ idb = [] ∧ refundOf ctx r = []) ∨
      (k = 1 ∧ idb = receiptIdFrom r.receiptId ctx.blockHeight 0 ∧
        refundOf ctx r = [gasRefundReceipt r ctx.blockHeight (surplusOf ctx r)]))
    (hg : g8 = u64 Params.G) (hb : b16 = u128 (Params.G * burnP ctx r)) :
    ArenaCore.sha256 (u32 2 ++ r.receiptId ++ ArenaCore.sha256 (u32 k ++ idb ++ g8 ++ b16 ++
      (u32 r.receiverId.length ++ r.receiverId) ++ [UInt8.ofNat 2] ++ u32 0)) = (outcomeOf ctx r).leaf := by
  subst hg hb
  simp only [Outcome.leaf, outcomeOf, Outcome.partialEncode, borshBytes]
  rcases hk with ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩ <;> rw [h] <;>
    simp [concatAll, List.append_assoc, gasRefundReceipt] <;> rfl

section
variable {pub cb pb : List UInt8}

set_option maxHeartbeats 4000000 in
theorem refundOutcome_twp {m : M} {E A L n i : Nat} {r : Receipt} {ctx : Ctx} {refs leaves : List UInt8}
    (hp : RefPre m E A L n i r ctx refs leaves) :
    twp P (Inp pub cb pb) pRefundOutcome m (fun m' c =>
      ArenaCore.Bytes.leToNat (readMem m'.mem 3116 4) =
        RB + 4 + L + (concatAll ((refundOf ctx r).map Receipt.encode)).length ∧
      readMem m'.mem (RB + 4) (L + (concatAll ((refundOf ctx r).map Receipt.encode)).length) =
        refs ++ concatAll ((refundOf ctx r).map Receipt.encode) ∧
      ArenaCore.Bytes.leToNat (readMem m'.mem 3112 4) = n + (refundOf ctx r).length ∧
      readMem m'.mem OL (32 * (i + 1)) = leaves ++ (outcomeOf ctx r).leaf ∧
      (concatAll ((refundOf ctx r).map Receipt.encode)).length ≤ 289 ∧
      (∀ a, ¬ (1088 ≤ a ∧ a < 1380) → ¬ (3112 ≤ a ∧ a < 3120) → ¬ (RB + 4 + L ≤ a ∧ a < AR) →
        ¬ (OL + 32 * i ≤ a ∧ a < OL + 32 * i + 32) → m'.mem a = m.mem a) ∧
      m'.regs 8 = i ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1 ∧ c ≤ 9000) := by
  rw [pRefundOutcome_eq2, batch_twp_seqs_append _ _ (by simp [R0L]) (by simp)]
  have hz16 : readMem m.mem 136 16 = List.replicate 16 0 := data_zero hp.data 16 (by omega)
  simp only [R0L, seqs]
  bvc [hp.k1, hp.k8, hz16, hp.sb]
  rw [← List.singleton_append, batch_twp_seqs_append _ _ (by simp) (by simp [OUTL, OUT1])]
  simp only [seqs]
  have hsl := hp.surl
  have hcap := hp.cap
  have hil := hp.il
  simp only [RB, AR] at hcap
  by_cases hs0 : surplusOf ctx r = 0
  · have hz : u128 (surplusOf ctx r) = List.replicate 16 0 := (u128_zero_iff hsl).2 hs0
    have href : refundOf ctx r = [] := by simp [refundOf, hs0]
    refine twp_ite_ne (by simp [setReg_apply, hz]) ?_
    rw [twp_op]
    refine ⟨rfl, _, rfl, ?_⟩
    refine twp_mono (out_twp (k := 0) (idb := []) (i := i) (by simp [setReg_apply, hp.k1])
      (by simp [setReg_apply, hp.k8]) (by simp [setReg_apply, hp.r9]) hp.hE hp.Elo hp.rt hp.rc hp.Alo hp.Ahi
      (by simp [setReg_apply]) (.inl ⟨rfl, rfl⟩) hp.recvl hp.ci hp.il) ?_
    rintro m' c ⟨h1, h2, h3, h4, h5, hc⟩
    simp only at h1
    rw [data_gb hp.data, hp.sa, leaf_eq ctx r 0 [] _ _ (.inl ⟨rfl, rfl, href⟩) rfl rfl] at h1
    rw [href]
    simp only [List.map_nil, concatAll, List.length_nil, Nat.add_zero, List.append_nil]
    have hfr : ∀ a, ¬ (1152 ≤ a ∧ a < 1380) → ¬ (OL + 32 * i ≤ a ∧ a < OL + 32 * i + 32) →
        m'.mem a = m.mem a := h2
    have hrb' := hp.rbend
    have hbuf' := hp.rbuf
    have hol' := hp.ol
    have hn' := hp.nref
    simp only [RB, OL] at hrb' hbuf' hol' hfr h1 ⊢
    refine ⟨?_, ?_, ?_, ?_, by simp, ?_, h3, h4, h5, by simp only [cost]; omega⟩
    · rw [readMem_congr (fun j hj => hfr _ (by omega) (by omega)), hrb']
    · rw [readMem_congr (fun j hj => hfr _ (by omega) (by omega)), hbuf']
    · rw [readMem_congr (fun j hj => hfr _ (by omega) (by omega)), hn']
    · rw [Nat.mul_add, Nat.mul_one, readMem_add, readMem_congr (fun j hj => hfr _ (by omega) (by omega)), hol', h1]
    · intro a h1' h2' h3' h4'
      exact hfr a (by omega) h4'
  · have hnz : ¬ u128 (surplusOf ctx r) = List.replicate 16 0 := fun h => hs0 ((u128_zero_iff hsl).1 h)
    have href : refundOf ctx r = [gasRefundReceipt r ctx.blockHeight (surplusOf ctx r)] := by
      simp [refundOf, hs0]
    refine twp_ite_zero (by simp [setReg_apply]; simpa using hnz) ?_
    refine twp_mono (refund_twp (m := ⟨_, m.mem⟩) (by simp [setReg_apply, hp.k1]) (by simp [setReg_apply, hp.k8])
      hp.data (by simp [setReg_apply, hp.r9]) hp.hE hp.Elo hp.rt hp.rc hp.Alo hp.Ahi hp.sigl hp.pkwf hp.ridl hp.hgt
      hp.rbend hp.rbuf hp.rl hp.cap hp.nref hp.nl hp.sb) ?_
    rintro m5 c5 ⟨r1, r2, r3, r4, r5, rfr, r9, r14, r15, rc5⟩
    have rfr' : ∀ a, ¬ (1088 ≤ a ∧ a < 1136) → ¬ (3112 ≤ a ∧ a < 3120) → ¬ (28164 + L ≤ a ∧ a < 117000) →
        m5.mem a = m.mem a := by simpa only [RB, AR] using rfr
    have hrt5 : RtMem m5.mem E r A := by
      have hE := hp.hE; have hElo := hp.Elo
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hp.rt
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (rw [readMem_congr (fun j hj => rfr' _ (by omega) (by omega) (by omega))]; assumption)
    have hrc5 : RcptMem m5.mem r A := by
      have hA := hp.Alo; have hAh := hp.Ahi
      have q1 : A ≤ pRecv r A := by simp only [pRecv]; omega
      have q2 : pRid r A = pRecv r A + r.receiverId.length := rfl
      have q3 : pSig r A = pRid r A + 37 := rfl
      have q4 : pPk r A = pSig r A + r.signerId.length := rfl
      have q5 : pGp r A = pPk r A + 1 + r.signerPk.data.length := rfl
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hp.rc
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (rw [readMem_congr (fun j hj => rfr' _ (by omega) (by omega) (by omega))]; assumption)
    have hci5 : ArenaCore.Bytes.leToNat (readMem m5.mem 3168 4) = i := by
      rw [readMem_congr (fun j hj => rfr' _ (by omega) (by omega) (by omega)), hp.ci]
    refine twp_mono (out_twp (k := 1) (i := i) r15 r14 r9 hp.hE hp.Elo hrt5 hrc5 hp.Alo hp.Ahi r5
      (.inr ⟨rfl, rfl⟩) hp.recvl hci5 hp.il) ?_
    rintro m' c ⟨h1, h2, h3, h4, h5, hc⟩
    have hd5 : readMem m5.mem 0 168 = dataSeg := by
      rw [readMem_congr (fun j hj => rfr' _ (by omega) (by omega) (by omega)), hp.data]
    have hsa5 : readMem m5.mem 896 16 = u128 (Params.G * burnP ctx r) := by
      rw [readMem_congr (fun j hj => rfr' _ (by omega) (by omega) (by omega)), hp.sa]
    rw [data_gb hd5, hsa5, r4, leaf_eq ctx r 1 _ _ _ (.inr ⟨rfl, rfl, href⟩) rfl rfl] at h1
    have hlen := refund_len r ctx.blockHeight (surplusOf ctx r) hp.sigl hp.pkwf
    rw [href]
    simp only [List.map_cons, List.map_nil, concatAll, List.append_nil, List.length_cons, List.length_nil]
    have hfr : ∀ a, ¬ (1152 ≤ a ∧ a < 1380) → ¬ (OL + 32 * i ≤ a ∧ a < OL + 32 * i + 32) →
        m'.mem a = m5.mem a := h2
    have hol' := hp.ol
    simp only [RB, OL, AR] at hol' hfr h1 r1 r2 ⊢
    refine ⟨?_, ?_, ?_, ?_, hlen, ?_, h3, h4, h5, by omega⟩
    · rw [readMem_congr (fun j hj => hfr _ (by omega) (by omega)), r1]
    · rw [readMem_congr (fun j hj => hfr _ (by omega) (by omega)), r2]
    · rw [readMem_congr (fun j hj => hfr _ (by omega) (by omega)), r3]
    · rw [Nat.mul_add, Nat.mul_one, readMem_add, readMem_congr (fun j hj => hfr _ (by omega) (by omega)),
        readMem_congr (fun j hj => rfr' _ (by omega) (by omega) (by omega)), hol', h1]
    · intro a h1' h2' h3' h4'
      rw [hfr a (by omega) h4', rfr' a (by omega) h2' h3']

end

end ReexecNpai

