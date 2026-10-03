import ReexecNpai.Spec.BatchAux3
import ReexecNpai.Spec.Walk

/-!
# Batch proofs, part 4: one receipt (`pOne`)
-/

set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-! ## Facts about receipt `j` -/

structure RFacts (r : Receipt) : Prop where
  rl2 : 2 ≤ r.receiverId.length
  rl : r.receiverId.length ≤ 64
  sl : r.signerId.length ≤ 64
  pl : r.predecessorId.length ≤ 64
  pk : r.signerPk.wf = true
  rid : r.receiptId.length = 32
  gp : r.gasPrice < Params.two128
  dep : r.deposit < Params.two128

theorem rfacts {r : Receipt} (h : r.inSlice = true) : RFacts r := by
  simp only [Receipt.inSlice, Receipt.wf, AccountId.valid, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hp2, hp64⟩, -⟩, ⟨hr2, hr64⟩, -⟩, ⟨hs2, hs64⟩, -⟩, hpk⟩, hrid⟩, hgp⟩, hdep⟩, -⟩, -⟩ := h
  exact ⟨hr2, hr64, hs64, hp64, hpk, hrid, hgp, hdep⟩

theorem pGp_enc (r : Receipt) (A : Nat) (h : r.receiptId.length = 32) :
    pGp r A + 45 = A + r.encode.length := by
  simp [pGp, pPk, pSig, pRid, pRecv, Receipt.encode, borshBytes, PublicKey.encode, u8, u32_len, u128_len,
    NearSpec.leN_length]
  omega

theorem batch_claim_seg {cb : List UInt8} {m : M} (h : ClaimIn cb m) (o n : Nat) (hn : o + n ≤ 309) :
    readMem m.mem (2560 + o) n = seg cb o n := by
  have := readMem_sub h.claim o n hn
  simpa [seg, CLM] using this

theorem claim_h {cb : List UInt8} {m : M} (h : ClaimIn cb m) :
    readMem m.mem 2645 8 = u64 (claimOf cb).ctx.blockHeight := by
  have hl := h.shape.1
  rw [show (2645 : Nat) = 2560 + 85 from rfl, batch_claim_seg h 85 8 (by omega)]
  simp only [Claim.ctx, claimOf]
  exact (leN_seg (by omega)).symm

theorem claim_g {cb : List UInt8} {m : M} (h : ClaimIn cb m) :
    readMem m.mem 2653 16 = u128 (claimOf cb).ctx.blockGasPrice ∧
      (claimOf cb).ctx.blockGasPrice < Params.two128 := by
  have hl := h.shape.1
  rw [show (2653 : Nat) = 2560 + 93 from rfl, batch_claim_seg h 93 16 (by omega)]
  simp only [Claim.ctx, claimOf]
  have := leNat_seg_lt (cb := cb) (o := 93) (n := 16) (by omega)
  exact ⟨(leN_seg (by omega)).symm, this⟩

theorem rtMem_keep {M0 M1 : Nat → UInt8} {E A : Nat} {r : Receipt} (h : RtMem M0 E r A)
    (hk : ∀ a, E ≤ a → a < E + 40 → M1 a = M0 a) : RtMem M1 E r A := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [readMem_congr (fun j hj => hk _ (by omega) (by omega))]; assumption)

theorem rcptMem_keep {M0 M1 : Nat → UInt8} {A : Nat} {r : Receipt} (h : RcptMem M0 r A)
    (hA : 8844304 ≤ A) (hk : ∀ a, A ≤ a → a < pGp r A + 45 → M1 a = M0 a) : RcptMem M1 r A := by
  have q1 : A ≤ pRecv r A := by simp only [pRecv]; omega
  have q2 : pRid r A = pRecv r A + r.receiverId.length := rfl
  have q3 : pSig r A = pRid r A + 37 := rfl
  have q4 : pPk r A = pSig r A + r.signerId.length := rfl
  have q5 : pGp r A = pPk r A + 1 + r.signerPk.data.length := rfl
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [readMem_congr (fun j hj => hk _ (by omega) (by omega))]; assumption)

theorem hasVal_of_val {pb : List UInt8} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {j : Nat} (hj : j < A.length) (hv : A[j].val ≠ 0) : hasVal A[j].nf = true := by
  obtain ⟨e, he, -, -, -, -, -, hval, -⟩ := hw.nodes j hj
  rw [List.getElem?_eq_getElem hj] at he
  cases he
  cases hh : hasVal A[j].nf
  · rw [hh] at hval; exact absurd hval hv
  · rfl

theorem walk_hasVal {A : List Ent} {K : List Nat} : ∀ {r : Nat} {key : List Nat} {f : Nat},
    Walk A K r key f → ∀ (hf : f < A.length), hasVal A[f].nf = true := by
  intro r key f hw
  induction hw with
  | leaf he hn =>
    intro hf; rw [List.getElem?_eq_getElem hf] at he; cases he; rw [hn]; rfl
  | brv he hn =>
    intro hf; rw [List.getElem?_eq_getElem hf] at he; cases he; rw [hn]; rfl
  | ext _ _ _ ih => exact ih
  | br _ _ _ _ ih => exact ih

theorem root_get_set {pb : List UInt8} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {vals : Nat → List UInt8} {key : List Nat} {f : Nat} (hwalk : Walk A K (rootRes A) key f) (nv : List UInt8) :
    (rootT A K vals).get key = some (vals f) ∧
      (rootT A K vals).set key nv = some (rootT A K (updVals vals f nv)) := by
  have hl := hw.len_pos
  have he : A[A.length - 1]? = some A[A.length - 1] := List.getElem?_eq_getElem (by omega)
  have hr : rootRes A = A[A.length - 1].res := by simp only [rootRes]; rw [getD_eq_get (by omega)]
  rw [hr] at hwalk
  exact walk_get_set hw he hwalk nv

/-- The loop invariant after `j` receipts. -/
def JB (cb pb : List UInt8) (rs : List Receipt) (R : Nat) (A : List Ent) (K : List Nat) (j : Nat) (m : M) : Prop :=
  ∃ st vals, applyAll (claimOf cb).ctx ⟨rootT A K (vals0 pb A), [], [], 0, 0⟩ (rs.take j) = some st ∧
    TrieSt cb pb rs R A K vals m ∧ rootT A K vals = st.trie ∧ BatchMem st m ∧
    st.outcomes.length = j ∧ st.refunds.length ≤ j ∧
    (concatAll (st.refunds.map Receipt.encode)).length ≤ 289 * j ∧ st.tokensBurnt < Params.two128

theorem batchMem_mem {acc : Acc} {m m' : M} (h : BatchMem acc m) (hm : m'.mem = m.mem) : BatchMem acc m' := by
  obtain ⟨h1, ⟨h2, h3⟩, h4, h5, h6⟩ := h
  exact ⟨by rw [hm]; exact h1, ⟨by simp only [rd32, hm] at h2 ⊢; exact h2, by rw [hm]; exact h3⟩,
    by simp only [rd32, hm] at h4 ⊢; exact h4, by rw [hm]; exact h5, h6⟩

theorem JB_regs {cb pb : List UInt8} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {j : Nat} {m : M}
    (h : JB cb pb rs R A K j m) (i t v w : Nat) (hi : i ≠ 14 ∧ i ≠ 15) (ht : t ≠ 14 ∧ t ≠ 15) :
    JB cb pb rs R A K j { m with regs := setReg (setReg m.regs i v) t w } := by
  obtain ⟨st, vals, h1, h2, h3, h4, h5⟩ := h
  refine ⟨st, vals, h1, trieSt_frame h2 ?_ ?_ (fun _ _ => rfl), h3, batchMem_mem h4 rfl, h5⟩
  · simp [setReg_apply, Ne.symm hi.1, Ne.symm ht.1]
  · simp [setReg_apply, Ne.symm hi.2, Ne.symm ht.2]

theorem jb_next {cb pb : List UInt8} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat}
    {m m' : M} {st : Acc} {vals : Nat → List UInt8} {j f : Nat}
    (hj : j < rs.length)
    (hap : applyAll (claimOf cb).ctx ⟨rootT A K (vals0 pb A), [], [], 0, 0⟩ (rs.take j) = some st)
    (hT : TrieSt cb pb rs R A K vals m) (hroot : rootT A K vals = st.trie) (hBM : BatchMem st m)
    (hol : st.outcomes.length = j) (hrl : st.refunds.length ≤ j)
    (henc : (concatAll (st.refunds.map Receipt.encode)).length ≤ 289 * j)
    (hf : f < A.length) (hwalk : Walk A K (rootRes A) (accountKeyPath rs[j].receiverId) f)
    (h72 : vlenAt pb A[f] = 72) (hok : StepOk (claimOf cb).ctx st.tokensBurnt rs[j] (vals f))
    (h14 : m'.regs 14 = m.regs 14) (h15 : m'.regs 15 = m.regs 15)
    (hfr : ∀ a, ¬ Scr a → ¬ (A[f].val ≤ a ∧ a < A[f].val + 16) → m'.mem a = m.mem a)
    (hV : readMem m'.mem A[f].val 72 = newVal (vals f) (acctAmt (vals f) + rs[j].deposit))
    (hrb : ArenaCore.Bytes.leToNat (readMem m'.mem 3116 4) = RB + 4 +
      (concatAll (st.refunds.map Receipt.encode)).length +
      (concatAll ((refundOf (claimOf cb).ctx rs[j]).map Receipt.encode)).length)
    (hbuf : readMem m'.mem (RB + 4) ((concatAll (st.refunds.map Receipt.encode)).length +
      (concatAll ((refundOf (claimOf cb).ctx rs[j]).map Receipt.encode)).length) =
      concatAll (st.refunds.map Receipt.encode) ++ concatAll ((refundOf (claimOf cb).ctx rs[j]).map Receipt.encode))
    (hnr : ArenaCore.Bytes.leToNat (readMem m'.mem 3112 4) = st.refunds.length + (refundOf (claimOf cb).ctx rs[j]).length)
    (hlv : readMem m'.mem OL (32 * (j + 1)) =
      concatAll (st.outcomes.map Outcome.leaf) ++ (outcomeOf (claimOf cb).ctx rs[j]).leaf)
    (hnl : (concatAll ((refundOf (claimOf cb).ctx rs[j]).map Receipt.encode)).length ≤ 289)
    (htk : readMem m'.mem 3088 16 = u128 (st.tokensBurnt + Params.G * burnP (claimOf cb).ctx rs[j])) :
    JB cb pb rs R A K (j + 1) m' := by
  have hw := hT.tok.wf
  have hhv := walk_hasVal hwalk hf
  obtain ⟨hg, hs⟩ := root_get_set hw (vals := vals) hwalk (newVal (vals f) (acctAmt (vals f) + rs[j].deposit))
  rw [hroot] at hg hs
  have hstep := applyReceipt_some hg hok hs
  refine ⟨stepAcc (claimOf cb).ctx st rs[j] (rootT A K (updVals vals f (newVal (vals f) (acctAmt (vals f) +
    rs[j].deposit)))), updVals vals f (newVal (vals f) (acctAmt (vals f) + rs[j].deposit)), ?_, ?_, rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [applyAll_take_succ hap hj, hstep]
  · exact trieSt_upd hT hf hhv h72 h14 h15 hfr hV
  · have hj255 : j ≤ 255 := by
      have := hT.ok.n_max; simp only [Params.maxBatch] at this; omega
    simp only [RB, OL] at hrb hbuf hlv
    refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp only [stepAcc, rd32, List.map_append, concatAll_append,
      List.length_append, List.map_cons, List.map_nil, List.length_cons, List.length_nil, RB, AR, OL,
      C_RBEND, C_NREF, C_TOK]
    · rw [hol]; simpa [concatAll] using hlv
    · omega
    · exact hbuf
    · exact hnr
    · exact htk
    · omega
  · simp [stepAcc, hol]
  · simp only [stepAcc, List.length_append]
    have : (refundOf (claimOf cb).ctx rs[j]).length ≤ 1 := by
      simp only [refundOf]; split <;> simp
    omega
  · simp only [stepAcc, List.map_append, concatAll_append, List.length_append]; omega
  · exact hok.c6
def P1L : List Stmt := [stCell C_I 8, CST 9 64, MUL 9 8 9, ADDI 9 9 RT, ADDI 0 9 8, ld32 1 0, ADDI 0 9 12, ld32 2 0]

theorem pOne_eq : pOne = seqs (P1L ++ ([pKey] ++ ([pWalk] ++ ([pAccount] ++ ([pRefundOutcome] ++
    [ldCell 8 C_I, ldCell 7 C_N]))))) := rfl

section
variable {pub cb pb : List UInt8}

theorem p1_twp {m : M} {j pr rl : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8) (h8 : m.regs 8 = j)
    (hj : j < 256) (hpr : ArenaCore.Bytes.leToNat (readMem m.mem (RT + 64 * j + 8) 4) = pr)
    (hrl : ArenaCore.Bytes.leToNat (readMem m.mem (RT + 64 * j + 12) 4) = rl) :
    twp P (Inp pub cb pb) (seqs P1L) m (fun m1 c => m1.regs 9 = RT + 64 * j ∧ m1.regs 1 = pr ∧
      m1.regs 2 = rl ∧ m1.mem = writeMem m.mem 3168 4 (ArenaCore.Bytes.leN 4 j) ∧
      m1.regs 14 = 8 ∧ m1.regs 15 = 1 ∧ c ≤ 100) := by
  simp only [P1L, seqs, stCell]
  bvc [hk1, hk8, h8]
  simp only [RT] at hpr hrl
  refine ⟨by omega, ?_, ?_⟩
  · rw [rm_wm_out _ _ _ _ _ _ (by omega), show j * 64 + 3584 + 8 = 3584 + 64 * j + 8 by omega, hpr]
  · rw [rm_wm_out _ _ _ _ _ _ (by omega), show j * 64 + 3584 + 12 = 3584 + 64 * j + 12 by omega, hrl]


theorem refundOutcome_wp {m : M} {E A L n i : Nat} {r : Receipt} {ctx : Ctx} {refs leaves : List UInt8}
    (hp : RefPre m E A L n i r ctx refs leaves) :
    wp P (Inp pub cb pb) pRefundOutcome m (fun m' =>
      ArenaCore.Bytes.leToNat (readMem m'.mem 3116 4) =
        RB + 4 + L + (concatAll ((refundOf ctx r).map Receipt.encode)).length ∧
      readMem m'.mem (RB + 4) (L + (concatAll ((refundOf ctx r).map Receipt.encode)).length) =
        refs ++ concatAll ((refundOf ctx r).map Receipt.encode) ∧
      ArenaCore.Bytes.leToNat (readMem m'.mem 3112 4) = n + (refundOf ctx r).length ∧
      readMem m'.mem OL (32 * (i + 1)) = leaves ++ (outcomeOf ctx r).leaf ∧
      (concatAll ((refundOf ctx r).map Receipt.encode)).length ≤ 289 ∧
      (∀ a, ¬ (1088 ≤ a ∧ a < 1380) → ¬ (3112 ≤ a ∧ a < 3120) → ¬ (RB + 4 + L ≤ a ∧ a < AR) →
        ¬ (OL + 32 * i ≤ a ∧ a < OL + 32 * i + 32) → m'.mem a = m.mem a) ∧
      m'.regs 8 = i ∧ m'.regs 14 = 8 ∧ m'.regs 15 = 1) :=
  wp_of_spec (refundOutcome_twp hp) (fun _ _ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ =>
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)

/-- Facts about receipt `j` at the start of its iteration. -/
structure ItFacts (cb pb : List UInt8) (rs : List Receipt) (R : Nat) (j : Nat) (m : M) : Prop where
  hj : j < rs.length
  j256 : j < 256
  rf : RFacts rs[j]
  rc : RcptMem m.mem rs[j] (PF + rOff rs j)
  rt : RtMem m.mem (RT + 64 * j) rs[j] (PF + rOff rs j)
  gpR : pGp rs[j] (PF + rOff rs j) + 45 ≤ PF + R
  Rle : PF + R ≤ 13844304

theorem itFacts {cb pb : List UInt8} {rs : List Receipt} {R : Nat} {j : Nat} {m : M}
    (h : RcptsMem cb pb rs R m) (hj : j < rs.length) : ItFacts cb pb rs R j m := by
  have rf := rfacts (List.all_eq_true.1 h.ok.slice rs[j] (List.getElem_mem hj))
  obtain ⟨hrc0, hR⟩ := rcpt_at h hj
  have hge := pGp_enc rs[j] (PF + rOff rs j) rf.rid
  have hRl : PF + R ≤ 13844304 := by
    have := h.ok.Rle; have := h.plen; simp only [PF, PMAX] at *; omega
  have hn := h.ok.n_max
  simp only [Params.maxBatch] at hn
  exact ⟨hj, by omega, rf, rcptMem_of rf.rid hrc0, rtMem_of (h.rt j hj) (by simp only [PF] at *; omega),
    by omega, hRl⟩

/-- Facts after `pKey; pWalk` (state `m3`), relative to the iteration start `m`. -/
structure AfterWalk (m m3 : M) (j f : Nat) : Prop where
  fr : ∀ a, ¬ (512 ≤ a ∧ a < 896) → ¬ (3168 ≤ a ∧ a < 3172) → m3.mem a = m.mem a
  ci : readMem m3.mem 3168 4 = ArenaCore.Bytes.leN 4 j
  r0 : m3.regs 0 = f
  r9 : m3.regs 9 = RT + 64 * j
  k8 : m3.regs 14 = 8
  k1 : m3.regs 15 = 1

theorem vlen_of {pb : List UInt8} {A : List Ent} {K : List Nat} {vals : Nat → List UInt8} {m : M} {f : Nat}
    (h : TrieMem pb A K vals m) (hf : f < A.length) (hh : hasVal A[f].nf = true) :
    vlenAt pb A[f] = ArenaCore.Bytes.leToNat (readMem m.mem (A[f].val - 4) 4) := by
  rw [h.lmem f hf hh, leToNat_eq]; rfl

set_option maxHeartbeats 4000000 in
theorem tail_wp {m m3 : M} {st : Acc} {vals : Nat → List UInt8} {j f : Nat}
    {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat}
    (hj : j < rs.length)
    (hap : applyAll (claimOf cb).ctx ⟨rootT A K (vals0 pb A), [], [], 0, 0⟩ (rs.take j) = some st)
    (hT : TrieSt cb pb rs R A K vals m) (hroot : rootT A K vals = st.trie) (hBM : BatchMem st m)
    (hol : st.outcomes.length = j) (hrl : st.refunds.length ≤ j)
    (henc : (concatAll (st.refunds.map Receipt.encode)).length ≤ 289 * j)
    (htok : st.tokensBurnt < Params.two128)
    (haw : AfterWalk m m3 j f) (hf : f < A.length)
    (hwk : A[f].val ≠ 0 → Walk A K (rootRes A) (accountKeyPath rs[j].receiverId) f) :
    wp P (Inp pub cb pb) (seqs ([pAccount] ++ ([pRefundOutcome] ++ [ldCell 8 C_I, ldCell 7 C_N]))) m3
      (fun m' => JB cb pb rs R A K (j + 1) m' ∧ m'.regs 8 = j ∧ m'.regs 7 = rs.length) := by
  have it := itFacts hT.toRcptsMem hj
  have hw := hT.tok.wf
  have hAl := hw.len_le
  simp only [NCAP] at hAl
  have hkeep3 : ∀ a, ¬ Scr a → m3.mem a = m.mem a := fun a ha => haw.fr a (by simp only [Scr] at ha; omega)
    (by simp only [Scr] at ha; omega)
  have T3 := trieSt_frame hT (by rw [haw.k8, hT.k8]) (by rw [haw.k1, hT.k1]) hkeep3
  have eo := entOk hw hf
  have hrstR := rst_ge hw hf
  have hpl := hT.plen
  have hlenv := (T3.tmem.amem f hf).2.2.2.2.2
  simp only [rd32] at hlenv
  rw [show AR + 24 * f + 20 = f * 24 + 117020 by simp only [AR]; omega] at hlenv
  have hcg := claim_g T3.toClaimIn
  have htk3 : readMem m3.mem 3088 16 = u128 st.tokensBurnt := by
    rw [readMem_congr (fun i hi => haw.fr _ (by omega) (by omega))]; exact hBM.tokens
  have hRl := it.Rle
  have hpre : AccPreW m3 f (RT + 64 * j) A[f].val rs[j] (PF + rOff rs j) (claimOf cb).ctx.blockGasPrice
      st.tokensBurnt := by
    refine ⟨haw.k1, haw.k8, T3.data, haw.r0, by omega, haw.r9, by simp only [RT]; have := it.j256; omega,
      by simp only [RT]; omega, hlenv, ?_, ?_, rtMem_keep it.rt (fun a h1 h2 => hkeep3 a (by simp only [Scr, RT] at *; have := it.j256; omega)),
      rcptMem_keep it.rc (by simp only [PF]; omega) (fun a h1 h2 => hkeep3 a (by simp only [Scr, PF] at *; omega)),
      by simp only [PF]; omega, ?_, by have := it.gpR; simp only [PF] at hRl this ⊢; omega, hcg.1, hcg.2, htk3, htok, it.rf.gp,
      it.rf.dep⟩
    · intro hv
      have hh := hasVal_of_val hw hf hv
      have e1 := (eo.hv hh)
      have e2 := eo.pend; have e3 := eo.rst
      simp only [PF, PMAX] at hpl e1 e2 e3 ⊢
      split at e1 <;> omega
    · intro h72
      by_cases hv : A[f].val = 0
      · rw [hv]; omega
      · have hh := hasVal_of_val hw hf hv
        have hvl := vlen_of T3.tmem hf hh
        rw [h72] at hvl
        have e1 := (eo.hv hh)
        have e2 := eo.pend
        simp only [PF, PMAX] at hpl e1 e2 ⊢
        split at e1 <;> omega
    · intro hv
      have hh := hasVal_of_val hw hf hv
      have := (eo.hv hh).1
      have := it.gpR
      omega
  rw [batch_wp_seqs_append _ _ (by simp) (by simp)]
  refine wp_mono (account_wp (ctx := (claimOf cb).ctx) hpre) ?_
  rintro m4 ⟨hV0, h72, hok, hpost⟩
  obtain ⟨pV, pA, pB, pT, pfr, p9, p14, p15⟩ := hpost
  have hh := hasVal_of_val hw hf hV0
  have hwalk := hwk hV0
  have hvl : vlenAt pb A[f] = 72 := by rw [vlen_of T3.tmem hf hh]; exact h72
  have hvals : readMem m3.mem A[f].val 72 = vals f := by
    have := (T3.tmem.vmem f hf hh).1; rwa [hvl] at this
  rw [hvals] at hok pV
  have eh := eo.hv hh
  have hVr : PF + R + 9 ≤ A[f].val := by omega
  have hVr' : 8844313 + R ≤ A[f].val := by simp only [PF] at hVr; omega
  -- memory at m4 relative to m
  have hfr4 : ∀ a, ¬ Scr a → ¬ (A[f].val ≤ a ∧ a < A[f].val + 16) → m4.mem a = m.mem a := by
    intro a h1 h2
    rw [pfr a (by simp only [Scr] at h1; omega) (by simp only [Scr] at h1; omega) h2, hkeep3 a h1]
  have hfm : ∀ a, ¬ (512 ≤ a ∧ a < 1056) → ¬ (3088 ≤ a ∧ a < 3104) → ¬ (3168 ≤ a ∧ a < 3172) →
      ¬ (A[f].val ≤ a ∧ a < A[f].val + 16) → m4.mem a = m.mem a := by
    intro a h1 h2 h3 h4
    rw [pfr a (by omega) h2 h4, haw.fr a (by omega) h3]
  have hn := hT.ok.n_max
  simp only [Params.maxBatch] at hn
  have hrefcap := hBM.rbcap
  have hRB := hBM.refunds
  simp only [rd32] at hRB
  have hrp : RefPre m4 (RT + 64 * j) (PF + rOff rs j) (concatAll (st.refunds.map Receipt.encode)).length
      st.refunds.length j rs[j] (claimOf cb).ctx (concatAll (st.refunds.map Receipt.encode))
      (concatAll (st.outcomes.map Outcome.leaf)) := by
    refine ⟨p15, p14, ?_, p9, by simp only [RT]; have := it.j256; omega, by simp only [RT]; omega,
      rtMem_keep it.rt (fun a h1 h2 => hfm a (by simp only [RT] at *; have := it.j256; omega)
        (by simp only [RT] at *; omega) (by simp only [RT] at *; have := it.j256; omega)
        (by simp only [RT] at *; have := it.j256; omega)),
      rcptMem_keep it.rc (by simp only [PF]; omega)
        (fun a h1 h2 => hfr4 a (by simp only [Scr, PF] at *; omega) (by have := it.gpR; omega)),
      by simp only [PF]; omega, by have := it.gpR; simp only [PF] at hRl this ⊢; omega,
      it.rf.sl, it.rf.pk, it.rf.rid, it.rf.rl, ?_, ?_, ?_, hok.c5, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [readMem_congr (fun i hi => hfm _ (by omega) (by omega) (by omega) (by omega))]; exact hT.data
    · rw [readMem_congr (fun i hi => hfm _ (by omega) (by omega) (by omega) (by omega))]
      exact claim_h hT.toClaimIn
    · exact pA
    · exact pB
    · rw [readMem_congr (fun i hi => hfm _ (by omega) (by omega) (by omega) (by omega))]
      simp only [C_RBEND] at hRB; exact hRB.1
    · rw [readMem_congr (fun i hi => hfm _ (by simp only [RB] at *; omega) (by simp only [RB] at *; omega) (by simp only [RB] at *; omega) (by simp only [RB] at *; omega))]
      exact hRB.2
    · simp only [RB, AR] at hrefcap ⊢; omega
    · rw [readMem_congr (fun i hi => hfm _ (by omega) (by omega) (by omega) (by omega))]
      have := hBM.nref; simp only [rd32, C_NREF] at this; exact this
    · omega
    · rw [readMem_congr (fun i hi => pfr _ (by omega) (by omega) (by omega)), haw.ci]
      exact leToNat_leN' (by have := it.j256; omega)
    · exact it.j256
    · have hl := hBM.leaves
      rw [hol] at hl
      have := it.j256
      rw [readMem_congr (fun i hi => hfm _ (by simp only [OL] at *; omega) (by simp only [OL] at *; omega)
        (by simp only [OL] at *; omega) (by simp only [OL] at *; omega))]
      exact hl
  rw [batch_wp_seqs_append _ _ (by simp) (by simp)]
  refine wp_mono (refundOutcome_wp hrp) ?_
  rintro m5 ⟨q1, q2, q3, q4, q5, q6, q8, q14, q15⟩
  have hci5 : ArenaCore.Bytes.leToNat (readMem m5.mem 3168 4) = j := by
    rw [readMem_congr (fun i hi => q6 _ (by omega) (by omega) (by simp only [RB, AR] at *; omega)
      (by simp only [OL]; omega)),
      readMem_congr (fun i hi => pfr _ (by omega) (by omega) (by omega)), haw.ci]
    exact leToNat_leN' (by have := it.j256; omega)
  have hcn5 : ArenaCore.Bytes.leToNat (readMem m5.mem 3076 4) = rs.length := by
    rw [readMem_congr (fun i hi => q6 _ (by omega) (by omega) (by simp only [RB, AR] at *; omega)
      (by simp only [OL]; omega)),
      readMem_congr (fun i hi => hfm _ (by omega) (by omega) (by omega) (by omega))]
    have := hT.nC; simp only [rd32, C_N] at this; exact this
  simp only [seqs, ldCell]
  bvc [q14, q15, hci5, hcn5]
  have q6' : ∀ a, 8844304 ≤ a → m5.mem a = m4.mem a := fun a ha =>
    q6 a (by omega) (by omega) (by simp only [RB, AR] at *; omega) (by simp only [OL]; omega)
  have hVm : readMem m5.mem A[f].val 72 = newVal (vals f) (acctAmt (vals f) + rs[j].deposit) := by
    rw [readMem_congr (fun i hi => q6' _ (by omega)), show (72 : Nat) = 16 + 56 from rfl, readMem_add, pV,
      readMem_congr (fun i hi => pfr _ (by omega) (by omega) (by omega)),
      readMem_sub hvals 16 56 (by omega)]
    rw [newVal, List.take_of_length_le (by rw [← hvals]; simp)]
  refine jb_next hj hap hT hroot hBM hol hrl henc hf hwalk hvl hok (by simp [setReg_apply, q14, hT.k8])
    (by simp [setReg_apply, q15, hT.k1]) ?_ hVm q1 q2 q3 q4 q5 ?_
  · intro a h1 h2
    simp only [Scr] at h1
    rw [q6 a (by omega) (by omega) (by simp only [RB, AR] at *; omega) (by simp only [OL] at *; omega)]
    exact hfm a (by omega) (by omega) (by omega) h2
  · rw [readMem_congr (fun i hi => q6 _ (by omega) (by omega) (by simp only [RB, AR] at *; omega)
      (by simp only [OL]; omega))]
    exact pT

set_option maxHeartbeats 4000000 in
theorem tail_twp {m m3 : M} {st : Acc} {vals : Nat → List UInt8} {j f : Nat}
    {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat}
    (hj : j < rs.length)
    (hap : applyAll (claimOf cb).ctx ⟨rootT A K (vals0 pb A), [], [], 0, 0⟩ (rs.take j) = some st)
    (hT : TrieSt cb pb rs R A K vals m) (hroot : rootT A K vals = st.trie) (hBM : BatchMem st m)
    (hol : st.outcomes.length = j) (hrl : st.refunds.length ≤ j)
    (henc : (concatAll (st.refunds.map Receipt.encode)).length ≤ 289 * j)
    (htok : st.tokensBurnt < Params.two128)
    (haw : AfterWalk m m3 j f) (hf : f < A.length)
    (hwalk : Walk A K (rootRes A) (accountKeyPath rs[j].receiverId) f)
    (hok : StepOk (claimOf cb).ctx st.tokensBurnt rs[j] (vals f)) :
    twp P (Inp pub cb pb) (seqs ([pAccount] ++ ([pRefundOutcome] ++ [ldCell 8 C_I, ldCell 7 C_N]))) m3
      (fun m' c => JB cb pb rs R A K (j + 1) m' ∧ m'.regs 8 = j ∧ m'.regs 7 = rs.length ∧ c ≤ 16000) := by
  have it := itFacts hT.toRcptsMem hj
  have hw := hT.tok.wf
  have hAl := hw.len_le
  simp only [NCAP] at hAl
  have hkeep3 : ∀ a, ¬ Scr a → m3.mem a = m.mem a := fun a ha => haw.fr a (by simp only [Scr] at ha; omega)
    (by simp only [Scr] at ha; omega)
  have T3 := trieSt_frame hT (by rw [haw.k8, hT.k8]) (by rw [haw.k1, hT.k1]) hkeep3
  have eo := entOk hw hf
  have hrstR := rst_ge hw hf
  have hpl := hT.plen
  have hlenv := (T3.tmem.amem f hf).2.2.2.2.2
  simp only [rd32] at hlenv
  rw [show AR + 24 * f + 20 = f * 24 + 117020 by simp only [AR]; omega] at hlenv
  have hcg := claim_g T3.toClaimIn
  have htk3 : readMem m3.mem 3088 16 = u128 st.tokensBurnt := by
    rw [readMem_congr (fun i hi => haw.fr _ (by omega) (by omega))]; exact hBM.tokens
  have hRl := it.Rle
  have hpre : AccPreW m3 f (RT + 64 * j) A[f].val rs[j] (PF + rOff rs j) (claimOf cb).ctx.blockGasPrice
      st.tokensBurnt := by
    refine ⟨haw.k1, haw.k8, T3.data, haw.r0, by omega, haw.r9, by simp only [RT]; have := it.j256; omega,
      by simp only [RT]; omega, hlenv, ?_, ?_, rtMem_keep it.rt (fun a h1 h2 => hkeep3 a (by simp only [Scr, RT] at *; have := it.j256; omega)),
      rcptMem_keep it.rc (by simp only [PF]; omega) (fun a h1 h2 => hkeep3 a (by simp only [Scr, PF] at *; omega)),
      by simp only [PF]; omega, ?_, by have := it.gpR; simp only [PF] at hRl this ⊢; omega, hcg.1, hcg.2, htk3, htok, it.rf.gp,
      it.rf.dep⟩
    · intro hv
      have hh := hasVal_of_val hw hf hv
      have e1 := (eo.hv hh)
      have e2 := eo.pend; have e3 := eo.rst
      simp only [PF, PMAX] at hpl e1 e2 e3 ⊢
      split at e1 <;> omega
    · intro h72
      by_cases hv : A[f].val = 0
      · rw [hv]; omega
      · have hh := hasVal_of_val hw hf hv
        have hvl := vlen_of T3.tmem hf hh
        rw [h72] at hvl
        have e1 := (eo.hv hh)
        have e2 := eo.pend
        simp only [PF, PMAX] at hpl e1 e2 ⊢
        split at e1 <;> omega
    · intro hv
      have hh := hasVal_of_val hw hf hv
      have := (eo.hv hh).1
      have := it.gpR
      omega
  have hh := walk_hasVal hwalk hf
  have hV0 : A[f].val ≠ 0 := by have := (eo.hv hh).1; omega
  have hvl : vlenAt pb A[f] = 72 := by rw [← (T3.tmem.vmem f hf hh).2]; exact hok.len
  have h72 : ArenaCore.Bytes.leToNat (readMem m3.mem (A[f].val - 4) 4) = 72 := by
    rw [← vlen_of T3.tmem hf hh]; exact hvl
  have hvals : readMem m3.mem A[f].val 72 = vals f := by
    have := (T3.tmem.vmem f hf hh).1; rwa [hvl] at this
  rw [batch_twp_seqs_append _ _ (by simp) (by simp)]
  refine twp_mono (account_twp (ctx := (claimOf cb).ctx) (hpre.pre hV0 h72) h72 (by rw [hvals]; exact hok)) ?_
  rintro m4 c4 ⟨hpost, hc4⟩
  obtain ⟨pV, pA, pB, pT, pfr, p9, p14, p15⟩ := hpost
  rw [hvals] at pV
  have eh := eo.hv hh
  have hVr : PF + R + 9 ≤ A[f].val := by omega
  have hVr' : 8844313 + R ≤ A[f].val := by simp only [PF] at hVr; omega
  -- memory at m4 relative to m
  have hfr4 : ∀ a, ¬ Scr a → ¬ (A[f].val ≤ a ∧ a < A[f].val + 16) → m4.mem a = m.mem a := by
    intro a h1 h2
    rw [pfr a (by simp only [Scr] at h1; omega) (by simp only [Scr] at h1; omega) h2, hkeep3 a h1]
  have hfm : ∀ a, ¬ (512 ≤ a ∧ a < 1056) → ¬ (3088 ≤ a ∧ a < 3104) → ¬ (3168 ≤ a ∧ a < 3172) →
      ¬ (A[f].val ≤ a ∧ a < A[f].val + 16) → m4.mem a = m.mem a := by
    intro a h1 h2 h3 h4
    rw [pfr a (by omega) h2 h4, haw.fr a (by omega) h3]
  have hn := hT.ok.n_max
  simp only [Params.maxBatch] at hn
  have hrefcap := hBM.rbcap
  have hRB := hBM.refunds
  simp only [rd32] at hRB
  have hrp : RefPre m4 (RT + 64 * j) (PF + rOff rs j) (concatAll (st.refunds.map Receipt.encode)).length
      st.refunds.length j rs[j] (claimOf cb).ctx (concatAll (st.refunds.map Receipt.encode))
      (concatAll (st.outcomes.map Outcome.leaf)) := by
    refine ⟨p15, p14, ?_, p9, by simp only [RT]; have := it.j256; omega, by simp only [RT]; omega,
      rtMem_keep it.rt (fun a h1 h2 => hfm a (by simp only [RT] at *; have := it.j256; omega)
        (by simp only [RT] at *; omega) (by simp only [RT] at *; have := it.j256; omega)
        (by simp only [RT] at *; have := it.j256; omega)),
      rcptMem_keep it.rc (by simp only [PF]; omega)
        (fun a h1 h2 => hfr4 a (by simp only [Scr, PF] at *; omega) (by have := it.gpR; omega)),
      by simp only [PF]; omega, by have := it.gpR; simp only [PF] at hRl this ⊢; omega,
      it.rf.sl, it.rf.pk, it.rf.rid, it.rf.rl, ?_, ?_, ?_, hok.c5, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [readMem_congr (fun i hi => hfm _ (by omega) (by omega) (by omega) (by omega))]; exact hT.data
    · rw [readMem_congr (fun i hi => hfm _ (by omega) (by omega) (by omega) (by omega))]
      exact claim_h hT.toClaimIn
    · exact pA
    · exact pB
    · rw [readMem_congr (fun i hi => hfm _ (by omega) (by omega) (by omega) (by omega))]
      simp only [C_RBEND] at hRB; exact hRB.1
    · rw [readMem_congr (fun i hi => hfm _ (by simp only [RB] at *; omega) (by simp only [RB] at *; omega) (by simp only [RB] at *; omega) (by simp only [RB] at *; omega))]
      exact hRB.2
    · simp only [RB, AR] at hrefcap ⊢; omega
    · rw [readMem_congr (fun i hi => hfm _ (by omega) (by omega) (by omega) (by omega))]
      have := hBM.nref; simp only [rd32, C_NREF] at this; exact this
    · omega
    · rw [readMem_congr (fun i hi => pfr _ (by omega) (by omega) (by omega)), haw.ci]
      exact leToNat_leN' (by have := it.j256; omega)
    · exact it.j256
    · have hl := hBM.leaves
      rw [hol] at hl
      have := it.j256
      rw [readMem_congr (fun i hi => hfm _ (by simp only [OL] at *; omega) (by simp only [OL] at *; omega)
        (by simp only [OL] at *; omega) (by simp only [OL] at *; omega))]
      exact hl
  rw [batch_twp_seqs_append _ _ (by simp) (by simp)]
  refine twp_mono (refundOutcome_twp hrp) ?_
  rintro m5 c5 ⟨q1, q2, q3, q4, q5, q6, q8, q14, q15, hc5⟩
  have hci5 : ArenaCore.Bytes.leToNat (readMem m5.mem 3168 4) = j := by
    rw [readMem_congr (fun i hi => q6 _ (by omega) (by omega) (by simp only [RB, AR] at *; omega)
      (by simp only [OL]; omega)),
      readMem_congr (fun i hi => pfr _ (by omega) (by omega) (by omega)), haw.ci]
    exact leToNat_leN' (by have := it.j256; omega)
  have hcn5 : ArenaCore.Bytes.leToNat (readMem m5.mem 3076 4) = rs.length := by
    rw [readMem_congr (fun i hi => q6 _ (by omega) (by omega) (by simp only [RB, AR] at *; omega)
      (by simp only [OL]; omega)),
      readMem_congr (fun i hi => hfm _ (by omega) (by omega) (by omega) (by omega))]
    have := hT.nC; simp only [rd32, C_N] at this; exact this
  simp only [seqs, ldCell]
  bvc [q14, q15, hci5, hcn5]
  have q6' : ∀ a, 8844304 ≤ a → m5.mem a = m4.mem a := fun a ha =>
    q6 a (by omega) (by omega) (by simp only [RB, AR] at *; omega) (by simp only [OL]; omega)
  have hVm : readMem m5.mem A[f].val 72 = newVal (vals f) (acctAmt (vals f) + rs[j].deposit) := by
    rw [readMem_congr (fun i hi => q6' _ (by omega)), show (72 : Nat) = 16 + 56 from rfl, readMem_add, pV,
      readMem_congr (fun i hi => pfr _ (by omega) (by omega) (by omega)),
      readMem_sub hvals 16 56 (by omega)]
    rw [newVal, List.take_of_length_le (by rw [← hvals]; simp)]
  refine ⟨jb_next hj hap hT hroot hBM hol hrl henc hf hwalk hvl hok (by simp [setReg_apply, q14, hT.k8])
    (by simp [setReg_apply, q15, hT.k1]) ?_ hVm q1 q2 q3 q4 q5 ?_, by omega⟩
  · intro a h1 h2
    simp only [Scr] at h1
    rw [q6 a (by omega) (by omega) (by simp only [RB, AR] at *; omega) (by simp only [OL] at *; omega)]
    exact hfm a (by omega) (by omega) (by omega) h2
  · rw [readMem_congr (fun i hi => q6 _ (by omega) (by omega) (by simp only [RB, AR] at *; omega)
      (by simp only [OL]; omega))]
    exact pT

theorem key_facts (l : List UInt8) : (accountKeyPath l).length = 2 + 2 * l.length ∧
    ∀ x ∈ accountKeyPath l, x < 16 := by
  refine ⟨by simp [accountKeyPath, nibbles_length]; omega, fun x hx => ?_⟩
  have := nibbles_ok (0 :: l)
  simp only [nibblesOk, List.all_eq_true, decide_eq_true_eq] at this
  exact this x hx

set_option maxHeartbeats 4000000 in
theorem one_wp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {j : Nat}
    (hJ : JB cb pb rs R A K j m) (h8 : m.regs 8 = j) (hj : j < rs.length) :
    wp P (Inp pub cb pb) pOne m (fun m' => JB cb pb rs R A K (j + 1) m' ∧ m'.regs 8 = j ∧
      m'.regs 7 = rs.length) := by
  obtain ⟨st, vals, hap, hT, hroot, hBM, hol, hrl, henc, htok⟩ := hJ
  have it := itFacts hT.toRcptsMem hj
  have hRl := it.Rle
  have hgR := it.gpR
  have hq1 : PF + rOff rs j ≤ pRecv rs[j] (PF + rOff rs j) := by simp only [pRecv]; omega
  have hq2 : pRecv rs[j] (PF + rOff rs j) + rs[j].receiverId.length ≤ pGp rs[j] (PF + rOff rs j) := by
    simp only [pGp, pPk, pSig, pRid]; omega
  rw [pOne_eq, batch_wp_seqs_append _ _ (by simp [P1L]) (by simp)]
  refine wp_of_spec (p1_twp (pub := pub) (cb := cb) (pb := pb) hT.k1 hT.k8 h8 it.j256 it.rt.f8 it.rt.f12) ?_
  rintro m1 c ⟨e9, e1, e2, hM1, e14, e15, -⟩
  have hd1 : readMem m1.mem 0 168 = dataSeg := by rw [hM1, rm_wm_out _ _ _ _ _ _ (by omega)]; exact hT.data
  have hPF : PF = 8844304 := rfl
  have hrv1 : readMem m1.mem (m1.regs 1) (m1.regs 2) = rs[j].receiverId := by
    rw [e1, e2, hM1, rm_wm_out _ _ _ _ _ _ (by omega)]; exact it.rc.recv
  rw [batch_wp_seqs_append _ _ (by simp) (by simp)]
  have hrl64 := it.rf.rl
  refine wp_mono (key_wp (pub := pub) (cb := cb) (pb := pb) ⟨e15, e14, hd1⟩
    (by rw [e1, e2]; simp; omega) (by rw [e2]; exact hrl64)
    (.inl (by rw [e1]; simp only [S_KEY]; omega))) ?_
  rintro m2 ⟨hk2, h32, ⟨k14, k15, kfr⟩, hF2⟩
  rw [hrv1, e2] at hk2
  rw [e2] at h32
  obtain ⟨hkl, hk16⟩ := key_facts rs[j].receiverId
  rw [batch_wp_seqs_append _ _ (by simp) (by simp)]
  have hkeep2 : ∀ a, ¬ Scr a → m2.mem a = m.mem a := by
    intro a ha
    rw [kfr a (by simp only [Scr] at ha; first | omega | (simp only [S_KEY]; omega)), hM1, writeMem_apply_out _ _ _ _ _ (by simp only [Scr] at ha; omega)]
  have T2 := trieSt_frame hT (by rw [k14, e14, hT.k8]) (by rw [k15, e15, hT.k1]) hkeep2
  refine wp_mono (walk_wp T2 (key := accountKeyPath rs[j].receiverId) (by rw [hkl]; exact hk2) hk16
    (by rw [hkl]; omega) (by rw [hkl]; exact h32)) ?_
  rintro m3 ⟨f, hf, h0, hwk, h93, ⟨w14, w15, wfr⟩⟩
  have haw : AfterWalk m m3 j f := by
    refine ⟨?_, ?_, h0, ?_, by rw [w14, k14, e14], by rw [w15, k15, e15]⟩
    · intro a h1 h2
      rw [wfr a (by first | omega | (simp only [S_HP]; omega)), kfr a (by first | omega | (simp only [S_KEY]; omega)), hM1,
        writeMem_apply_out _ _ _ _ _ (by omega)]
    · rw [readMem_congr (fun i hi => wfr _ (by first | omega | (simp only [S_HP]; omega))),
        readMem_congr (fun i hi => kfr _ (by first | omega | (simp only [S_KEY]; omega))), hM1, rm_wm_self _ _ _ _ (ArenaCore.Bytes.leN_length _ _)]
    · rw [h93, hF2 9 (by decide), e9]
  have hwk' : A[f].val ≠ 0 → Walk A K (rootRes A) (accountKeyPath rs[j].receiverId) f := by
    intro hv; apply hwk; rw [getD_eq_get hf]; exact hv
  exact tail_wp hj hap hT hroot hBM hol hrl henc htok haw hf hwk'

theorem applyReceipt_get {ctx : Ctx} {st st' : Acc} {r : Receipt} (h : applyReceipt ctx st r = some st') :
    ∃ raw, st.trie.get (accountKeyPath r.receiverId) = some raw := by
  simp only [applyReceipt] at h
  split at h
  · cases h
  · rename_i raw _; exact ⟨raw, by assumption⟩

theorem step_of_run {ctx : Ctx} {st0 st acc : Acc} {rs : List Receipt} {j : Nat} (hj : j < rs.length)
    (hap : applyAll ctx st0 (rs.take j) = some st) (hrun : applyAll ctx st0 rs = some acc) :
    ∃ st', applyReceipt ctx st rs[j] = some st' := by
  have h := applyAll_drop hap hrun
  rw [List.drop_eq_getElem_cons hj] at h
  simp only [applyAll] at h
  split at h
  · cases h
  · rename_i st' hs; exact ⟨st', hs⟩

set_option maxHeartbeats 4000000 in
theorem one_twp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {j : Nat} {acc : Acc}
    (hJ : JB cb pb rs R A K j m) (h8 : m.regs 8 = j) (hj : j < rs.length)
    (hrun : runBatch (claimOf cb).ctx (rootT A K (vals0 pb A)) rs = some acc) :
    twp P (Inp pub cb pb) pOne m (fun m' c => JB cb pb rs R A K (j + 1) m' ∧ m'.regs 8 = j ∧
      m'.regs 7 = rs.length ∧ c ≤ 78100) := by
  obtain ⟨st, vals, hap, hT, hroot, hBM, hol, hrl, henc, htok⟩ := hJ
  obtain ⟨st', hst⟩ := step_of_run hj hap hrun
  obtain ⟨raw, hg⟩ := applyReceipt_get hst
  have hw := hT.tok.wf
  have hlp := hw.len_pos
  rw [← hroot] at hg
  obtain ⟨f, hwalk0, hraw⟩ := get_walk hw (j := A.length - 1) (List.getElem?_eq_getElem (by omega)) hg
  have hwalk : Walk A K (rootRes A) (accountKeyPath rs[j].receiverId) f := by
    simp only [rootRes]; rw [getD_eq_get (by omega)]; exact hwalk0
  have hg' := hg
  rw [hroot] at hg'
  have hok := (applyReceipt_inv hg' hst).1
  rw [hraw] at hok
  have it := itFacts hT.toRcptsMem hj
  have hRl := it.Rle
  have hgR := it.gpR
  have hq1 : PF + rOff rs j ≤ pRecv rs[j] (PF + rOff rs j) := by simp only [pRecv]; omega
  have hq2 : pRecv rs[j] (PF + rOff rs j) + rs[j].receiverId.length ≤ pGp rs[j] (PF + rOff rs j) := by
    simp only [pGp, pPk, pSig, pRid]; omega
  have hPF : PF = 8844304 := rfl
  rw [pOne_eq, batch_twp_seqs_append _ _ (by simp [P1L]) (by simp)]
  refine twp_mono (p1_twp (pub := pub) (cb := cb) (pb := pb) hT.k1 hT.k8 h8 it.j256 it.rt.f8 it.rt.f12) ?_
  rintro m1 c1 ⟨e9, e1, e2, hM1, e14, e15, hc1⟩
  have hd1 : readMem m1.mem 0 168 = dataSeg := by rw [hM1, rm_wm_out _ _ _ _ _ _ (by omega)]; exact hT.data
  have hrv1 : readMem m1.mem (m1.regs 1) (m1.regs 2) = rs[j].receiverId := by
    rw [e1, e2, hM1, rm_wm_out _ _ _ _ _ _ (by omega)]; exact it.rc.recv
  rw [batch_twp_seqs_append _ _ (by simp) (by simp)]
  have hrl64 := it.rf.rl
  refine twp_mono (key_twp (pub := pub) (cb := cb) (pb := pb) ⟨e15, e14, hd1⟩
    (by rw [e1, e2]; simp; omega) (by rw [e2]; exact hrl64)
    (.inl (by rw [e1]; simp only [S_KEY]; omega))) ?_
  rintro m2 c2 ⟨hk2, h32, ⟨k14, k15, kfr⟩, hF2, hc2⟩
  rw [hrv1, e2] at hk2
  rw [e2] at h32
  obtain ⟨hkl, hk16⟩ := key_facts rs[j].receiverId
  rw [batch_twp_seqs_append _ _ (by simp) (by simp)]
  have hkeep2 : ∀ a, ¬ Scr a → m2.mem a = m.mem a := by
    intro a ha
    rw [kfr a (by simp only [Scr] at ha; first | omega | (simp only [S_KEY]; omega)), hM1,
      writeMem_apply_out _ _ _ _ _ (by simp only [Scr] at ha; omega)]
  have T2 := trieSt_frame hT (by rw [k14, e14, hT.k8]) (by rw [k15, e15, hT.k1]) hkeep2
  refine twp_mono (walk_twp T2 (key := accountKeyPath rs[j].receiverId) (by rw [hkl]; exact hk2) hk16
    (by rw [hkl]; omega) (by rw [hkl]; exact h32) hwalk) ?_
  rintro m3 c3 ⟨h0, hf, h93, ⟨w14, w15, wfr⟩, hc3⟩
  have haw : AfterWalk m m3 j f := by
    refine ⟨?_, ?_, h0, ?_, by rw [w14, k14, e14], by rw [w15, k15, e15]⟩
    · intro a h1 h2
      rw [wfr a (by first | omega | (simp only [S_HP]; omega)), kfr a (by first | omega | (simp only [S_KEY]; omega)), hM1,
        writeMem_apply_out _ _ _ _ _ (by omega)]
    · rw [readMem_congr (fun i hi => wfr _ (by first | omega | (simp only [S_HP]; omega))),
        readMem_congr (fun i hi => kfr _ (by first | omega | (simp only [S_KEY]; omega))), hM1,
        rm_wm_self _ _ _ _ (ArenaCore.Bytes.leN_length _ _)]
    · rw [h93, hF2 9 (by decide), e9]
  refine twp_mono (tail_twp hj hap hT hroot hBM hol hrl henc htok haw hf hwalk hok) ?_
  rintro m' c ⟨q1, q2, q3, hc⟩
  exact ⟨q1, q2, q3, by omega⟩

end

end ReexecNpai
