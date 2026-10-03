import ReexecNpai.Spec.BatchAux4

/-!
# Phase spec: applying the receipts

Proof structure (helper files `BatchAux1`–`BatchAux4`):
* `BatchAux1`: `applyAll`/`applyReceipt` in closed form, data segment, receipt fields in memory,
  arena layout and the trie-state frame/update lemmas, macro rules;
* `BatchAux2`: `pAccount` (`account_wp`, `account_twp`);
* `BatchAux3`: `pRefundOutcome` (`refundOutcome_twp`);
* `BatchAux4`: one receipt (`one_wp`, `one_twp`) and the loop invariant `JB`;
* here: the prefix of `pBatch` and the receipt loop.
-/

set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

section
variable {pub cb pb : Bytes}

def BPL : List Stmt := [CST 0 0, stCell C_NREF 0, CST 0 (RB + 4), stCell C_RBEND 0, CST 1 C_TOK, CST 2 D_ZERO,
  CST 3 16, memcpy 1 2 3 4, ldCell 7 C_N, CST 8 0]

theorem pBatch_eq : pBatch = seqs (BPL ++ [forUp 8 7 6 pOne]) := rfl

set_option maxHeartbeats 2000000 in
theorem bpre_twp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat}
    (h : TrieSt cb pb rs R A K (vals0 pb A) m) :
    twp P (Inp pub cb pb) (seqs BPL) m (fun m' c => JB cb pb rs R A K 0 m' ∧ m'.regs 8 = 0 ∧
      m'.regs 7 = rs.length ∧ c ≤ 300) := by
  have hk1 := h.k1
  have hk8 := h.k8
  simp only [BPL, seqs, stCell, ldCell]
  bvc [hk1, hk8]
  refine twp_memcpy (n := 16) (by simp [setReg_apply, hk1]) (by simp [setReg_apply])
    (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) (fun m1 c1 hm1 _ hF hc1 => ?_)
  simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte] at hm1
  have e14 : m1.regs 14 = 8 := by rw [hF 14 (by decide)]; simp [setReg_apply, hk8]
  have e15 : m1.regs 15 = 1 := by rw [hF 15 (by decide)]; simp [setReg_apply, hk1]
  have hfr : ∀ a, ¬ Scr a → m1.mem a = m.mem a := by
    intro a ha
    simp only [Scr] at ha
    rw [hm1, writeMem_apply_out _ _ _ _ _ (by omega), writeMem_apply_out _ _ _ _ _ (by omega),
      writeMem_apply_out _ _ _ _ _ (by omega)]
  have hcn : ArenaCore.Bytes.leToNat (readMem m1.mem 3076 4) = rs.length := by
    rw [readMem_congr (fun i hi => hfr _ (by simp only [Scr]; omega))]
    have := h.nC; simp only [rd32, C_N] at this; exact this
  bvc [e14, e15, hcn]
  refine ⟨?_, by omega⟩
  refine ⟨⟨rootT A K (vals0 pb A), [], [], 0, 0⟩, vals0 pb A, rfl,
    trieSt_frame h (by simp [setReg_apply, e14, hk8]) (by simp [setReg_apply, e15, hk1]) hfr, rfl, ?_, rfl,
    by simp, by simp [concatAll], by simp [Params.two128]⟩
  have hz : readMem m.mem 136 16 = List.replicate 16 0 := data_zero h.data 16 (by omega)
  refine ⟨by simp [readMem_zero, concatAll], ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [rd32, C_RBEND, List.map_nil, concatAll, List.length_nil, Nat.add_zero, RB]
    rw [hm1, rm_wm_out _ _ _ _ _ _ (by omega), rm_wm_leN, leToNat_leN' (by omega)]
  · simp [readMem_zero, concatAll]
  · simp only [rd32, C_NREF, List.length_nil]
    rw [hm1, rm_wm_out _ _ _ _ _ _ (by omega), rm_wm_out _ _ _ _ _ _ (by omega), rm_wm_leN,
      leToNat_leN' (by omega)]
  · simp only [C_TOK]
    rw [hm1, rm_wm_self _ _ _ _ (by simp), rm_wm_out _ _ _ _ _ _ (by omega), rm_wm_out _ _ _ _ _ _ (by omega), hz]
    rfl
  · simp [RB, AR, concatAll]


theorem JB_final {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {m : M}
    (h : JB cb pb rs R A K rs.length m) : ∃ acc vals,
      runBatch (claimOf cb).ctx (rootT A K (vals0 pb A)) rs = some acc ∧
      TrieSt cb pb rs R A K vals m ∧ rootT A K vals = acc.trie ∧ BatchMem acc m := by
  obtain ⟨st, vals, hap, hT, hroot, hBM, -⟩ := h
  rw [List.take_length] at hap
  exact ⟨st, vals, hap, hT, hroot, hBM⟩

theorem batch_wp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat}
    (h : TrieSt cb pb rs R A K (vals0 pb A) m) :
    wp P (Inp pub cb pb) pBatch m (fun m' => ∃ acc vals,
      runBatch (claimOf cb).ctx (rootT A K (vals0 pb A)) rs = some acc ∧
      TrieSt cb pb rs R A K vals m' ∧ rootT A K vals = acc.trie ∧ BatchMem acc m') := by
  have hn := h.ok.n_max
  simp only [Params.maxBatch] at hn
  rw [pBatch_eq, batch_wp_seqs_append _ _ (by simp [BPL]) (by simp)]
  refine wp_of_spec (bpre_twp h) ?_
  rintro m0 c ⟨hJ, h8, h7, -⟩
  simp only [seqs]
  refine wp_forUp (i := 8) (n := 7) (t := 6) (by decide) (by decide) (by decide)
    (J := fun j x => JB cb pb rs R A K j x) (N := rs.length) (by omega)
    (fun j x v w hx => JB_regs hx 8 6 v w (by decide) (by decide)) hJ h8 h7 ?_ ?_
  · intro j x hj hx hi hn'
    exact one_wp hx hi hj
  · intro x hx _
    exact JB_final hx

theorem batch_twp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat}
    (h : TrieSt cb pb rs R A K (vals0 pb A) m) {acc : Acc}
    (hr : runBatch (claimOf cb).ctx (rootT A K (vals0 pb A)) rs = some acc) :
    twp P (Inp pub cb pb) pBatch m (fun m' c => ∃ vals, TrieSt cb pb rs R A K vals m' ∧
      rootT A K vals = acc.trie ∧ BatchMem acc m' ∧ c ≤ 20000000) := by
  have hn := h.ok.n_max
  simp only [Params.maxBatch] at hn
  rw [pBatch_eq, batch_twp_seqs_append _ _ (by simp [BPL]) (by simp)]
  refine twp_mono (bpre_twp h) ?_
  rintro m0 c0 ⟨hJ, h8, h7, hc0⟩
  simp only [seqs]
  refine twp_forUp (i := 8) (n := 7) (t := 6) (by decide) (by decide) (by decide)
    (J := fun j x => JB cb pb rs R A K j x) (N := rs.length) (B := 78100) (by omega)
    (fun j x v w hx => JB_regs hx 8 6 v w (by decide) (by decide)) hJ h8 h7 ?_ ?_
  · intro j x hj hx hi hn'
    exact one_twp hx hi hj hr
  · intro x c hx _ hc
    obtain ⟨acc', vals, hr', hT, hroot, hBM⟩ := JB_final hx
    rw [hr] at hr'
    cases hr'
    refine ⟨vals, hT, hroot, hBM, ?_⟩
    have : rs.length * (78100 + 4) ≤ 256 * 78104 := Nat.mul_le_mul hn (by omega)
    omega

end

end ReexecNpai
