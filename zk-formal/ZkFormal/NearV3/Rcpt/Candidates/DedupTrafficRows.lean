import ZkFormal.NearV3.Rcpt.Candidates.DedupBlocks
namespace ZkFormal.NearV3.Rcpt.Candidates.DedupProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl SrcpV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal (DedupTable.table 24) tr tt pub)
include hL
/-- Row-local facts. -/
theorem local_nodup {r : Nat} (hr : r < tr.height tt) (hd : tr.cell tt r dup=0) :
    tr.cell tt r rt * tr.cell tt r sg = 0 ∧
    (tr.cell tt r rt = 1 → tr.cell tt r dup = 1 → tr.cell tt r L = 12) ∧
    (tr.cell tt r wf = 1 → tr.cell tt r sg = 1 ∧ tr.cell tt r pw = 0) ∧
    (tr.cell tt r wl = 1 → tr.cell tt r sg = 1 ∧ tr.cell tt r pw = 31) ∧
    tr.cell tt r sf = tr.cell tt r wf * (1 - tr.cell tt r wn) ∧
    tr.cell tt r sl = tr.cell tt r wl * (tr.cell tt r wn + tr.cell tt r lf) ∧
    (tr.cell tt r lf = 1 → tr.cell tt r wn = 0 ∧ tr.cell tt r dir = 0 ∧ tr.cell tt r aw = 1 ∧
      tr.cell tt r sg = 1) ∧
    (tr.cell tt r sg = 1 → tr.cell tt r aw = tr.cell tt r lf + (1 - tr.cell tt r lf) *
      (tr.cell tt r wn + tr.cell tt r dir - 2 * (tr.cell tt r wn * tr.cell tt r dir))) ∧
    (tr.cell tt r sg = 1 → tr.cell tt r aw = 1 → tr.cell tt r b = tr.cell tt r (reg 0)) ∧
    tr.cell tt r gD = tr.cell tt r rt + tr.cell tt r wf * tr.cell tt r aw ∧
    (tr.cell tt r rt = 1 → tr.cell tt r cId = (K_SRC : Fp) + 16 * tr.cell tt r qe ∧
      tr.cell tt r cLen = tr.cell tt r le) ∧
    (tr.cell tt r wf = 1 → tr.cell tt r lf = 1 → tr.cell tt r cId = (K_RC : Fp) + 16 * tr.cell tt r j ∧
      tr.cell tt r cLen = tr.cell tt r L) ∧
    (tr.cell tt r wf = 1 → tr.cell tt r aw = 1 → tr.cell tt r lf = 0 →
      tr.cell tt r cId = (K_SRC : Fp) + 16 * (tr.cell tt r q - 1) ∧ tr.cell tt r cLen = tr.cell tt r pl) ∧
    (tr.cell tt r gz = 1 → tr.cell tt r sl = 1) := by
  have h1 := old_row_of_nodup hL hr hd (.mul (c rt) (c sg)) (by simp [SrcpV3.constraints])
  have h2 := old_row_of_nodup hL hr hd (mul3 (c rt) (c dup) (sub (c L) (k 12))) (by simp [SrcpV3.constraints])
  have h3 := old_row_of_nodup hL hr hd (.mul (c wf) (Dsl.not (c sg))) (by simp [SrcpV3.constraints])
  have h4 := old_row_of_nodup hL hr hd (.mul (c wl) (Dsl.not (c sg))) (by simp [SrcpV3.constraints])
  have h5 := old_row_of_nodup hL hr hd (.mul (c wf) (c pw)) (by simp [SrcpV3.constraints])
  have h6 := old_row_of_nodup hL hr hd (.mul (c wl) (sub (c pw) (k 31))) (by simp [SrcpV3.constraints])
  have h7 := old_row_of_nodup hL hr hd (sub (c sf) (.mul (c wf) (Dsl.not (c wn)))) (by simp [SrcpV3.constraints])
  have h8 := old_row_of_nodup hL hr hd (sub (c sl) (.mul (c wl) (.add (c wn) (c lf)))) (by simp [SrcpV3.constraints])
  have h9 := old_row_of_nodup hL hr hd (.mul (c lf) (c wn)) (by simp [SrcpV3.constraints])
  have h10 := old_row_of_nodup hL hr hd (.mul (c lf) (c dir)) (by simp [SrcpV3.constraints])
  have h11 := old_row_of_nodup hL hr hd (.mul (c lf) (Dsl.not (c aw))) (by simp [SrcpV3.constraints])
  have h12 := old_row_of_nodup hL hr hd (.mul (c lf) (Dsl.not (c sg))) (by simp [SrcpV3.constraints])
  have h13 := old_row_of_nodup hL hr hd (.mul (c sg) (sub (c aw) (.add (c lf) (.mul (Dsl.not (c lf))
      (sub (.add (c wn) (c dir)) (smul 2 (.mul (c wn) (c dir)))))))) (by simp [SrcpV3.constraints])
  have h14 := old_row_of_nodup hL hr hd (mul3 (c sg) (c aw) (sub (c b) (c (reg 0)))) (by simp [SrcpV3.constraints])
  have h15 := old_row_of_nodup hL hr hd (sub (c gD) (.add (c rt) (.mul (c wf) (c aw)))) (by simp [SrcpV3.constraints])
  have h16 := old_row_of_nodup hL hr hd (.mul (c rt) (sub (c cId) (mid K_SRC (c qe)))) (by simp [SrcpV3.constraints])
  have h17 := old_row_of_nodup hL hr hd (.mul (c rt) (sub (c cLen) (c le))) (by simp [SrcpV3.constraints])
  have h18 := old_row_of_nodup hL hr hd (mul3 (c wf) (c lf) (sub (c cId) (mid K_RC (c j)))) (by simp [SrcpV3.constraints])
  have h19 := old_row_of_nodup hL hr hd (mul3 (c wf) (c lf) (sub (c cLen) (c L))) (by simp [SrcpV3.constraints])
  have h20 := old_row_of_nodup hL hr hd (.mul (mul3 (c wf) (c aw) (Dsl.not (c lf))) (sub (c cId) (mid K_SRC (sub (c q) (k 1)))))
    (by simp [SrcpV3.constraints])
  have h21 := old_row_of_nodup hL hr hd (.mul (mul3 (c wf) (c aw) (Dsl.not (c lf))) (sub (c cLen) (c pl)))
    (by simp [SrcpV3.constraints])
  have h22 := old_row_of_nodup hL hr hd (.mul (c gz) (Dsl.not (c sl))) (by simp [SrcpV3.constraints])
  simp only [eval_mul, eval_mul3, eval_c, eval_not, eval_sub, eval_add, eval_k, eval_smul, eval_mid] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
  refine ⟨h1, fun ha hd => ?_, fun h => ?_, fun h => ?_, by grind, by grind, fun h => ?_, fun h => ?_,
    fun h1' h2' => ?_, by grind, fun h => ?_, fun ha hb' => ?_, fun ha hb' hc' => ?_, fun h => ?_⟩
  · rw [ha, hd] at h2; grind
  · rw [h] at h3 h5; exact ⟨by grind, by grind⟩
  · rw [h] at h4 h6; exact ⟨by grind, by grind⟩
  · rw [h] at h9 h10 h11 h12; exact ⟨by grind, by grind, by grind, by grind⟩
  · rw [h] at h13; grind
  · rw [h1', h2'] at h14; grind
  · rw [h] at h16 h17; exact ⟨by grind, by grind⟩
  · rw [ha, hb'] at h18 h19; exact ⟨by grind, by grind⟩
  · rw [ha, hb', hc'] at h20 h21; exact ⟨by grind, by grind⟩
  · rw [h] at h22; grind


end ZkFormal.NearV3.Rcpt.Candidates.DedupProof
