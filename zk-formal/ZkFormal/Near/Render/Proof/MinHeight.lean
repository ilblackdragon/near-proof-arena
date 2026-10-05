import ZkFormal.Near.Render.Proof.ShaTab
import ZkFormal.Sha.Complete.Pad

/-!
# ZkFormal.Near.Render.Proof.MinHeight — the honest SHA table has at least 32 rows (R-L7-6)

Every rendered trace hashes the receipt-commitment message `RC`, i.e. at least one
SHA block: `1 + 17 = 18` rows, so `log ≥ 5`.
-/

namespace ZkFormal.Near.Render

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1 ZkFormal.Near

theorem shaClog2_go_ge (n : Nat) : ∀ fuel acc, acc ≤ Sha.Gen.clog2.go n fuel acc
  | 0, acc => Nat.le_refl _
  | fuel + 1, acc => by
    simp only [Sha.Gen.clog2.go]; split
    · exact Nat.le_refl _
    · exact Nat.le_trans (Nat.le_succ acc) (shaClog2_go_ge n fuel (acc + 1))

theorem shaClog2_step (n fuel acc : Nat) (h : ¬ n ≤ 2 ^ acc) :
    Sha.Gen.clog2.go n (fuel + 1) acc = Sha.Gen.clog2.go n fuel (acc + 1) := by
  rw [Sha.Gen.clog2.go, if_neg h]

theorem clog2_ge5 (n : Nat) (h : 17 ≤ n) : 5 ≤ Sha.Gen.clog2 n := by
  unfold Sha.Gen.clog2
  obtain ⟨f, hf⟩ : ∃ f, n = f + 5 := ⟨n - 5, by omega⟩
  have e : Sha.Gen.clog2.go n n 0 = Sha.Gen.clog2.go n f 5 := by
    conv => lhs; arg 2; rw [hf]
    rw [shaClog2_step n _ 0 (by simp; omega), shaClog2_step n _ 1 (by simp; omega),
      shaClog2_step n _ 2 (by simp; omega), shaClog2_step n _ 3 (by simp; omega),
      shaClog2_step n _ 4 (by simp; omega)]
  rw [e]; exact shaClog2_go_ge _ _ _

theorem msgRows_length_ge (M : Sha.Gen.Msg) : 18 ≤ (Sha.Gen.msgRows M).length := by
  have hp := Sha.Complete.pad_len M.bytes
  have hb : 1 ≤ (Sha.Gen.msgBlocks M.bytes).length := by
    unfold Sha.Gen.msgBlocks; rw [Sha.Complete.chunks_length]; omega
  obtain ⟨k, hk⟩ : ∃ k, (Sha.Gen.msgBlocks M.bytes).length = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hb).symm⟩
  unfold Sha.Gen.msgRows
  rw [List.length_cons, hk, List.range_succ (n := k), List.flatMap_append, List.length_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, List.length_map,
    List.length_range, List.length_cons, List.length_nil]
  omega

theorem render_sha_log_ge (c : Claim) (e : Ext) : 5 ≤ (render c e).log T_SHA := by
  rw [render_sha_log]
  show 5 ≤ Sha.Gen.honestLog (shaMsgsOf c e)
  unfold Sha.Gen.honestLog
  refine Nat.le_trans (clog2_ge5 _ ?_) (Nat.le_max_right _ _)
  unfold Sha.Gen.honestRows shaMsgsOf shaMsgs bundle
  simp only [List.map_append, List.flatMap_append, List.length_append]
  have : 18 ≤ ((List.map (fun m => (⟨m.id, m.bytes, true⟩ : Sha.Gen.Msg)) (rcptMsgs (mkInfo c e))).flatMap
      Sha.Gen.msgRows).length := by
    unfold rcptMsgs
    simp only [List.cons_append, List.map_cons, List.flatMap_cons, List.length_append]
    have := msgRows_length_ge ⟨msgId K_RC 0, rcBytes (mkInfo c e), true⟩
    omega
  omega

end ZkFormal.Near.Render
