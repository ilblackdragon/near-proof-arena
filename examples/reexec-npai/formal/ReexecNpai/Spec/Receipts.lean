import ReexecNpai.Spec.State
import ReexecNpai.Spec.AccountId
import ReexecNpai.Spec.RcptAux7

/-!
# Phase spec: the receipts section

The proof is split over `RcptAux1` … `RcptAux7`:

* `RcptAux1`/`RcptAux2`: one receipt (`pReceipt`), field by field, against
  `decRcptPos` (`receipt_wp`, `receipt_twp`);
* `RcptAux3`: the receipt loop (`loop_wp`, `loop_twp`);
* `RcptAux4`: the prefix checks (count, bounds, gas);
* `RcptAux5`: the receipts commitment (`C_REND`, shard id copy, SHA-256, compare);
* `RcptAux6`: the distinct-receipt-id double loop;
* `RcptAux7`: the Lean-level facts and the final state.
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore Interp NearSpec NearSpec.TransferV1 RcptProof

theorem pReceipts_eq : pReceipts = seqs (LPre ++ [forUp 8 7 5 pReceipt] ++ LC1 ++ [memcpy 1 2 3 4] ++ LC3 ++
    [forUp 8 7 5 nBody]) := rfl

section
variable {pub cb pb : NearSpec.Bytes}

theorem receipts_wp {m : M} (h : Front cb pb m) (ht : TapesOK cb pb) :
    wp P (Inp pub cb pb) pReceipts m (fun m' => ∃ rs R, RcptsSt cb pb rs R m') := by
  rw [pReceipts_eq]
  refine wp_seqs_append _ _ _ _ (by simp [LPre, LPre1]) (by simp) ?_
  refine wp_seqs_append _ _ _ _ (by simp [LPre, LPre1]) (by simp [LC3]) ?_
  refine wp_seqs_append _ _ _ _ (by simp [LPre, LPre1]) (by simp) ?_
  refine wp_seqs_append _ _ _ _ (by simp [LPre, LPre1]) (by simp [LC1]) ?_
  refine wp_seqs_append _ _ _ _ (by simp [LPre, LPre1]) (by simp) ?_
  refine wp_mono (prefix_wp h) ?_
  rintro ms ⟨n, hpre⟩
  simp only [seqs]
  refine wp_mono (loop_wp hpre.toLBase hpre.r9 hpre.nmax hpre.r7 hpre.r8 hpre.r10 hpre.r6 hpre.n4) ?_
  rintro x ⟨rs, hI, hx7⟩
  have hk8 : x.regs 14 = 8 := by rw [hI.fr 14 (by decide)]; exact hpre.k8
  have hk1 : x.regs 15 = 1 := by rw [hI.fr 15 (by decide)]; exact hpre.k1
  have hRP : rOff rs n ≤ PMAX := Nat.le_trans hI.oLe hpre.plen
  refine wp_mono (c1_wp hk8 hI.r10 hRP) ?_
  rintro y ⟨hym, hy1, hy2, hy3, hFy⟩
  refine wp_of_spec (cp_spec (by rw [hFy 15 (by decide), hk1]) hy1 hy2 hy3) ?_
  rintro z c ⟨hzm, hFz, -⟩
  refine wp_mono (c3_wp (by rw [hFz 14 (by decide), hFy 14 (by decide), hk8])
    (by rw [hFz 15 (by decide), hFy 15 (by decide), hk1])
    (by rw [hFz 10 (by decide), hFy 10 (by decide), hI.r10]) hRP) ?_
  rintro w ⟨hsha, hwm, hw8, hFw⟩
  have hch : Chain cb pb n rs ms x y z w := ⟨hpre, hI, hym, hzm, hwm⟩
  refine wp_mono (nodup_wp rfl (by rw [hFw 14 (by decide), hFz 14 (by decide), hFy 14 (by decide), hk8]) hw8
    (by rw [hFw 7 (by decide), hFz 7 (by decide), hFy 7 (by decide), hx7]) hpre.nmax hch.ridOK) ?_
  rintro m' ⟨hd, hm', hF'⟩
  exact ⟨rs, rOff rs n, hch.st hm'
    (by rw [hF' 15 (by decide), hFw 15 (by decide), hFz 15 (by decide), hFy 15 (by decide), hk1])
    (by rw [hF' 14 (by decide), hFw 14 (by decide), hFz 14 (by decide), hFy 14 (by decide), hk8])
    (nodup_of_getD (by simp [hI.len]) hd) (hch.commit_iff.mp hsha)⟩

theorem receipts_twp {m : M} (h : Front cb pb m) {rs : List Receipt} {R : Nat}
    (hok : RcptsOK cb pb rs R) :
    twp P (Inp pub cb pb) pReceipts m (fun m' c => RcptsSt cb pb rs R m' ∧ c ≤ 6000000) := by
  have hRe := R_eq hok.dec hok.Rle hok.n4
  subst hRe
  have hmax : rs.length ≤ 256 := hok.n_max
  rw [pReceipts_eq]
  refine twp_seqs_append _ _ _ _ (by simp [LPre, LPre1]) (by simp) ?_
  refine twp_seqs_append _ _ _ _ (by simp [LPre, LPre1]) (by simp [LC3]) ?_
  refine twp_seqs_append _ _ _ _ (by simp [LPre, LPre1]) (by simp) ?_
  refine twp_seqs_append _ _ _ _ (by simp [LPre, LPre1]) (by simp [LC1]) ?_
  refine twp_seqs_append _ _ _ _ (by simp [LPre, LPre1]) (by simp) ?_
  refine twp_mono (prefix_twp h hok.n4 hok.count hok.cnt_claim hok.n_pos hmax hok.gas) ?_
  rintro ms c0 ⟨hpre, hc0⟩
  simp only [seqs]
  refine twp_mono (loop_twp hpre.toLBase hpre.r9 hpre.nmax hpre.r7 hpre.r8 hpre.r10 hpre.r6 hpre.n4 hok.dec
    hok.Rle hok.slice) ?_
  rintro x c1 ⟨hI, hx7, hc1⟩
  have hk8 : x.regs 14 = 8 := by rw [hI.fr 14 (by decide)]; exact hpre.k8
  have hk1 : x.regs 15 = 1 := by rw [hI.fr 15 (by decide)]; exact hpre.k1
  have hRP : rOff rs rs.length ≤ PMAX := Nat.le_trans hI.oLe hpre.plen
  refine twp_mono (c1_twp hk8 hI.r10 hRP) ?_
  rintro y c2 ⟨hym, hy1, hy2, hy3, hFy, hc2⟩
  refine twp_of_spec (cp_spec (by rw [hFy 15 (by decide), hk1]) hy1 hy2 hy3) ?_
  rintro z c3 ⟨hzm, hFz, hc3⟩
  have hch0 : ∀ w : M, w.mem = writeMem z.mem 1408 32
      (ArenaCore.sha256 (readMem z.mem SH8 (rOff rs rs.length + 8))) →
      Chain cb pb rs.length rs ms x y z w := fun w hwm => ⟨hpre, hI, hym, hzm, hwm⟩
  have hsha := ((hch0 ⟨z.regs, writeMem z.mem 1408 32
    (ArenaCore.sha256 (readMem z.mem SH8 (rOff rs rs.length + 8)))⟩ rfl).commit_iff).mpr hok.commit
  refine twp_mono (c3_twp (by rw [hFz 14 (by decide), hFy 14 (by decide), hk8])
    (by rw [hFz 15 (by decide), hFy 15 (by decide), hk1])
    (by rw [hFz 10 (by decide), hFy 10 (by decide), hI.r10]) hRP hsha) ?_
  rintro w c4 ⟨hwm, hw8, hFw, hc4⟩
  have hch := hch0 w hwm
  refine twp_mono (nodup_twp rfl (by rw [hFw 14 (by decide), hFz 14 (by decide), hFy 14 (by decide), hk8]) hw8
    (by rw [hFw 7 (by decide), hFz 7 (by decide), hFy 7 (by decide), hx7]) hpre.nmax hch.ridOK
    (fun a b hab hb => getD_of_nodup hok.nodup a b hab (by simp; omega))) ?_
  rintro m' c5 ⟨hm', hF', hc5⟩
  refine ⟨hch.st hm'
    (by rw [hF' 15 (by decide), hFw 15 (by decide), hFz 15 (by decide), hFy 15 (by decide), hk1])
    (by rw [hF' 14 (by decide), hFw 14 (by decide), hFz 14 (by decide), hFy 14 (by decide), hk8])
    hok.nodup hok.commit, ?_⟩
  have : rs.length * 8504 ≤ 256 * 8504 := Nat.mul_le_mul_right _ hmax
  omega

end

end ReexecNpai
