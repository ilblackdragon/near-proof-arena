import ZkFormal.NearV3.Assembly.RcptCandidateRegs
import ZkFormal.NearV3.Assembly.RcptCandidateNamed
-- Source SystemFlag.lean SHA256: 94b3260bacd3d148bcd32b9404f16e8c53525de8b4d2e536fb3aa60db135c3af.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.Named

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 NearSpec
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- The native system predecessor forces the active V3 system flag. -/
theorem system_flag_of_string {s r0 L : Nat} (F : RFld tr tt s r0 L sP) (hH : r0 + L < tr.height tt)
    (hLc : ∀ k, k < L → tr.cell tt (r0 + k) RcptV3.Lp = ((L : Nat) : Fp))
    (he : toBytes (colAt tr tt r0 L b) = AccountId.system) :
    tr.cell tt (r0+(L-1)) RcptV3.sys = 1 := by
  have hl : L = 6 := by have := congrArg List.length he; simpa [toBytes, colAt_len, AccountId.system] using this
  subst hl
  have hfs : tr.cell tt r0 fs = 1 := by simpa using F.fld.fs 0 (by omega)
  have h1 : tr.cell tt r0 sP = 1 := by simpa using F.fld.st 0 (by omega)
  have sys : ∀ k, k < 6 → tr.cell tt (r0 + k) b = tr.cell tt (r0 + k) (reg 0) := by
    intro k hk
    rw [fld_reg hL (by omega) F.fld (by simp [states]) (by decide) k hk 0 (by omega), Nat.zero_add,
      reg_load hL (by omega) (X := sP) (l := ks [115, 121, 115, 116, 101, 109]) (by simp [loads]) h1 hfs k
        (by simp [ks]; omega)]
    rw [ks_get [115, 121, 115, 116, 101, 109] k (by simp; omega) r0]
    have hc := congrArg (fun l : List UInt8 => l[k]?) he
    simp only [toBytes, colAt, List.map_map, Function.comp_def, List.getElem?_map, List.getElem?_range hk,
      Option.map_some] at hc
    have hsy : ∀ k, k < 6 → AccountId.system[k]? = some (UInt8.ofNat ([115, 121, 115, 116, 101, 109].getD k 0)) := by
      decide
    have hsl : ∀ k, k < 6 → [115, 121, 115, 116, 101, 109].getD k 0 < 128 := by decide
    rw [hsy k hk] at hc
    have hch := (row_char hL (q := r0 + k) (by omega) (X := sP) (by simp) (F.fld.st k hk)).1
    rw [cell_eq_cast tr tt _ b, ofNat_lt128 hch (hsl k hk) (Option.some.inj hc)]
  -- the accumulator stays `0`
  have acc0 : ∀ k, k < 6 → tr.cell tt (r0 + k) acc = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      have cc := con hL (r := r0) (by omega) (e := mul3 (c sP) (c fs) (sub (c acc) (sq (sub (c b) (c (reg 0))))))
        (mem_ch (by simp [cChars]))
      simp only [sq, eval_mul3, eval_mul, eval_c, eval_sub] at cc
      rw [h1, hfs, show tr.cell tt r0 b = tr.cell tt r0 (reg 0) by simpa using sys 0 (by omega)] at cc
      simp only [Nat.add_zero]; grind
    | succ k ih =>
      intro hk
      have cc := con hL (r := r0 + k) (by omega)
        (e := mul3 (c sP) (Dsl.not (c fe)) (sub (n acc) (.add (c acc) (sq (sub (n b) (n (reg 0)))))))
        (mem_ch (by simp [cChars]))
      simp only [sq, eval_mul3, eval_mul, eval_c, eval_not, eval_sub, eval_add, eval_n,
        nxt (show r0 + k + 1 < tr.height tt by omega)] at cc
      rw [F.fld.st k (by omega), F.fld.fe k (by omega), if_neg (by omega), ih (by omega),
        show r0 + k + 1 = r0 + (k + 1) by omega, sys (k + 1) hk] at cc
      grind
  have cc1 := con hL (r := r0 + 5) (by omega) (e := mul3 (c sP) (c fe) (sub (c p1) (.add (c acc) (sq (sub (c RcptV3.Lp) (k 6))))))
    (mem_ch (by simp [cChars]))
  have cc2 := con hL (r := r0 + 5) (by omega) (e := mul3 (c sP) (c fe) (sub (.mul (c p1) (c isys)) (Dsl.not (c RcptV3.sys))))
    (mem_ch (by simp [cChars]))
  simp only [sq, eval_mul3, eval_mul, eval_c, eval_sub, eval_add, eval_k, eval_not] at cc1 cc2
  rw [F.fld.st 5 (by omega), F.fld.fe 5 (by omega), if_pos rfl, acc0 5 (by omega), hLc 5 (by omega)] at cc1
  rw [F.fld.st 5 (by omega), F.fld.fe 5 (by omega), if_pos rfl] at cc2
  have : tr.cell tt (r0 + 5) p1 = 0 := by grind
  rw [this] at cc2; grind


end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
