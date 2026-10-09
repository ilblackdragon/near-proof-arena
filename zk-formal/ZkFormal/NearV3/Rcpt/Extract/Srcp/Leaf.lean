import ZkFormal.NearV3.Rcpt.Extract.Srcp.Bytes

/-! Exact messages of a source-proof leaf segment. -/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

/-- Each leaf row emits its loaded digest byte; only its first row requests the RC digest. -/
theorem leafRowT {s o : Nat} (hu : IsU tr tt s 32)
    (hH : s + 32 ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 1) (ho : o < 32)
    {bb : Nat} (hb : bb ≠ B_SIZE) (sd : Bool) :
    rowTraffic SrcpV3.interactions tr tt (s + o) pub bb sd =
      (if bb = B_BYTES ∧ sd = true then
        [[(K_SRC : Fp) + (16 : Nat) * tr.cell tt s q, ((o : Nat) : Fp),
          tr.cell tt s (reg o)]] else []) ++
      (if bb = B_DIGEST ∧ sd = false ∧ o = 0 then
        [[(K_RC : Fp) + (16 : Nat) * tr.cell tt s j, tr.cell tt s L] ++ regsF tr tt s]
       else []) := by
  rw [segRowT hL hu hH hrt ho hb sd, leaf_byte hL hu hH hrt hlf ho]
  congr 1
  rw [Nat.mod_eq_of_lt ho]
  by_cases hz : o = 0
  · subst o
    have hwf : tr.cell tt s wf = 1 := (segRows hL hu hH hrt).2.1
    obtain ⟨-, -, -, -, -, -, hf, -, -, -, -, hc, -⟩ := local_ hL (r := s) (by omega)
    simp only [Nat.add_zero, (hf hlf).2.2.1, (hc hwf hlf).1, (hc hwf hlf).2]
    simp only [and_true, c16]
  · simp [hz]

/-- The leaf segment emits exactly 32 consecutive bytes of its loaded RC digest. -/
theorem leaf_bytes_traffic {s : Nat} (hu : IsU tr tt s 32)
    (hH : s + 32 ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 1) :
    (List.range 32).flatMap (fun o =>
      rowTraffic SrcpV3.interactions tr tt (s + o) pub B_BYTES true) =
      (emitAt (msgId K_SRC (tr.cell tt s q).toNat) 0 (regsN tr tt s)).map Msg.toFp := by
  rw [flatMap_congr' (fun o ho => leafRowT hL hu hH hrt hlf (List.mem_range.mp ho)
    (by decide : B_BYTES ≠ B_SIZE) true)]
  simp only [B_BYTES, B_DIGEST, Bool.true_eq_false, and_false, false_and,
    and_self, ite_true, ite_false, List.append_nil]
  apply bytesEq (Fp.ofNat_toNat _) (by simp [regsN])
  intro o ho
  simp [regsN, List.getD_eq_getElem?_getD, ho, Fp.ofNat_toNat]

omit hL in
private theorem flatMap_first {α : Type} (v : List α) (n : Nat) :
    (List.range (n + 1)).flatMap (fun o => if o = 0 then v else []) = v := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih]; simp

/-- The leaf requests its RC digest exactly once, with the list's committed length. -/
theorem leaf_digest_traffic {s : Nat} (hu : IsU tr tt s 32)
    (hH : s + 32 ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 1) :
    (List.range 32).flatMap (fun o =>
      rowTraffic SrcpV3.interactions tr tt (s + o) pub B_DIGEST false) =
      [Msg.toFp (digMsg (msgId K_RC (tr.cell tt s j).toNat)
        (tr.cell tt s L).toNat (regsN tr tt s))] := by
  rw [flatMap_congr' (fun o ho => leafRowT hL hu hH hrt hlf (List.mem_range.mp ho)
    (by decide : B_DIGEST ≠ B_SIZE) false)]
  simp only [B_BYTES, B_DIGEST, Bool.false_eq_true, and_false, false_and,
    true_and, ite_false, List.nil_append]
  rw [flatMap_first _ 31]
  simp [toFp_digMsg, ofNat_msgId, Fp.ofNat_toNat, regsN_toFp]

end ZkFormal.NearV3.SrcpProof
