import ZkFormal.NearV3.Rcpt.Extract.Srcp.Leaf

/-!
# Source-proof path traffic

A path segment emits 64 bytes and requests its predecessor digest once, at the
start of the accumulator window selected by the direction bit.
-/

namespace ZkFormal.NearV3.SrcpProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.SrcpV3

/-- The accumulator is first for a right sibling, second for a left sibling. -/
def accStart (d : Bool) : Nat := if d then 0 else 32

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal SrcpV3.table tr tt pub)
include hL

theorem path_aw {s o : Nat} (hu : IsU tr tt s 64)
    (hH : s + 64 ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 0) (d : Bool)
    (hd : tr.cell tt s dir = (if d then 1 else 0)) (ho : o < 64) :
    tr.cell tt (s + o) aw =
      (if o < 32 then (if d then 1 else 0) else (if d then 0 else 1)) := by
  have hrows := (segRows hL hu hH hrt).2.2.2.2.2.2 o ho
  obtain ⟨-, -, -, -, -, -, -, haw, -⟩ := local_ hL (r := s + o) (by omega)
  rw [haw hrows.1, hrows.2.2.2.2 lf (by simp [segConst]), hlf,
    hrows.2.2.2.2 dir (by simp [segConst]), hd,
    ((segShape hL hu hH hrt).2 o ho).2.1]
  cases d <;> split <;> simp_all <;> grind

theorem path_digest_gate {s o : Nat} (hu : IsU tr tt s 64)
    (hH : s + 64 ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 0) (d : Bool)
    (hd : tr.cell tt s dir = (if d then 1 else 0)) (ho : o < 64) :
    (o % 32 = 0 ∧ tr.cell tt (s + o) aw = 1) ↔ o = accStart d := by
  rw [path_aw hL hu hH hrt hlf d hd ho]
  cases d <;> by_cases h : o < 32 <;> simp [accStart, h] <;> omega

/-- The path digest request occurs exactly at the selected window's first row. -/
theorem pathRowT {s o : Nat} (hu : IsU tr tt s 64)
    (hH : s + 64 ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 0) (d : Bool)
    (hd : tr.cell tt s dir = (if d then 1 else 0)) (ho : o < 64)
    {bb : Nat} (hb : bb ≠ B_SIZE) (sd : Bool) :
    rowTraffic SrcpV3.interactions tr tt (s + o) pub bb sd =
      (if bb = B_BYTES ∧ sd = true then
        [[(K_SRC : Fp) + (16 : Nat) * tr.cell tt s q, ((o : Nat) : Fp),
          tr.cell tt (s + o) b]] else []) ++
      (if bb = B_DIGEST ∧ sd = false ∧ o = accStart d then
        [[(K_SRC : Fp) + (16 : Nat) * (tr.cell tt s q - 1), tr.cell tt s pl] ++
          regsF tr tt (s + accStart d)] else []) := by
  rw [segRowT hL hu hH hrt ho hb sd]
  simp only [path_digest_gate hL hu hH hrt hlf d hd ho]
  congr 1
  by_cases he : o = accStart d
  · subst o
    have hm : accStart d % 32 = 0 := by cases d <;> decide
    have haw := (path_digest_gate hL hu hH hrt hlf d hd ho).mpr rfl
    have hwf : tr.cell tt (s + accStart d) wf = 1 := by
      rw [((segShape hL hu hH hrt).2 (accStart d) ho).2.2.1, hm]; rfl
    have hrows := (segRows hL hu hH hrt).2.2.2.2.2.2 (accStart d) ho
    have hf : tr.cell tt (s + accStart d) lf = 0 := by
      rw [hrows.2.2.2.2 lf (by simp [segConst]), hlf]
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hc, -⟩ :=
      local_ hL (r := s + accStart d) (by omega)
    rw [(hc hwf haw.2 hf).1, (hc hwf haw.2 hf).2,
      hrows.2.2.2.2 q (by simp [segConst]), hrows.2.2.2.2 pl (by simp [segConst])]
    rfl
  · simp [he]

/-- All emitted path bytes in their SHA message order. -/
def pathBytes (tr : Trace Fp) (tt s : Nat) : List Nat :=
  (List.range 64).map fun o => (tr.cell tt (s + o) b).toNat

theorem path_bytes_traffic {s : Nat} (hu : IsU tr tt s 64)
    (hH : s + 64 ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 0) (d : Bool)
    (hd : tr.cell tt s dir = (if d then 1 else 0)) :
    (List.range 64).flatMap (fun o =>
      rowTraffic SrcpV3.interactions tr tt (s + o) pub B_BYTES true) =
      (emitAt (msgId K_SRC (tr.cell tt s q).toNat) 0 (pathBytes tr tt s)).map Msg.toFp := by
  rw [flatMap_congr' (fun o ho => pathRowT hL hu hH hrt hlf d hd (List.mem_range.mp ho)
    (by decide : B_BYTES ≠ B_SIZE) true)]
  simp only [B_BYTES, B_DIGEST, Bool.true_eq_false, and_false, false_and,
    and_self, ite_true, ite_false, List.append_nil]
  apply bytesEq (Fp.ofNat_toNat _) (by simp [pathBytes])
  intro o ho
  simp [pathBytes, List.getD_eq_getElem?_getD, ho, Fp.ofNat_toNat]

omit hL in
private theorem flatMap_at {α : Type} (v : List α) (n k : Nat) (hk : k < n) :
    (List.range n).flatMap (fun o => if o = k then v else []) = v := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases he : k = n
    · subst k
      have hz : (List.range n).flatMap (fun o => if o = n then v else []) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro o ho
        simp [show o ≠ n by have := List.mem_range.mp ho; omega]
      rw [hz]; simp
    · rw [ih (by omega)]; simp [Ne.symm he]

/-- The predecessor digest is requested exactly once. Positivity of the message
counter is supplied later by the global root/segment counter chain. -/
theorem path_digest_traffic {s : Nat} (hu : IsU tr tt s 64)
    (hH : s + 64 ≤ tr.height tt) (hrt : tr.cell tt s rt = 0)
    (hlf : tr.cell tt s lf = 0) (d : Bool)
    (hd : tr.cell tt s dir = (if d then 1 else 0))
    (hq : 0 < (tr.cell tt s q).toNat) :
    (List.range 64).flatMap (fun o =>
      rowTraffic SrcpV3.interactions tr tt (s + o) pub B_DIGEST false) =
      [Msg.toFp (digMsg (msgId K_SRC ((tr.cell tt s q).toNat - 1))
        (tr.cell tt s pl).toNat (regsN tr tt (s + accStart d)))] := by
  rw [flatMap_congr' (fun o ho => pathRowT hL hu hH hrt hlf d hd (List.mem_range.mp ho)
    (by decide : B_DIGEST ≠ B_SIZE) false)]
  simp only [B_BYTES, B_DIGEST, Bool.false_eq_true, and_false, false_and,
    true_and, ite_false, List.nil_append]
  rw [flatMap_at _ 64 (accStart d) (by cases d <;> decide)]
  have hsub : Fp.ofNat ((tr.cell tt s q).toNat - 1) = tr.cell tt s q - 1 := by
    have he : Fp.ofNat ((tr.cell tt s q).toNat - 1) + 1 = tr.cell tt s q := by
      rw [show (1 : Fp) = Fp.ofNat 1 from rfl, ofNat_add', Nat.sub_add_cancel hq,
        Fp.ofNat_toNat]
    grind
  simp [toFp_digMsg, ofNat_msgId, Fp.ofNat_toNat, regsN_toFp, hsub]

end ZkFormal.NearV3.SrcpProof
