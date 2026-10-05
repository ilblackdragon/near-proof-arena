import ZkFormal.Near.Extract.RcptTraffic

/-!
# ZkFormal.Near.Extract.RcptWfEasy — the structural facts of `RcptWf`

Lengths, byte ranges of the column-read values, canonicity, `tprev ≤ r`, the
fixed claim prefix.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

theorem lens_of (tr : Trace Fp) (y : RS) (hkt : y.kt ≤ 1) :
    let x := rcptOf tr y
    x.rid.length = 32 ∧ x.pk.length = 32 + 32 * x.kt ∧ x.kt ≤ 1 ∧ x.gp.length = 16 ∧
    x.dep.length = 16 ∧ x.bef.length = 16 ∧ x.lk.length = 16 ∧ x.st.length = 16 ∧
    x.aft.length = 16 ∧ x.burnt.length = 16 ∧ x.ramt.length = 16 ∧ x.rfid.length = 32 ∧
    x.peoh.length = 32 := by
  obtain ⟨s, h, Lp, Lv, Ls, kt⟩ := y
  simp only at hkt
  cases h <;> simp [rcptOf, colAt_len, hkt]

theorem colAt_lt (tr : Trace Fp) (r0 len x : Nat) : ∀ y ∈ colAt tr r0 len x, y < P := by
  intro y hy; simp only [colAt, List.mem_map] at hy; obtain ⟨k, -, rfl⟩ := hy; exact cv_lt _ _ _ _

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem aft8_of {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt) :
    Bytes8 (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).aft := by
  have hm : (sDEP, 107 + Vt Lp Lv Ls kt, 16) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have hle := plan_le h Lp Lv Ls kt _ hm
  have hfin := lay.fin
  intro y hy
  simp only [rcptOf, List.mem_map, List.mem_range] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  have := bitsVal_lt (fun j => cv tr T_RCPT (s + (107 + Vt Lp Lv Ls kt) + k) (xb j)) 0 8 (fun j hj =>
    cv_bool (isBool hL (by simp at hle; omega)
      (by unfold boolCols; simp only [List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨j, by omega, by simp⟩)))
  simpa using this

theorem canon_of {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt) :
    ∀ y ∈ (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).raw, y < P := by
  have ha := aft8_of hL lay
  have hkt := lay.kt1
  intro y hy
  simp only [RcptV.raw, List.mem_append, List.mem_singleton, or_assoc] at hy
  rcases hy with hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy | hy
  all_goals first
    | exact colAt_lt _ _ _ _ _ hy
    | (have := ha y hy; unfold P; omega)
    | (subst hy; exact Nat.lt_of_le_of_lt hkt (by decide))
    | skip
  simp only [rcptOf] at hy
  cases h
  · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_replicate] at hy; rw [hy.2]; unfold P; omega
  · exact colAt_lt _ _ _ _ _ hy

theorem prefix_ok : ∀ j, j < 77 → pubNat pub j = (ZkFormal.Near.claimPrefix.getD j 0).toNat := by
  intro j hj
  have h0 : 0 < tr.height T_RCPT := by have := height_ge hL; omega
  have hl : ZkFormal.Near.claimPrefix.length = 77 := by rw [claimPrefix_length]; rfl
  have hz : (ZkFormal.Near.claimPrefix[j]'(by omega), j) ∈ ZkFormal.Near.claimPrefix.zip (List.range 77) := by
    have : (ZkFormal.Near.claimPrefix.zip (List.range 77))[j]'(by simp [hl]; omega) =
        (ZkFormal.Near.claimPrefix[j]'(by omega), j) := by simp
    rw [← this]; exact List.getElem_mem _
  have c := con hL h0 (e := sub (.pub j) (k (ZkFormal.Near.claimPrefix[j]'(by omega)).toNat)) (mem_cl (by
    unfold cClaim; simp only [List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨_, hz, rfl⟩)))
  simp only [eval_sub, eval_pub, eval_k] at c
  have e : pub.getD j 0 = (((ZkFormal.Near.claimPrefix[j]'(by omega)).toNat : Nat) : Fp) := by grind
  have hb := (ZkFormal.Near.claimPrefix[j]'(by omega)).toNat_lt
  simp only [pubNat, e, toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < ZkFormal.Near.claimPrefix.length by omega),
    Option.getD_some]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb (by decide))

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

theorem xb_bool {q : Nat} (hq : q < tr.height T_RCPT) (j : Nat) (hj : j < 66) :
    tr.cell T_RCPT q (xb j) = 0 ∨ tr.cell T_RCPT q (xb j) = 1 :=
  isBool hL hq (by
    unfold boolCols; simp only [List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨j, hj, rfl⟩)

theorem bitsX_eval {q : Nat} (hq : q < tr.height T_RCPT) (off len : Nat) (hl : off + len ≤ 66) :
    (bitsX off len).eval tr T_RCPT q pub = ((bitsVal (fun j => cv tr T_RCPT q (xb j)) off len : Nat) : Fp) ∧
    bitsVal (fun j => cv tr T_RCPT q (xb j)) off len < 2 ^ len :=
  ⟨eval_bits tr T_RCPT q pub xb off len (fun j hj => xb_bool hL hq _ (by omega)),
   bitsVal_lt _ off len (fun j hj => cv_bool (xb_bool hL hq _ (by omega)))⟩

theorem tprev_le_of {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr s h Lp Lv Ls kt) {rN : Nat}
    (hrN : tr.cell T_RCPT s Rcpt.r = (rN : Fp)) (hrP : rN < P) :
    (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).tprev < P - 512 → (rcptOf tr ⟨s, h, Lp, Lv, Ls, kt⟩).tprev ≤ rN := by
  intro ht
  have hm : (sDEP, 107 + Vt Lp Lv Ls kt, 16) ∈ plan h Lp Lv Ls kt := by simp [plan]
  have hle := plan_le h Lp Lv Ls kt _ hm
  have hfin := lay.fin
  have F : RFld tr s (s + (107 + Vt Lp Lv Ls kt)) 16 sDEP := lay.flds _ hm
  have hq : s + (107 + Vt Lp Lv Ls kt) < tr.height T_RCPT := by simp at hle; omega
  have c := con hL hq (e := mul3 dp (c fs) (sub (sub (c Rcpt.r) (c tprev)) (bitsX 57 9))) (mem_dp (by simp [cDep]))
  have h1 : tr.cell T_RCPT (s + (107 + Vt Lp Lv Ls kt)) sDEP = 1 := by simpa using F.fld.st 0 (by omega)
  have hfs : tr.cell T_RCPT (s + (107 + Vt Lp Lv Ls kt)) fs = 1 := by simpa using F.fld.fs 0 (by omega)
  have hr0 := F.consts 0 (by omega) _ rC
  have ht0 := F.consts 0 (by omega) tprev (by simp [rconsts])
  simp only [Nat.add_zero] at hr0 ht0
  obtain ⟨be, bl⟩ := bitsX_eval hL hq 57 9 (by omega)
  simp only [dp, eval_mul3, eval_c, eval_sub] at c
  rw [h1, hfs, be, hr0, ht0, hrN, cell_eq_cast tr T_RCPT s tprev] at c
  have e : ((rN : Nat) : Fp) = ((cv tr T_RCPT s tprev + bitsVal (fun j => cv tr T_RCPT (s + (107 + Vt Lp Lv Ls kt)) (xb j)) 57 9 : Nat) : Fp) := by
    rw [natCast_add]; grind
  have := ofNat_inj hrP (by simp [rcptOf] at ht; omega) e
  simp only [rcptOf]; omega

end ZkFormal.Near.RcptProof
