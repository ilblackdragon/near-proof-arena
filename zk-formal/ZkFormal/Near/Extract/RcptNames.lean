import ZkFormal.Near.Extract.RcptStrField
import ZkFormal.Near.Extract.RcptGas1

/-!
# ZkFormal.Near.Extract.RcptNames — lengths, `predecessor ≠ "system"`, named receiver
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt NearSpec

variable {tr : Trace Fp} {pub : List Fp}
variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

/-- Length bounds `2 ≤ L ≤ 64` of a string field. -/
theorem str_len {s r0 L X Lc : Nat} (F : RFld tr s r0 L X) (hH : r0 + L < tr.height T_RCPT)
    (hc : ∀ k, k < L → tr.cell T_RCPT (r0 + k) Lc = ((L : Nat) : Fp))
    (m1 : mul3 (c fe) (c X) (sub (sub (c Lc) (k 2)) (bitsX 0 6)) ∈ Rcpt.constraints)
    (m2 : mul3 (c fe) (c X) (sub (sub (k 64) (c Lc)) (bitsX 6 6)) ∈ Rcpt.constraints) :
    2 ≤ L ∧ L ≤ 64 := by
  have hp := F.fld.pos
  have hq : r0 + (L - 1) < tr.height T_RCPT := by omega
  have c1 := con hL hq m1
  have c2 := con hL hq m2
  obtain ⟨b1, l1⟩ := bitsX_eval hL hq 0 6 (by omega)
  obtain ⟨b2, l2⟩ := bitsX_eval hL hq 6 6 (by omega)
  simp only [eval_mul3, eval_c, eval_sub, eval_k] at c1 c2
  rw [F.fld.fe (L - 1) (by omega), if_pos (by omega), F.fld.st (L - 1) (by omega), hc (L - 1) (by omega), b1] at c1
  rw [F.fld.fe (L - 1) (by omega), if_pos (by omega), F.fld.st (L - 1) (by omega), hc (L - 1) (by omega), b2] at c2
  have hLP : L < P := by have := hP hL; omega
  have e1 : L = 2 + bitsVal (fun j => cv tr T_RCPT (r0 + (L - 1)) (xb j)) 0 6 := by
    apply nat_of_fp hLP (by simp at l1; unfold P; omega); rw [natCast_add]; grind
  have e2 : 64 = L + bitsVal (fun j => cv tr T_RCPT (r0 + (L - 1)) (xb j)) 6 6 := by
    apply nat_of_fp (by unfold P; omega) (by simp at l2; unfold P; omega); rw [natCast_add]; grind
  omega

/-- A column kept along a field. -/
theorem fld_keep {s r0 L X col : Nat} (F : RFld tr s r0 L X) (hH : r0 + L < tr.height T_RCPT)
    (m : mul3 (c X) (Dsl.not (c fe)) (sub (n col) (c col)) ∈ Rcpt.constraints) :
    ∀ k, k < L → tr.cell T_RCPT (r0 + k) col = tr.cell T_RCPT r0 col := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have cc := con hL (r := r0 + k) (by omega) m
    simp only [eval_mul3, eval_c, eval_not, eval_sub, eval_n, nxt (show r0 + k + 1 < tr.height T_RCPT by omega)] at cc
    rw [F.fld.st k (by omega), F.fld.fe k (by omega), if_neg (by omega)] at cc
    rw [show r0 + (k + 1) = r0 + k + 1 by omega, ← ih (by omega)]; grind

omit hL in
theorem ofNat_lt128 {a b : Nat} (ha : a < 128) (hb : b < 128) (h : UInt8.ofNat a = UInt8.ofNat b) : a = b := by
  have := congrArg UInt8.toNat h
  simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt (show a < 256 by omega), Nat.mod_eq_of_lt (show b < 256 by omega)] at this
  exact this

/-- **`predecessor ≠ "system"`.** -/
theorem not_system {s r0 L : Nat} (F : RFld tr s r0 L sP) (hH : r0 + L < tr.height T_RCPT)
    (hLc : ∀ k, k < L → tr.cell T_RCPT (r0 + k) Rcpt.Lp = ((L : Nat) : Fp)) :
    toBytes (colAt tr r0 L b) ≠ AccountId.system := by
  intro he
  have hl : L = 6 := by have := congrArg List.length he; simpa [toBytes, colAt_len, AccountId.system] using this
  subst hl
  have hfs : tr.cell T_RCPT r0 fs = 1 := by simpa using F.fld.fs 0 (by omega)
  have h1 : tr.cell T_RCPT r0 sP = 1 := by simpa using F.fld.st 0 (by omega)
  have sys : ∀ k, k < 6 → tr.cell T_RCPT (r0 + k) b = tr.cell T_RCPT (r0 + k) (reg 0) := by
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
    rw [cast_cv tr _ b, ofNat_lt128 hch (hsl k hk) (Option.some.inj hc)]
  -- the accumulator stays `0`
  have acc0 : ∀ k, k < 6 → tr.cell T_RCPT (r0 + k) acc = 0 := by
    intro k
    induction k with
    | zero =>
      intro _
      have cc := con hL (r := r0) (by omega) (e := mul3 (c sP) (c fs) (sub (c acc) (sq (sub (c b) (c (reg 0))))))
        (mem_ch (by simp [cChars]))
      simp only [sq, eval_mul3, eval_mul, eval_c, eval_sub] at cc
      rw [h1, hfs, show tr.cell T_RCPT r0 b = tr.cell T_RCPT r0 (reg 0) by simpa using sys 0 (by omega)] at cc
      simp only [Nat.add_zero]; grind
    | succ k ih =>
      intro hk
      have cc := con hL (r := r0 + k) (by omega)
        (e := mul3 (c sP) (Dsl.not (c fe)) (sub (n acc) (.add (c acc) (sq (sub (n b) (n (reg 0)))))))
        (mem_ch (by simp [cChars]))
      simp only [sq, eval_mul3, eval_mul, eval_c, eval_not, eval_sub, eval_add, eval_n,
        nxt (show r0 + k + 1 < tr.height T_RCPT by omega)] at cc
      rw [F.fld.st k (by omega), F.fld.fe k (by omega), if_neg (by omega), ih (by omega),
        show r0 + k + 1 = r0 + (k + 1) by omega, sys (k + 1) hk] at cc
      grind
  have cc1 := con hL (r := r0 + 5) (by omega) (e := mul3 (c sP) (c fe) (sub (c p1) (.add (c acc) (sq (sub (c Rcpt.Lp) (k 6))))))
    (mem_ch (by simp [cChars]))
  have cc2 := con hL (r := r0 + 5) (by omega) (e := mul3 (c sP) (c fe) (sub (.mul (c p1) (c isys)) (k 1)))
    (mem_ch (by simp [cChars]))
  simp only [sq, eval_mul3, eval_mul, eval_c, eval_sub, eval_add, eval_k] at cc1 cc2
  rw [F.fld.st 5 (by omega), F.fld.fe 5 (by omega), if_pos rfl, acc0 5 (by omega), hLc 5 (by omega)] at cc1
  rw [F.fld.st 5 (by omega), F.fld.fe 5 (by omega), if_pos rfl] at cc2
  have : tr.cell T_RCPT (r0 + 5) p1 = 0 := by grind
  rw [this] at cc2; grind

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt NearSpec

variable {tr : Trace Fp} {pub : List Fp}

/-- Number of hex characters among the first `n` of `f`. -/
def hcount (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => hcount f n + (if f n then 1 else 0)

theorem hcount_all (f : Nat → Bool) (a : Nat) : ∀ n, (∀ m, a ≤ m → m < a + n → f m = true) →
    hcount f (a + n) = hcount f a + n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [show a + (n + 1) = (a + n) + 1 by omega, hcount, ih (fun m h1 h2 => h m h1 (by omega)),
      h (a + n) (by omega) (by omega)]
    simp; omega

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

/-- **The receiver is a named account.** -/
theorem named_ok {s r0 L : Nat} (F : RFld tr s r0 L sV) (hH : r0 + L < tr.height T_RCPT)
    (hLc : ∀ k, k < L → tr.cell T_RCPT (r0 + k) Rcpt.Lv = ((L : Nat) : Fp)) (hlen : 2 ≤ L ∧ L ≤ 64) :
    AccountId.isNamed (toBytes (colAt tr r0 L b)) = true := by
  have RC := fun k (hk : k < L) => row_char hL (q := r0 + k) (by omega) (X := sV) (by simp) (F.fld.st k hk)
  let hx : Nat → Bool := fun m => AccountId.isHex (UInt8.ofNat (cv tr T_RCPT (r0 + m) b))
  have hfs : tr.cell T_RCPT r0 fs = 1 := by simpa using F.fld.fs 0 (by omega)
  have h1 : tr.cell T_RCPT r0 sV = 1 := by simpa using F.fld.st 0 (by omega)
  have hexv : ∀ k, k < L → hexE.eval tr T_RCPT (r0 + k) pub = ((if hx k then 1 else 0 : Nat) : Fp) := by
    intro k hk; rw [(RC k hk).2.2.2.2]; simp only [hx]; split <;> rfl
  -- the hex counter
  have accv : ∀ k, k < L → tr.cell T_RCPT (r0 + k) acc = ((hcount hx (k + 1) : Nat) : Fp) := by
    intro k
    induction k with
    | zero =>
      intro _
      have cc := con hL (r := r0) (by omega) (e := mul3 (c sV) (c fs) (sub (c acc) hexE)) (mem_ch (by simp [cChars]))
      simp only [eval_mul3, eval_c, eval_sub] at cc
      rw [h1, hfs, show hexE.eval tr T_RCPT r0 pub = _ from hexv 0 (by omega)] at cc
      simp only [hcount, Nat.zero_add, Nat.add_zero]; grind
    | succ k ih =>
      intro hk
      have cc := con hL (r := r0 + k) (by omega) (e := mul3 (c sV) (Dsl.not (c fe)) (sub (n acc) (.add (c acc) hexN)))
        (mem_ch (by simp [cChars]))
      simp only [eval_mul3, eval_c, eval_not, eval_sub, eval_add, eval_n,
        nxt (show r0 + k + 1 < tr.height T_RCPT by omega)] at cc
      rw [F.fld.st k (by omega), F.fld.fe k (by omega), if_neg (by omega), ih (by omega),
        hexN_eval hL (show r0 + k + 1 < tr.height T_RCPT by omega), show r0 + k + 1 = r0 + (k + 1) by omega,
        hexv (k + 1) hk] at cc
      rw [show k + 1 + 1 = (k + 1) + 1 from rfl, hcount, natCast_add]; grind
  have hl : (toBytes (colAt tr r0 L b)).length = L := by simp [toBytes, colAt_len]
  have gk : ∀ k (hk : k < L), (toBytes (colAt tr r0 L b))[k]'(by omega) = UInt8.ofNat (cv tr T_RCPT (r0 + k) b) := by
    intro k hk; simp [toBytes, colAt]
  have allHex : ∀ a, AccountId.allHex ((toBytes (colAt tr r0 L b)).drop a) = true → ∀ m, a ≤ m → m < L → hx m = true := by
    intro a ha m h1 h2
    simp only [AccountId.allHex, List.all_eq_true] at ha
    have := ha ((toBytes (colAt tr r0 L b))[m]'(by omega)) (List.mem_iff_getElem.mpr ⟨m - a, by simp; omega, by
      simp [List.getElem_drop, show a + (m - a) = m by omega]⟩)
    rwa [gk m h2] at this
  -- `p1`, `p2`, `p3` and their inverses on the last row
  have hq : r0 + (L - 1) < tr.height T_RCPT := by omega
  have fe1 : tr.cell T_RCPT (r0 + (L - 1)) fe = 1 := by rw [F.fld.fe (L - 1) (by omega), if_pos (by omega)]
  have st1 : tr.cell T_RCPT (r0 + (L - 1)) sV = 1 := F.fld.st (L - 1) (by omega)
  have keep := fun col m => fld_keep hL F hH (col := col) m (L - 1) (by omega)
  have kv0 := keep vc0 (mem_ch (by simp [cChars]))
  have kv1 := keep vc1 (mem_ch (by simp [cChars]))
  have kh := keep h01 (mem_ch (by simp [cChars]))
  have f0 : tr.cell T_RCPT r0 vc0 = tr.cell T_RCPT r0 b := by
    have cc := con hL (r := r0) (by omega) (e := mul3 (c sV) (c fs) (sub (c vc0) (c b))) (mem_ch (by simp [cChars]))
    simp only [eval_mul3, eval_c, eval_sub] at cc; rw [h1, hfs] at cc; grind
  have f1 : tr.cell T_RCPT r0 vc1 = tr.cell T_RCPT (r0 + 1) b := by
    have cc := con hL (r := r0) (by omega) (e := mul3 (c sV) (c fs) (sub (c vc1) (n b))) (mem_ch (by simp [cChars]))
    simp only [eval_mul3, eval_c, eval_sub, eval_n, nxt (show r0 + 1 < tr.height T_RCPT by omega)] at cc
    rw [h1, hfs] at cc; grind
  have fh : tr.cell T_RCPT r0 h01 = ((if hx 0 then 1 else 0 : Nat) : Fp) + ((if hx 1 then 1 else 0 : Nat) : Fp) := by
    have cc := con hL (r := r0) (by omega) (e := mul3 (c sV) (c fs) (sub (c h01) (.add hexE hexN))) (mem_ch (by simp [cChars]))
    simp only [eval_mul3, eval_c, eval_sub, eval_add] at cc
    rw [h1, hfs, hexN_eval hL (show r0 + 1 < tr.height T_RCPT by omega), show hexE.eval tr T_RCPT r0 pub = _ from
      hexv 0 (by omega), show r0 + 1 = r0 + 1 from rfl, hexv 1 (by omega)] at cc
    grind
  have accL := accv (L - 1) (by omega)
  rw [show L - 1 + 1 = L by omega] at accL
  -- the three non-named shapes give a vanishing `p`
  have kill : ∀ (pc ic : Nat) (E : Expr),
      mul3 (c sV) (c fe) (sub (c pc) E) ∈ Rcpt.constraints →
      mul3 (c sV) (c fe) (sub (.mul (c pc) (c ic)) (k 1)) ∈ Rcpt.constraints →
      E.eval tr T_RCPT (r0 + (L - 1)) pub = 0 → False := by
    intro pc ic E m1 m2 hE
    have c1 := con hL hq m1; have c2 := con hL hq m2
    simp only [eval_mul3, eval_mul, eval_c, eval_sub, eval_k] at c1 c2
    rw [st1, fe1, hE] at c1; rw [st1, fe1] at c2
    have : tr.cell T_RCPT (r0 + (L - 1)) pc = 0 := by grind
    rw [this] at c2; grind
  simp only [AccountId.isNamed, Bool.not_eq_true', Bool.or_eq_false_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- `0x` + 40 hex
    cases e : AccountId.isEthImplicit (toBytes (colAt tr r0 L b))
    · rfl
    exfalso
    simp only [AccountId.isEthImplicit, Bool.and_eq_true, beq_iff_eq] at e
    obtain ⟨⟨e1, e2⟩, e3⟩ := e
    rw [hl] at e1; subst e1
    have v0 : cv tr T_RCPT (r0 + 0) b = 48 := by
      have := congrArg (fun l => l[0]?) e2; simp [toBytes, colAt] at this
      exact ofNat_lt128 (RC 0 (by omega)).1 (by decide) this
    have v1 : cv tr T_RCPT (r0 + 1) b = 120 := by
      have := congrArg (fun l => l[1]?) e2; simp [toBytes, colAt] at this
      exact ofNat_lt128 (RC 1 (by omega)).1 (by decide) this
    have hc := hcount_all hx 2 40 (fun m h1 h2 => allHex 2 e3 m h1 (by omega))
    refine kill p2 i2 (sum [sq (sub (c Rcpt.Lv) (k 42)), sq (sub (c vc0) (k 48)), sq (sub (c vc1) (k 120)), sq (sub (sub (c acc) (c h01)) (k 40))]) (mem_ch (by simp [cChars])) (mem_ch (by simp [cChars])) ?_
    simp only [sq, eval_sum_cons, eval_sum_nil, eval_mul, eval_sub, eval_c, eval_k]
    rw [hLc 41 (by omega), kv0, kv1, kh, f0, f1, fh, accL, cast_cv tr _ b, cast_cv tr _ b, Nat.add_zero] at *
    rw [v0, v1, show (42 : Nat) = 2 + 40 from rfl, hc]
    simp only [hcount, Nat.zero_add, natCast_add]; grind
  · -- 64 hex
    cases e : AccountId.isNearImplicit (toBytes (colAt tr r0 L b))
    · rfl
    exfalso
    simp only [AccountId.isNearImplicit, Bool.and_eq_true, beq_iff_eq] at e
    obtain ⟨e1, e3⟩ := e
    rw [hl] at e1; subst e1
    have hc := hcount_all hx 0 64 (fun m h1 h2 => allHex 0 (by simpa using e3) m h1 (by omega))
    refine kill p1 i1 (.add (sq (sub (c Rcpt.Lv) (k 64))) (sq (sub (c acc) (c Rcpt.Lv)))) (mem_ch (by simp [cChars])) (mem_ch (by simp [cChars])) ?_
    simp only [sq, eval_mul, eval_add, eval_sub, eval_c, eval_k]
    rw [hLc 63 (by omega), accL, show (64 : Nat) = 0 + 64 from rfl, hc]
    simp only [hcount]; grind
  · -- `0s` + 40 hex
    cases e : AccountId.isNearDeterministic (toBytes (colAt tr r0 L b))
    · rfl
    exfalso
    simp only [AccountId.isNearDeterministic, Bool.and_eq_true, beq_iff_eq] at e
    obtain ⟨⟨e1, e2⟩, e3⟩ := e
    rw [hl] at e1; subst e1
    have v0 : cv tr T_RCPT (r0 + 0) b = 48 := by
      have := congrArg (fun l => l[0]?) e2; simp [toBytes, colAt] at this
      exact ofNat_lt128 (RC 0 (by omega)).1 (by decide) this
    have v1 : cv tr T_RCPT (r0 + 1) b = 115 := by
      have := congrArg (fun l => l[1]?) e2; simp [toBytes, colAt] at this
      exact ofNat_lt128 (RC 1 (by omega)).1 (by decide) this
    have hc := hcount_all hx 2 40 (fun m h1 h2 => allHex 2 e3 m h1 (by omega))
    refine kill p3 i3 (sum [sq (sub (c Rcpt.Lv) (k 42)), sq (sub (c vc0) (k 48)), sq (sub (c vc1) (k 115)), sq (sub (sub (c acc) (c h01)) (k 40))]) (mem_ch (by simp [cChars])) (mem_ch (by simp [cChars])) ?_
    simp only [sq, eval_sum_cons, eval_sum_nil, eval_mul, eval_sub, eval_c, eval_k]
    rw [hLc 41 (by omega), kv0, kv1, kh, f0, f1, fh, accL, cast_cv tr _ b, cast_cv tr _ b, Nat.add_zero] at *
    rw [v0, v1, show (42 : Nat) = 2 + 40 from rfl, hc]
    simp only [hcount, Nat.zero_add, natCast_add]; grind

end ZkFormal.Near.RcptProof
