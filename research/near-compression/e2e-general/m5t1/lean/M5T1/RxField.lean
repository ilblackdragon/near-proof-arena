import M5T1.Gadget
import M5T1.RxSem

/-!
# M5T1.RxField — an `RX` row's constraints give `RxRel` of its decoded values

`rx_rel_of_row`: on a row of any trace where every constraint of `Rx.table` vanishes (over
BabyBear), `act = 1`, every byte column is `< 256` and `r10 + 246 < 256` (the `RNG` lookups;
`RxBus` derives them from `Holds`), the decoded naturals (`decode`: each byte group's
little-endian value) satisfy `RxRel`. The bit columns are bits by the table's own booleanity
constraints. Standard axioms only.
-/

namespace M5T1.RxField

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound M5T1

section
variable (tr : Trace Fp) (t r : Nat) (pub : List Fp)

/-- byte `k` of group `g` of the row -/
def cb (g : String) (k : Nat) : Nat := cv tr t r pub (Rx.L.off g + k)

/-- the little-endian value of group `g` (`w` bytes) -/
def gv (g : String) (w : Nat) : Nat := val (cb tr t r pub g) w

/-- The decoded row. -/
def decode : RxVals where
  lm := cb tr t r pub "lm" 0
  la := cb tr t r pub "la" 0
  gp := gv tr t r pub "gp" 16
  egp := gv tr t r pub "egp" 16
  gas := gv tr t r pub "gas" 8
  dep := gv tr t r pub "dep" 16
  amt := gv tr t r pub "amt" 16
  lck := gv tr t r pub "lck" 16
  vb := gv tr t r pub "vb" 8
  vu := gv tr t r pub "vu" 8
  vc := gv tr t r pub "vc" 8
  vbal := gv tr t r pub "vbal" 16
  vus := gv tr t r pub "vus" 8
  vsub := gv tr t r pub "vsub" 16
  fcx := gv tr t r pub "fcx" 8
  gb := gv tr t r pub "gb" 8
  gu := gv tr t r pub "gu" 8
  cu := gv tr t r pub "cu" 8
  req := gv tr t r pub "req" 16
  burn := gv tr t r pub "burn" 16
  pexec := gv tr t r pub "pexec" 8
  tot := gv tr t r pub "tot" 8
  gross := gv tr t r pub "gross" 8
  unu := gv tr t r pub "unu" 16
  gpb := gv tr t r pub "gpb" 16
  sur := gv tr t r pub "sur" 16
  bc := gv tr t r pub "bc" 16
  rf := gv tr t r pub "rf" 16
  tb := gv tr t r pub "tb" 16
  q10 := gv tr t r pub "q10" 8
  rew := gv tr t r pub "rew" 16
  amt2 := gv tr t r pub "amt2" 16
  txb := gv tr t r pub "txb" 16
  glim := gv tr t r pub "glim" 8
  gin := gv tr t r pub "gin" 8
  cin := gv tr t r pub "cin" 8
  tbin := gv tr t r pub "tbin" 16
  sbin := gv tr t r pub "sbin" 16
  wgin := gv tr t r pub "wgin" 16
  gout := gv tr t r pub "gout" 8
  cout := gv tr t r pub "cout" 8
  tbout := gv tr t r pub "tbout" 16
  sbout := gv tr t r pub "sbout" 16
  wgout := gv tr t r pub "wgout" 16

/-- The premises: the row's constraints, `act = 1`, the `RNG` facts. -/
structure Hyps : Prop where
  cons : ∀ e ∈ Rx.constraints, ev tr t r pub e = 0
  act : cb tr t r pub "act" 0 = 1
  bytes : ∀ g w, (g, w) ∈ Rx.byteGroups → ∀ k < w, cb tr t r pub g k < 256
  r10 : cb tr t r pub "r10" 0 + 246 < 256
end

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

@[simp] theorem ize_c (g : String) (k : Nat) : ize tr t r pub (Rx.c g k) = (cb tr t r pub g k : Int) := rfl
@[simp] theorem ize_bv (g : String) (k : Nat) : ize tr t r pub (Rx.bv g k) = (cb tr t r pub g k : Int) := rfl
@[simp] theorem ize_kb (v k : Nat) : ize tr t r pub (Rx.kb v k) = ((v / 256 ^ k % 256 : Nat) : Int) := rfl
@[simp] theorem ize_add2 (a b : Nat → Expr) (k : Nat) :
    ize tr t r pub (Rx.add2 a b k) = ize tr t r pub (a k) + ize tr t r pub (b k) := rfl
@[simp] theorem ize_add3 (a b d : Nat → Expr) (k : Nat) :
    ize tr t r pub (Rx.add3 a b d k) = ize tr t r pub (a k) + ize tr t r pub (b k) + ize tr t r pub (d k) := rfl
@[simp] theorem ize_cy2 (g : String) (k : Nat) :
    ize tr t r pub (Rx.cy2 g k) = (cb tr t r pub g (2 * k) : Int) + 256 * (cb tr t r pub g (2 * k + 1) : Int) := rfl

/-! ## From the table's constraints -/

theorem arith_zero (H : Hyps tr t r pub) : ∀ e ∈ Rx.arith, ev tr t r pub e = 0 := by
  intro e he
  have hm : Rx.c "act" * e ∈ Rx.constraints := by
    unfold Rx.constraints
    simp only [List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨e, he, rfl⟩)
  have h := H.cons _ hm
  have hA : ev tr t r pub (Rx.c "act") = 1 := H.act
  rwa [show Rx.c "act" * e = Expr.mul (Rx.c "act") e from rfl, ev_mul_gate e hA] at h

theorem bit_le (H : Hyps tr t r pub) {g : String} {w : Nat} (hg : (g, w) ∈ Rx.bitGroups) {i : Nat}
    (hi : i < w) : cb tr t r pub g i ≤ 1 := by
  have hm : bool (Rx.c g i) ∈ Rx.constraints := by
    unfold Rx.constraints
    simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inl ⟨(g, w), hg, i, hi, rfl⟩))
  exact bool_le (H.cons _ hm)

/-! ## The gadget instances, at the byte level -/

@[simp] theorem ize_one : ize tr t r pub (1 : Expr) = 1 := rfl
@[simp] theorem ize_zero : ize tr t r pub (0 : Expr) = 0 := rfl

@[simp] theorem ize_bytes (n : Nat) (a : Nat → Expr) (k : Nat) :
    ize tr t r pub (Rx.bytes n a k) = if k < n then ize tr t r pub (a k) else 0 := by
  unfold Rx.bytes; split <;> rfl

/-- Two byte addends, carries `< 256`. -/
theorem L_sum2 {N : Nat} (hN : 0 < N) {a b rr cy : Nat → Expr} {top : Expr} {A B R C : Nat → Nat} {tp : Nat}
    (hz : ∀ e ∈ Rx.lin N (Rx.add2 a b) rr cy top, ev tr t r pub e = 0)
    (hA : ∀ k < N, ize tr t r pub (a k) = A k) (hB : ∀ k < N, ize tr t r pub (b k) = B k)
    (hR : ∀ k < N, ize tr t r pub (rr k) = R k) (hC : ∀ k, k + 1 < N → ize tr t r pub (cy k) = C k)
    (htop : ize tr t r pub top = tp)
    (bA : ∀ k < N, A k < 256) (bB : ∀ k < N, B k < 256) (bR : ∀ k < N, R k < 256)
    (bC : ∀ k, k + 1 < N → C k < 256) (btp : tp < 256) :
    val A N + val B N = val R N + 256 ^ N * tp := by
  have h := lin_val hN hz (fun k => A k + B k) R C tp
    (fun k hk => by simp only [ize_add2, hA k hk, hB k hk]; push_cast; rfl) hR hC htop
    (fun k hk => by
      have := bA k hk; have := bB k hk
      split
      · unfold PP; omega
      · have := bC (k - 1) (by omega); unfold PP; omega)
    (fun k hk => by
      have := bR k hk
      split
      · unfold PP; omega
      · have := bC k (by omega); unfold PP; omega)
  rwa [val_add] at h

/-- Three byte addends (the first a constant), carries `< 256`. -/
theorem L_sum3 {N : Nat} (hN : 0 < N) {a b d rr cy : Nat → Expr} {A B D R C : Nat → Nat}
    (hz : ∀ e ∈ Rx.lin N (Rx.add3 a b d) rr cy (0 : Expr), ev tr t r pub e = 0)
    (hA : ∀ k < N, ize tr t r pub (a k) = A k) (hB : ∀ k < N, ize tr t r pub (b k) = B k)
    (hD : ∀ k < N, ize tr t r pub (d k) = D k)
    (hR : ∀ k < N, ize tr t r pub (rr k) = R k) (hC : ∀ k, k + 1 < N → ize tr t r pub (cy k) = C k)
    (bA : ∀ k < N, A k < 256) (bB : ∀ k < N, B k < 256) (bD : ∀ k < N, D k < 256)
    (bR : ∀ k < N, R k < 256) (bC : ∀ k, k + 1 < N → C k < 256) :
    val A N + val B N + val D N = val R N := by
  have h := lin_val hN hz (fun k => A k + B k + D k) R C 0
    (fun k hk => by simp only [ize_add3, hA k hk, hB k hk, hD k hk]; push_cast; rfl) hR hC rfl
    (fun k hk => by
      have := bA k hk; have := bB k hk; have := bD k hk
      split
      · unfold PP; omega
      · have := bC (k - 1) (by omega); unfold PP; omega)
    (fun k hk => by
      have := bR k hk
      split
      · unfold PP; omega
      · have := bC k (by omega); unfold PP; omega)
  rw [val_add, val_add] at h; omega

/-- A product `a·b` into `nr` bytes (`Rx.mulG`). -/
theorem L_mul {na nb nr : Nat} (hpos : 0 < na + nb) (hnr : nr ≤ na + nb) (hna : na ≤ 16)
    {a b : Nat → Expr} {rg cyg : String} {A B : Nat → Nat}
    (hz : ∀ e ∈ Rx.mulG a na b nb rg nr cyg, ev tr t r pub e = 0)
    (hA : ∀ i < na, ize tr t r pub (a i) = A i) (hB : ∀ j < nb, ize tr t r pub (b j) = B j)
    (bA : ∀ i < na, A i < 256) (bB : ∀ j < nb, B j < 256)
    (bR : ∀ k < nr, cb tr t r pub rg k < 256) (bC : ∀ k < 2 * (na + nb - 1), cb tr t r pub cyg k < 256) :
    val (conv A B na nb) (na + nb) = val (cb tr t r pub rg) nr := by
  have h := lin_val (N := na + nb) hpos hz (conv A B na nb) (fun k => if k < nr then cb tr t r pub rg k else 0)
    (fun k => cb tr t r pub cyg (2 * k) + 256 * cb tr t r pub cyg (2 * k + 1)) 0
    (fun k _ => ize_mulT a b na nb k A B hA hB)
    (fun k _ => by rw [ize_bytes]; split <;> simp)
    (fun k _ => by simp only [ize_cy2]; omega) rfl
    (fun k hk => by
      try dsimp only
      have := conv_le A B na nb k bA bB
      have : na * 65025 ≤ 16 * 65025 := Nat.mul_le_mul_right _ hna
      have h2 : (if k = 0 then 0 else cb tr t r pub cyg (2 * (k - 1)) + 256 * cb tr t r pub cyg (2 * (k - 1) + 1))
          < 65536 := by
        split
        · omega
        · have := bC (2 * (k - 1)) (by omega); have := bC (2 * (k - 1) + 1) (by omega); omega
      unfold PP; omega)
    (fun k hk => by
      try dsimp only
      have h1 : (if k < nr then cb tr t r pub rg k else 0) < 256 := by
        split
        · exact bR k ‹_›
        · omega
      have h2 : (if k + 1 = na + nb then 0 else cb tr t r pub cyg (2 * k) + 256 * cb tr t r pub cyg (2 * k + 1))
          < 65536 := by
        split
        · omega
        · have := bC (2 * k) (by omega); have := bC (2 * k + 1) (by omega); omega
      unfold PP; omega)
  rw [h, val_pad _ _ _ hnr]; simp

set_option maxHeartbeats 4000000 in
theorem conv_16_8 (A B : Nat → Nat) : val (conv A B 16 8) (16 + 8) = val A 16 * val B 8 := by
  simp [val, conv, List.range, List.range.loop]
  grind

set_option maxHeartbeats 4000000 in
theorem conv_8_8 (A B : Nat → Nat) : val (conv A B 8 8) (8 + 8) = val A 8 * val B 8 := by
  simp [val, conv, List.range, List.range.loop]
  grind

set_option maxHeartbeats 4000000 in
theorem conv_16_6 (A B : Nat → Nat) : val (conv A B 16 6) (16 + 6) = val A 16 * val B 6 := by
  simp [val, conv, List.range, List.range.loop]
  grind

set_option maxHeartbeats 4000000 in
theorem conv_3_3 (A B : Nat → Nat) : val (conv A B 3 3) 8 = val A 3 * val B 3 := by
  simp [val, conv, List.range, List.range.loop]
  grind

theorem kb_lt (v k : Nat) : v / 256 ^ k % 256 < 256 := Nat.mod_lt _ (by decide)

theorem val4 (f : Nat → Nat) : val f 4 = f 0 + 256 * f 1 + 65536 * f 2 + 16777216 * f 3 := by
  simp [val]

theorem cb_lt (g : String) (k : Nat) : cb tr t r pub g k < PP := ev_lt _

/-- membership of a sub-list of `Rx.arith` -/
macro "inA" H:term : term =>
  `(fun e he => arith_zero $H e (by unfold Rx.arith; simp only [List.mem_append, he, true_or, or_true]))

theorem lens (H : Hyps tr t r pub) :
    cb tr t r pub "lm" 0 < 65536 ∧ cb tr t r pub "la" 0 < 16777216 ∧
      gv tr t r pub "nb" 3 = cb tr t r pub "lm" 0 + cb tr t r pub "la" 0 := by
  have bl := H.bytes "lmb" 2 (by simp [Rx.byteGroups])
  have ba := H.bytes "lab" 3 (by simp [Rx.byteGroups])
  have bn := H.bytes "nb" 3 (by simp [Rx.byteGroups])
  have l0 := bl 0 (by omega); have l1 := bl 1 (by omega)
  have a0 := ba 0 (by omega); have a1 := ba 1 (by omega); have a2 := ba 2 (by omega)
  have n0 := bn 0 (by omega); have n1 := bn 1 (by omega); have n2 := bn 2 (by omega)
  have hlm := cb_lt (tr := tr) (t := t) (r := r) (pub := pub) "lm" 0
  have hla := cb_lt (tr := tr) (t := t) (r := r) (pub := pub) "la" 0
  have e1 := arith_zero H (Rx.c "lm" - leVal (Rx.bv "lmb") 2)
    (by unfold Rx.arith; simp only [List.mem_append, List.mem_cons]; simp)
  have e2 := arith_zero H (Rx.c "la" - leVal (Rx.bv "lab") 3)
    (by unfold Rx.arith; simp only [List.mem_append, List.mem_cons]; simp)
  have e3 := arith_zero H (leVal (Rx.bv "nb") 3 - Rx.c "lm" - Rx.c "la")
    (by unfold Rx.arith; simp only [List.mem_append, List.mem_cons]; simp)
  have z1 := ize_eq_zero e1
  have z2 := ize_eq_zero e2
  have z3 := ize_eq_zero e3
  simp only [leVal, ize_hsub, ize_c, ize_sumE, List.range, List.range.loop, List.map, ize_hmul, ize_K,
    ize_bv, List.sum_cons, List.sum_nil] at z1 z2 z3
  unfold PP at *
  have q1 := z1 (by omega) (by omega)
  have q2 := z2 (by omega) (by omega)
  have q3 := z3 (by omega) (by omega)
  refine ⟨by omega, by omega, ?_⟩
  unfold gv; simp only [val]; omega

/-! ## Byte and bit facts as functions -/

theorem byt (H : Hyps tr t r pub) (g : String) (w : Nat) (hg : (g, w) ∈ Rx.byteGroups) :
    ∀ k < w, cb tr t r pub g k < 256 := H.bytes g w hg

theorem bit (H : Hyps tr t r pub) (g : String) (w : Nat) (hg : (g, w) ∈ Rx.bitGroups) :
    ∀ k, k + 1 < w + 1 → cb tr t r pub g k < 256 := fun k hk => by
  have := bit_le H hg (i := k) (by omega); omega

theorem bit1 (H : Hyps tr t r pub) (g : String) (hg : (g, 1) ∈ Rx.bitGroups) : cb tr t r pub g 0 ≤ 1 :=
  bit_le H hg (by omega)

theorem val_lt' (f : Nat → Nat) (n : Nat) (h : ∀ k < n, f k < 256) : val f n < 256 ^ n := val_lt f n h

/-- `S · inv − 1 = 0` in the field: `S ≠ 0` in the field. -/
theorem nz_lemma {S inv : Expr} (h : ev tr t r pub (S * inv - 1) = 0) : ev tr t r pub S ≠ 0 := by
  intro h0
  have h' : ev tr t r pub (Expr.add (Expr.mul S inv) (Expr.neg (Expr.const 1))) = 0 := h
  simp only [ev_add, ev_mul, ev_neg, ev_const, h0, Nat.zero_mul, Nat.zero_mod] at h'
  omega

theorem ev_of_ize {e : Expr} (n : Nat) (h : ize tr t r pub e = n) (hn : n < PP) : ev tr t r pub e = n := by
  have := ize_mod (tr := tr) (t := t) (r := r) (pub := pub) e
  rw [h] at this; unfold PP at *; omega

theorem val_smul (c : Nat) (f : Nat → Nat) (n : Nat) : val (fun k => c * f k) n = c * val f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [val, ih, Nat.mul_add]; rw [Nat.mul_left_comm]

theorem val_first (x : Nat) (n : Nat) (hn : 0 < n) : val (fun k => if k = 0 then x else 0) n = x := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [val]
    · simp only [val, ih h, show ¬ n = 0 by omega, ite_false, Nat.mul_zero, Nat.add_zero]

theorem mem_bytes {g : String} {w : Nat} (h : (g, w) ∈ Rx.byteGroups) : (g, w) ∈ Rx.byteGroups := h

/-! ## The instances -/

theorem p_fcx (H : Hyps tr t r pub) :
    gv tr t r pub "fcx" 8 = FC_BASE_EXEC + FC_BYTE_EXEC * gv tr t r pub "nb" 3 := by
  have bn := byt H "nb" 3 (by simp [Rx.byteGroups])
  have bf := byt H "fcx" 8 (by simp [Rx.byteGroups])
  have bc := byt H "cfx" 14 (by simp [Rx.byteGroups])
  have h := lin_val (N := 8)
    (terms := fun k => Rx.kb FC_BASE_EXEC k + Rx.mulT (Rx.bv "nb") 3 (Rx.kb FC_BYTE_EXEC) 3 k)
    (rr := Rx.bv "fcx") (cy := Rx.cy2 "cfx") (top := (0 : Expr)) (by decide) (inA H)
    (fun k => FC_BASE_EXEC / 256 ^ k % 256 + conv (cb tr t r pub "nb") (fun j => FC_BYTE_EXEC / 256 ^ j % 256) 3 3 k)
    (cb tr t r pub "fcx") (fun k => cb tr t r pub "cfx" (2 * k) + 256 * cb tr t r pub "cfx" (2 * k + 1)) 0
    (fun k _ => by
      simp only [ize_hadd, ize_kb]
      rw [ize_mulT (Rx.bv "nb") (Rx.kb FC_BYTE_EXEC) 3 3 k (cb tr t r pub "nb") (fun j => FC_BYTE_EXEC / 256 ^ j % 256)
        (fun i _ => rfl) (fun j _ => rfl)]
      omega)
    (fun k _ => rfl) (fun k _ => by simp only [ize_cy2]; omega) rfl
    (fun k hk => by
      have := conv_le (cb tr t r pub "nb") (fun j => FC_BYTE_EXEC / 256 ^ j % 256) 3 3 k bn (fun j _ => kb_lt _ _)
      have := kb_lt FC_BASE_EXEC k
      have h2 : (if k = 0 then 0 else cb tr t r pub "cfx" (2 * (k - 1)) + 256 * cb tr t r pub "cfx" (2 * (k - 1) + 1))
          < 65536 := by
        split
        · omega
        · have := bc (2 * (k - 1)) (by omega); have := bc (2 * (k - 1) + 1) (by omega); omega
      unfold PP; omega)
    (fun k hk => by
      have := bf k hk
      have h2 : (if k + 1 = 8 then 0 else cb tr t r pub "cfx" (2 * k) + 256 * cb tr t r pub "cfx" (2 * k + 1))
          < 65536 := by
        split
        · omega
        · have := bc (2 * k) (by omega); have := bc (2 * k + 1) (by omega); omega
      unfold PP; omega)
  rw [val_add, conv_3_3, show val (fun k => FC_BASE_EXEC / 256 ^ k % 256) 8 = FC_BASE_EXEC by decide,
    show val (fun j => FC_BYTE_EXEC / 256 ^ j % 256) 3 = FC_BYTE_EXEC by decide] at h
  unfold gv; rw [Nat.mul_comm FC_BYTE_EXEC]; omega

/-- the three-term sums `nar + fcx + x = y` -/
theorem p_sum3 (H : Hyps tr t r pub) (x y cy : String) (hx : (x, 8) ∈ Rx.byteGroups)
    (hy : (y, 8) ∈ Rx.byteGroups) (hc : (cy, 7) ∈ Rx.byteGroups)
    (hz : ∀ e ∈ Rx.lin 8 (Rx.add3 (Rx.kb NAR_EXEC) (Rx.bv "fcx") (Rx.bv x)) (Rx.bv y) (Rx.bv cy) (0 : Expr),
      ev tr t r pub e = 0) :
    NAR_EXEC + gv tr t r pub "fcx" 8 + gv tr t r pub x 8 = gv tr t r pub y 8 := by
  have h := L_sum3 (N := 8) (by decide) hz (A := fun k => NAR_EXEC / 256 ^ k % 256) (B := cb tr t r pub "fcx")
    (D := cb tr t r pub x) (R := cb tr t r pub y) (C := cb tr t r pub cy)
    (fun k _ => rfl) (fun k _ => rfl) (fun k _ => rfl) (fun k _ => rfl) (fun k _ => rfl)
    (fun k _ => kb_lt _ _) (byt H "fcx" 8 (by simp [Rx.byteGroups])) (byt H x 8 hx) (byt H y 8 hy)
    (fun k hk => byt H cy 7 hc k (by omega))
  rw [show val (fun k => NAR_EXEC / 256 ^ k % 256) 8 = NAR_EXEC by decide] at h
  unfold gv; omega

/-- two-term sums of byte groups with bit carries: `x + y = z + 2^(8N)·top` -/
theorem p_sum2 (H : Hyps tr t r pub) (N : Nat) (hN : 0 < N) (x y z cy : String) (top : Expr) (tp : Nat)
    (hx : (x, N) ∈ Rx.byteGroups) (hy : (y, N) ∈ Rx.byteGroups) (hzz : (z, N) ∈ Rx.byteGroups)
    (hc : (cy, N - 1) ∈ Rx.bitGroups) (htop : ize tr t r pub top = tp) (htp : tp ≤ 1)
    (hz : ∀ e ∈ Rx.lin N (Rx.add2 (Rx.bv x) (Rx.bv y)) (Rx.bv z) (Rx.bv cy) top, ev tr t r pub e = 0) :
    gv tr t r pub x N + gv tr t r pub y N = gv tr t r pub z N + 256 ^ N * tp := by
  exact L_sum2 hN hz (A := cb tr t r pub x) (B := cb tr t r pub y) (R := cb tr t r pub z) (C := cb tr t r pub cy)
    (fun k _ => rfl) (fun k _ => rfl) (fun k _ => rfl) (fun k _ => rfl) htop
    (byt H x N hx) (byt H y N hy) (byt H z N hzz) (fun k hk => bit H cy (N - 1) hc k (by omega)) (by omega)

/-- products of byte groups -/
theorem p_mul (H : Hyps tr t r pub) {na nb : Nat} (hpos : 0 < na + nb) (hna : na ≤ 16) (hnr : 16 ≤ na + nb)
    {a b : Nat → Expr} {A B : Nat → Nat} (rg cyg : String)
    (hz : ∀ e ∈ Rx.mulG a na b nb rg 16 cyg, ev tr t r pub e = 0)
    (hA : ∀ i < na, ize tr t r pub (a i) = A i) (hB : ∀ j < nb, ize tr t r pub (b j) = B j)
    (bA : ∀ i < na, A i < 256) (bB : ∀ j < nb, B j < 256)
    (hr : (rg, 16) ∈ Rx.byteGroups) (hc : (cyg, 2 * (na + nb - 1)) ∈ Rx.byteGroups) :
    val (conv A B na nb) (na + nb) = gv tr t r pub rg 16 :=
  L_mul hpos hnr hna hz hA hB bA bB (byt H rg 16 hr) (byt H cyg _ hc)

/-- `x·y` with `x`, `y` byte groups -/
theorem p_mulbb (H : Hyps tr t r pub) {na nb : Nat} (hpos : 0 < na + nb) (hna : na ≤ 16) (hnr : 16 ≤ na + nb)
    (x y rg cyg : String) (hx : (x, na) ∈ Rx.byteGroups) (hy : (y, nb) ∈ Rx.byteGroups)
    (hr : (rg, 16) ∈ Rx.byteGroups) (hc : (cyg, 2 * (na + nb - 1)) ∈ Rx.byteGroups)
    (hz : ∀ e ∈ Rx.mulG (Rx.bv x) na (Rx.bv y) nb rg 16 cyg, ev tr t r pub e = 0) :
    val (conv (cb tr t r pub x) (cb tr t r pub y) na nb) (na + nb) = gv tr t r pub rg 16 :=
  p_mul H hpos hna hnr rg cyg hz (fun i _ => rfl) (fun j _ => rfl) (byt H x na hx) (byt H y nb hy) hr hc

theorem p_burn (H : Hyps tr t r pub) :
    gv tr t r pub "burn" 16 = min (gv tr t r pub "gp" 16) (gv tr t r pub "egp" 16) := by
  have hbm := bit1 H "bm" (by simp [Rx.bitGroups])
  have hd := p_sum2 H 16 (by decide) "egp" "dmn" "gp" "cmn" (Rx.c "bm") (cb tr t r pub "bm" 0)
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups])
    rfl hbm (inA H)
  have bg := byt H "gp" 16 (by simp [Rx.byteGroups])
  have be := byt H "egp" 16 (by simp [Rx.byteGroups])
  have bd := byt H "dmn" 16 (by simp [Rx.byteGroups])
  have hk : ∀ k < 16, (ize tr t r pub (Rx.c "burn" k) - ize tr t r pub (Rx.c "bm") * ize tr t r pub (Rx.c "gp" k) -
      (1 - ize tr t r pub (Rx.c "bm")) * ize tr t r pub (Rx.c "egp" k) = 0) := by
    intro k hk
    have e := arith_zero H (Rx.c "burn" k - Rx.c "bm" * Rx.c "gp" k - (1 - Rx.c "bm") * Rx.c "egp" k)
      (by unfold Rx.arith; simp only [List.mem_append, List.mem_map, List.mem_range]
          repeat (first | exact Or.inr ⟨k, hk, rfl⟩ | apply Or.inl))
    have z := ize_eq_zero e
    have hb := cb_lt (tr := tr) (t := t) (r := r) (pub := pub) "burn" k
    have g1 := bg k hk; have g2 := be k hk
    simp only [ize_hsub, ize_hmul, ize_c, ize_one] at z ⊢
    unfold PP at *
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hbm with h0 | h1
    · rw [h0] at z ⊢; exact z (by omega) (by omega)
    · rw [h1] at z ⊢; exact z (by omega) (by omega)
  simp only [ize_c] at hk
  unfold gv at hd ⊢
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hbm with h0 | h1
  · rw [val_congr (cb tr t r pub "burn") (cb tr t r pub "egp") 16 (fun k hk' => by
        have := hk k hk'; rw [h0] at this; omega)]
    rw [h0] at hd
    omega
  · rw [val_congr (cb tr t r pub "burn") (cb tr t r pub "gp") 16 (fun k hk' => by
        have := hk k hk'; rw [h1] at this; omega)]
    rw [h1] at hd
    have := val_lt' _ 16 bd
    omega

end M5T1.RxField
