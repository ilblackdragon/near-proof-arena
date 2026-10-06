import ZkFormal.NearV3.Sched.View.Mem
import ZkFormal.NearV3.Sched.Tables.Codec

/-!
# ZkFormal.NearV3.Sched.View.Codec — row facts of the codec table `schV3`

`CLocal` is every codec constraint on every row. From it:

* kinds: `act = kH + kR + kZ + kA` one-hot bits, `kR = fS + fR + fA`, `kF ≤ kH`; an active row
  is not the last row (`act_next`);
* bytes: on encoding rows (`kH + kR + kZ = 1`) `bpost` and `bpre` are their 8-bit
  decompositions (`< 256`); `pres = 0 ⇒ bpre = 0`;
* gadgets (`isZ`): `e7 = [g = 7]` (record rows), `e2 = [g = 2]` (allowance rows),
  `ekl = [kidx + 1 ≡ NN]` (record rows), `ehp = [pos = 4]` (header rows),
  `esj = [sj = 31 + 32·kA]` (hash / ash rows), `zt = [τ = 0]` (active rows); each flag is 0
  where its gate is 0;
* carries: the instance constants to the next row (`gT = 1`), `pos + 1` on encoding rows, the
  record data `al, gb, srcC, hasC, useC` inside a record.

Value equations are stated over naturals modulo `P` where the cells are arbitrary field
elements.
-/

namespace ZkFormal.NearV3.Sched.Codec

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

abbrev CLocal (tr : Trace Fp) (t : Nat) (pub : List Fp) : Prop := Local constraints tr t pub

/-- Simp set for evaluating a codec constraint. -/
macro "zs " h:ident " [" ts:term,* "]" : tactic => do
  let ls ← ts.getElems.mapM fun x => `(Lean.Parser.Tactic.simpLemma| $x:term)
  `(tactic| simp only [mul3, notE, gT, encG, oE, aLE, ftE, zev_mul, zev_sub, zev_add, zev_c, zev_n,
      zev_k, zev_smul, cur_cv, $ls,*] at $h:ident)

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-! ## Membership -/

theorem mem_bool {x : Nat} (hx : x ∈ boolCols) : ZkFormal.Chacha.Table.boolC x ∈ constraints := by
  unfold constraints cKind
  iterate 13 apply List.mem_append_left
  exact List.mem_map_of_mem hx

theorem mem_rbool {x : Nat} (hx : x ∈ recBoolCols) :
    Expr.mul (c kR) (ZkFormal.Chacha.Table.boolC x) ∈ constraints := by
  unfold constraints cKind
  iterate 12 apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_map.2 ⟨x, hx, rfl⟩)

theorem mem_hshift {i : Nat} (hi : i < 31) :
    mul3 (c kH) (notE (c ehp)) (sub (n (reg i)) (c (reg (i + 1)))) ∈ constraints := by
  unfold constraints cKind
  iterate 3 apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)

theorem mem_zshift {i : Nat} (hi : i < 31) :
    mul3 (c kZ) (notE (c esj)) (sub (n (reg i)) (c (reg (i + 1)))) ∈ constraints := by
  unfold constraints cTrl
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))

theorem mem_rcarry {x : Nat} (hx : x ∈ [al, gb, srcC, hasC, useC]) :
    Expr.mul (sub (c kR) (c rend)) (sub (n x) (c x)) ∈ constraints := by
  unfold constraints cRec
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.2 ⟨x, hx, rfl⟩

/-! ## Evaluation helpers -/

theorem zd (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) {e : Expr}
    (he : e ∈ constraints) : ∃ q : Int, zev (tenv tr t r pub) e = 2013265921 * q :=
  Mem.zdvd hL hr he

theorem lt (r x : Nat) : cv tr t r x < 2013265921 := cv_lt r x

theorem bool_of_eval {r x : Nat} (h : (ZkFormal.Chacha.Table.boolC x).eval tr t r pub = 0) :
    cv tr t r x ≤ 1 := by
  have h' : Fp.mul (tr.cell t r x) (Fp.add (tr.cell t r x) (Fp.neg (Fp.ofNat 1))) = 0 := h
  rcases ZkFormal.Sha.fp_mul_eq_zero h' with h0 | h1
  · unfold cv; rw [h0]; decide
  · have : tr.cell t r x = Fp.ofNat 1 := by
      have e := congrArg (fun z => Fp.add z (Fp.ofNat 1)) h1
      apply Fp.ext
      have h3 := congrArg Fp.toNat e
      simp only [Fp.toNat_add, Fp.toNat_neg, Fp.toNat_ofNat] at h3
      have := (tr.cell t r x).toNat_lt
      rw [show (0 : Fp) = Fp.ofNat 0 from rfl, Fp.toNat_ofNat] at h3
      rw [Fp.toNat_ofNat]
      unfold P at *
      omega
    unfold cv; rw [this]; decide

theorem bool_of (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) {x : Nat}
    (hx : x ∈ boolCols) : cv tr t r x ≤ 1 :=
  hL.bool hr (mem_bool hx)

/-- Record-row flags (`recBoolCols`) are bits on record rows. -/
theorem rbool_of (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (hk : cv tr t r kR = 1)
    {x : Nat} (hx : x ∈ recBoolCols) : cv tr t r x ≤ 1 := by
  have h := hL r hr _ (mem_rbool hx)
  have h' : Fp.mul (tr.cell t r kR) ((ZkFormal.Chacha.Table.boolC x).eval tr t r pub) = 0 := h
  rcases ZkFormal.Sha.fp_mul_eq_zero h' with h0 | h1
  · unfold cv at hk; rw [h0] at hk; exact absurd hk (by decide)
  · exact bool_of_eval h1

theorem nx {r : Nat} (hr : r + 1 < tr.height t) (x : Nat) :
    (tenv tr t r pub).nxt x = cv tr t (r + 1) x := nxt_cv hr x

/-! ## Kinds -/

/-- **Kinds.** -/
theorem kinds (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) :
    cv tr t r act ≤ 1 ∧ cv tr t r kH ≤ 1 ∧ cv tr t r kR ≤ 1 ∧ cv tr t r kZ ≤ 1 ∧
      cv tr t r kA ≤ 1 ∧ cv tr t r kF ≤ 1 ∧ cv tr t r fS ≤ 1 ∧ cv tr t r fR ≤ 1 ∧
      cv tr t r fA ≤ 1 ∧ cv tr t r pres ≤ 1 ∧
      cv tr t r act = cv tr t r kH + cv tr t r kR + cv tr t r kZ + cv tr t r kA ∧
      cv tr t r kR = cv tr t r fS + cv tr t r fR + cv tr t r fA ∧
      cv tr t r kF ≤ cv tr t r kH := by
  have b := fun x (hx : x ∈ boolCols) => bool_of hL hr hx
  have hA := b act (by simp [boolCols]); have hH := b kH (by simp [boolCols])
  have hR := b kR (by simp [boolCols]); have hZ := b kZ (by simp [boolCols])
  have hAa := b kA (by simp [boolCols]); have hF := b kF (by simp [boolCols])
  have hS := b fS (by simp [boolCols]); have hRr := b fR (by simp [boolCols])
  have hAl := b fA (by simp [boolCols]); have hP := b pres (by simp [boolCols])
  obtain ⟨q1, c1⟩ := zd hL hr (e := sub (c act) (.add (c kH) (.add (c kR) (.add (c kZ) (c kA)))))
    (by simp [constraints, cKind])
  obtain ⟨q2, c2⟩ := zd hL hr (e := sub (c kR) (.add (c fS) (.add (c fR) (c fA))))
    (by simp [constraints, cKind])
  obtain ⟨q3, c3⟩ := zd hL hr (e := .mul (c kF) (notE (c kH))) (by simp [constraints, cKind])
  zs c1 []; zs c2 []; zs c3 []
  refine ⟨hA, hH, hR, hZ, hAa, hF, hS, hRr, hAl, hP, by omega, by omega, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hF with h | h <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hH with h' | h' <;> rw [h, h'] at c3 ⊢ <;> omega

/-- An active row is not the last row. -/
theorem act_next (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (ha : cv tr t r act = 1) :
    r + 1 < tr.height t := by
  rcases Nat.lt_or_ge (r + 1) (tr.height t) with h | h
  · exact h
  · obtain ⟨q, c1⟩ := zd hL hr (e := .mul .isLast (c act)) (by simp [constraints, cKind])
    simp only [zev_mul, zev_c, cur_cv, ha] at c1
    simp only [zev, tenv, if_pos (show r + 1 = tr.height t by omega)] at c1
    omega

/-! ## Bytes -/

theorem mem_bool_pbit {i : Nat} (hi : i < 8) : pbit i ∈ boolCols := by
  unfold boolCols
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.2 hi)))

theorem mem_bool_prbit {i : Nat} (hi : i < 8) : prbit i ∈ boolCols := by
  unfold boolCols
  exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_range.2 hi))

theorem num_eval (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (col : Nat → Nat)
    (hc : ∀ i, i < 8 → col i ∈ boolCols) :
    zev (tenv tr t r pub) (ZkFormal.Chacha.Rng.Table.num col 8) = (numv tr t r col 8 : Int) ∧
      numv tr t r col 8 < 2 ^ 8 := by
  refine ⟨?_, nbits_le_of (fun i hi => bool_of hL hr (hc i hi))⟩
  unfold ZkFormal.Chacha.Rng.Table.num numv
  exact zev_sum_pow _ (fun b => .col (col b) false) (fun b => cv tr t r (col b)) 8 (fun _ _ => rfl)

/-- **Bytes.** On an encoding row the post and pre bytes are their bit decompositions. -/
theorem bytes (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t)
    (he : cv tr t r kH + cv tr t r kR + cv tr t r kZ = 1) :
    cv tr t r bpost = numv tr t r pbit 8 ∧ cv tr t r bpost < 256 ∧
      cv tr t r bpre = numv tr t r prbit 8 ∧ cv tr t r bpre < 256 := by
  obtain ⟨e1, b1⟩ := num_eval hL hr pbit (fun _ hi => mem_bool_pbit hi)
  obtain ⟨e2, b2⟩ := num_eval hL hr prbit (fun _ hi => mem_bool_prbit hi)
  obtain ⟨q1, c1⟩ := zd hL hr (e := .mul encG (sub (c bpost) pbitsE)) (by simp [constraints, cKind])
  obtain ⟨q2, c2⟩ := zd hL hr (e := .mul encG (sub (c bpre) (ZkFormal.Chacha.Rng.Table.num prbit 8)))
    (by simp [constraints, cKind])
  zs c1 [pbitsE, e1]; zs c2 [e2]
  have := lt (tr := tr) (t := t) r bpost; have := lt (tr := tr) (t := t) r bpre
  have hb1 : numv tr t r pbit 8 < 256 := b1
  have hb2 : numv tr t r prbit 8 < 256 := b2
  have h1 : (cv tr t r kH : Int) + (cv tr t r kR + cv tr t r kZ) = 1 := by omega
  rw [h1] at c1 c2
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- Absent previous state: every pre byte is 0. -/
theorem pre_absent (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t)
    (hp : cv tr t r pres = 0) : cv tr t r bpre = 0 := by
  obtain ⟨q, c1⟩ := zd hL hr (e := .mul (notE (c pres)) (c bpre)) (by simp [constraints, cKind])
  zs c1 [hp]
  have := lt (tr := tr) (t := t) r bpre
  omega

/-! ## Gadgets -/

theorem isZ_flag (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) {gate x : Expr}
    {inv flag : Nat} (hm : ∀ e ∈ isZ gate x inv flag, e ∈ constraints) (hb : cv tr t r flag ≤ 1) :
    (zev (tenv tr t r pub) gate = 1 →
      (cv tr t r flag = 1 ↔ zev (tenv tr t r pub) x % 2013265921 = 0)) ∧
    (zev (tenv tr t r pub) gate = 0 → cv tr t r flag = 0) := by
  obtain ⟨q1, c1⟩ := zd hL hr (hm (.mul gate (sub (c flag) (notE (.mul x (c inv))))) (by simp [isZ]))
  obtain ⟨q2, c2⟩ := zd hL hr (hm (.mul gate (.mul x (c flag))) (by simp [isZ]))
  obtain ⟨q3, c3⟩ := zd hL hr (hm (.mul (notE gate) (c flag)) (by simp [isZ]))
  simp only [notE, zev_mul, zev_sub, zev_c, zev_k, cur_cv] at c1 c2 c3
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · rw [hg] at c1 c2
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h | h <;> rw [h] at c1 c2 ⊢
    · constructor
      · intro h; omega
      · intro hx
        have hm := Int.mul_emod (zev (tenv tr t r pub) x) (cv tr t r inv) 2013265921
        rw [hx, Int.zero_mul, Int.zero_emod] at hm
        generalize zev (tenv tr t r pub) x * (cv tr t r inv : Int) = y at c1 hm
        omega
    · constructor
      · intro _
        generalize zev (tenv tr t r pub) x = y at c2
        omega
      · intro _; rfl
  · rw [hg] at c3
    omega

theorem mem_isZ_e7 : ∀ e ∈ isZ (c kR) (sub (c g) (k 7)) ig7 e7, e ∈ constraints := by
  intro e he; simp only [isZ, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> simp [constraints, cKind, isZ]
theorem mem_isZ_e2 : ∀ e ∈ isZ (c fA) (sub (c g) (k 2)) ig2 e2, e ∈ constraints := by
  intro e he; simp only [isZ, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> simp [constraints, cKind, isZ]
theorem mem_isZ_ekl : ∀ e ∈ isZ (c kR) (sub (c kidx) (sub (c NN) (k 1))) ikl ekl, e ∈ constraints := by
  intro e he; simp only [isZ, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> simp [constraints, cKind, isZ]
theorem mem_isZ_ehp : ∀ e ∈ isZ (c kH) (sub (c pos) (k 4)) ihp ehp, e ∈ constraints := by
  intro e he; simp only [isZ, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> simp [constraints, cKind, isZ]
theorem mem_isZ_esj :
    ∀ e ∈ isZ (.add (c kZ) (c kA)) (sub (c sj) (.add (k 31) (smul 32 (c kA)))) isj esj,
      e ∈ constraints := by
  intro e he; simp only [isZ, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> simp [constraints, cKind, isZ]
theorem mem_isZ_zt : ∀ e ∈ isZ (c act) (c tau) itz zt, e ∈ constraints := by
  intro e he; simp only [isZ, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> simp [constraints, cKind, isZ]

/-- **`e7 = [g = 7]`** on record rows, 0 elsewhere. -/
theorem e7_iff (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) :
    (cv tr t r kR = 1 → (cv tr t r e7 = 1 ↔ cv tr t r g = 7)) ∧
      (cv tr t r kR = 0 → cv tr t r e7 = 0) := by
  have H := isZ_flag hL hr mem_isZ_e7 (bool_of hL hr (x := e7) (by simp [boolCols]))
  simp only [zev_sub, zev_c, zev_k, cur_cv] at H
  have := lt (tr := tr) (t := t) r g
  refine ⟨fun h => ?_, fun h => H.2 (by rw [h]; rfl)⟩
  rw [H.1 (by rw [h]; rfl)]; omega

/-- **`e2 = [g = 2]`** on allowance rows, 0 elsewhere. -/
theorem e2_iff (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) :
    (cv tr t r fA = 1 → (cv tr t r e2 = 1 ↔ cv tr t r g = 2)) ∧
      (cv tr t r fA = 0 → cv tr t r e2 = 0) := by
  have H := isZ_flag hL hr mem_isZ_e2 (bool_of hL hr (x := e2) (by simp [boolCols]))
  simp only [zev_sub, zev_c, zev_k, cur_cv] at H
  have := lt (tr := tr) (t := t) r g
  refine ⟨fun h => ?_, fun h => H.2 (by rw [h]; rfl)⟩
  rw [H.1 (by rw [h]; rfl)]; omega

/-- **`ekl = [kidx + 1 ≡ NN]`** on record rows (the last record), 0 elsewhere. -/
theorem ekl_iff (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) :
    (cv tr t r kR = 1 → (cv tr t r ekl = 1 ↔ (cv tr t r kidx + 1) % 2013265921 = cv tr t r NN)) ∧
      (cv tr t r kR = 0 → cv tr t r ekl = 0) := by
  have H := isZ_flag hL hr mem_isZ_ekl (bool_of hL hr (x := ekl) (by simp [boolCols]))
  simp only [zev_sub, zev_c, zev_k, cur_cv] at H
  have := lt (tr := tr) (t := t) r kidx; have := lt (tr := tr) (t := t) r NN
  refine ⟨fun h => ?_, fun h => H.2 (by rw [h]; rfl)⟩
  rw [H.1 (by rw [h]; rfl)]; omega

/-- **`ehp = [pos = 4]`** on header rows, 0 elsewhere. -/
theorem ehp_iff (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) :
    (cv tr t r kH = 1 → (cv tr t r ehp = 1 ↔ cv tr t r pos = 4)) ∧
      (cv tr t r kH = 0 → cv tr t r ehp = 0) := by
  have H := isZ_flag hL hr mem_isZ_ehp (bool_of hL hr (x := ehp) (by simp [boolCols]))
  simp only [zev_sub, zev_c, zev_k, cur_cv] at H
  have := lt (tr := tr) (t := t) r pos
  refine ⟨fun h => ?_, fun h => H.2 (by rw [h]; rfl)⟩
  rw [H.1 (by rw [h]; rfl)]; omega

/-- **`esj = [sj = 31]`** on hash rows, **`[sj = 63]`** on ash rows, 0 elsewhere. -/
theorem esj_iff (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) :
    (cv tr t r kZ = 1 → (cv tr t r esj = 1 ↔ cv tr t r sj = 31)) ∧
      (cv tr t r kA = 1 → (cv tr t r esj = 1 ↔ cv tr t r sj = 63)) ∧
      (cv tr t r kZ = 0 → cv tr t r kA = 0 → cv tr t r esj = 0) := by
  have H := isZ_flag hL hr mem_isZ_esj (bool_of hL hr (x := esj) (by simp [boolCols]))
  have K := kinds hL hr
  simp only [zev_sub, zev_add, zev_smul, zev_c, zev_k, cur_cv] at H
  have := lt (tr := tr) (t := t) r sj
  refine ⟨fun h => ?_, fun h => ?_, fun h h' => H.2 (by rw [h, h']; rfl)⟩
  · have hA : cv tr t r kA = 0 := by omega
    rw [H.1 (by rw [h, hA]; rfl), hA]; omega
  · have hZ : cv tr t r kZ = 0 := by omega
    rw [H.1 (by rw [h, hZ]; rfl), h]; omega

/-- **`zt = [τ = 0]`** on active rows. -/
theorem zt_iff (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (ha : cv tr t r act = 1) :
    cv tr t r zt = 1 ↔ cv tr t r tau = 0 := by
  have H := isZ_flag hL hr mem_isZ_zt (bool_of hL hr (x := zt) (by simp [boolCols]))
  simp only [zev_c, cur_cv] at H
  have := lt (tr := tr) (t := t) r tau
  rw [H.1 (by rw [ha]; rfl)]; omega

/-! ## Carries -/

/-- The instance constants agree on two rows. -/
def IC (tr : Trace Fp) (t a b : Nat) : Prop := ∀ x ∈ instCols, cv tr t a x = cv tr t b x

theorem IC.trans {a b d : Nat} (h1 : IC tr t a b) (h2 : IC tr t b d) : IC tr t a d :=
  fun x hx => (h1 x hx).trans (h2 x hx)

theorem IC.refl (a : Nat) : IC tr t a a := fun _ _ => rfl

/-- **Instance constants** are carried to the next row on active rows other than the last ash
row. -/
theorem inst_next (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t)
    (ha : cv tr t r act = 1) (hz : cv tr t r kA = 0 ∨ cv tr t r esj = 0) :
    r + 1 < tr.height t ∧ IC tr t (r + 1) r := by
  have hr1 := act_next hL hr ha
  refine ⟨hr1, fun x hx => ?_⟩
  have hm : Expr.mul gT (sub (n x) (c x)) ∈ constraints := by
    simp only [instCols, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [constraints, cKind, gT]
  obtain ⟨q, c1⟩ := zd hL hr hm
  zs c1 [nx hr1, ha]
  have := lt (tr := tr) (t := t) r x; have := lt (tr := tr) (t := t) (r + 1) x
  rcases hz with h | h <;> rw [h] at c1 <;> omega

/-- **Byte position** advances on encoding rows. -/
theorem pos_next (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t)
    (he : cv tr t r kH + cv tr t r kR + cv tr t r kZ = 1) :
    r + 1 < tr.height t ∧ cv tr t (r + 1) pos = (cv tr t r pos + 1) % 2013265921 := by
  have K := kinds hL hr
  have hr1 := act_next hL hr (by omega)
  refine ⟨hr1, ?_⟩
  obtain ⟨q, c1⟩ := zd hL hr (e := .mul encG (sub (n pos) (.add (c pos) (k 1))))
    (by simp [constraints, cKind])
  zs c1 [nx hr1]
  have h1 : (cv tr t r kH : Int) + (cv tr t r kR + cv tr t r kZ) = 1 := by omega
  rw [h1] at c1
  have := lt (tr := tr) (t := t) r pos; have := lt (tr := tr) (t := t) (r + 1) pos
  omega

/-- **Record data** is carried inside a record. -/
theorem rec_next (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t)
    (hk : cv tr t r kR = 1) (he : cv tr t r rend = 0) {x : Nat}
    (hx : x ∈ [al, gb, srcC, hasC, useC]) :
    r + 1 < tr.height t ∧ cv tr t (r + 1) x = cv tr t r x := by
  have K := kinds hL hr
  have hr1 := act_next hL hr (by omega)
  refine ⟨hr1, ?_⟩
  obtain ⟨q, c1⟩ := zd hL hr (mem_rcarry hx)
  zs c1 [nx hr1, hk, he]
  have := lt (tr := tr) (t := t) r x; have := lt (tr := tr) (t := t) (r + 1) x
  omega

end

end ZkFormal.NearV3.Sched.Codec
