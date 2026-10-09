import ZkFormal.NearV3.Candidates.ProcSound.Entry

/-!
# ZkFormal.NearV3.Sched.View.ProcRow — row facts of the process table `sprV3`

From `PLocal` (every constraint on every row):

* kinds: `act = kK + kH + kE` one-hot bits, `kl ≤ kK`, `le ≤ kE`; an active row is not the last
  row (`act_next`); padding is a suffix (`pad_next`); the first row (`row_first`);
* gadgets: `kl = [kc = 15]` on key rows (`kl_iff`), header validity (`hdr_valid`: `[K ≠ 0]` via
  `iK` when `zk = 0`), the comparator gate and operands (`cmp_hdr`, `cmp_ent`), `zn` (`zn_def`);
  `lastf = [rem = 0]`, `za = [alOut = 0]` are `entry_row`;
* carries: the key register (`key_reg`), the key-row instance initial values (`key_init`),
  limbs over non-key rows (`limb_next`), instance carries (`inst_next`), round constants
  (`round_next`);
* transitions: key row → key row inside a block (`key_next`), block end / last entry → new block
  (`blk_next`), header → entry 0 (`hdr_next`), entry → entry (`ent_next`), the last entry
  (`le_entry`), and what may precede a header / entry (`prev_hdr`, `prev_ent`);
* `tau_le`: on an active row `w`, `τ ≤ w`.

Value equations are stated over naturals modulo `P` where the cells are arbitrary field
elements.
-/

namespace ZkFormal.NearV3.Candidates.ProcSound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Proc

/-- Simp set for evaluating a process-table constraint. -/
macro "rpz " h:ident " [" ts:term,* "]" : tactic => do
  let ls ← ts.getElems.mapM fun x => `(Lean.Parser.Tactic.simpLemma| $x:term)
  `(tactic| simp only [mul3, notE, gR, gB, tE, lidE, aS, aR, aL, zev_mul, zev_sub, zev_add, zev_c,
      zev_n, zev_k, zev_smul, cur_cv, $ls,*] at $h:ident)

section
variable {tr : Trace Fp} {tp : Nat} {pub : List Fp}

theorem zd (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp) {e : Expr}
    (he : e ∈ constraints) : ∃ q : Int, zev (tenv tr tp w pub) e = 2013265921 * q :=
  Mem.zdvd hL hw he

theorem lt (w col : Nat) : cv tr tp w col < 2013265921 := cv_lt w col

theorem nx {w : Nat} (hw : w + 1 < tr.height tp) (col : Nat) :
    (tenv tr tp w pub).nxt col = cv tr tp (w + 1) col := nxt_cv hw col

/-! ## Membership -/

theorem mem_rot {i : Nat} (hi : i < 16) :
    ProcBoundaryRepair.rotation i ∈ constraints := by
  unfold constraints cKey ProcBoundaryRepair.cKey
  simp only [Proc.cKey,List.take,List.drop]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
  apply List.mem_append_left; apply List.mem_append_right
  exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩

theorem mem_lcarry {i : Nat} (hi : i < 16) :
    mul3 (.add (c kH) (c kE)) (notE (n kK)) (sub (n (colL i)) (c (colL i))) ∈ constraints := by
  unfold constraints cKey ProcBoundaryRepair.cKey
  simp only [Proc.cKey,List.take,List.drop]
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
  apply List.mem_append_right
  exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩

theorem mem_round {col : Nat} (hc : col ∈ roundCols) :
    Expr.mul gR (sub (n col) (c col)) ∈ constraints := by
  unfold constraints cHdr
  apply List.mem_append_left; apply List.mem_append_right
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
  exact List.mem_map.2 ⟨col, hc, rfl⟩

theorem mem_inst {col : Nat} (hc : col ∈ instCols) :
    mul3 (.add (c kE) (c kK)) (notE (n kK)) (sub (n col) (c col)) ∈ constraints := by
  unfold constraints cHdr
  apply List.mem_append_left; apply List.mem_append_right
  apply List.mem_append_right
  exact List.mem_map.2 ⟨col, hc, rfl⟩

/-! ## Kinds -/

theorem le_gate (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp) {a b : Nat}
    (he : Expr.mul (c a) (notE (c b)) ∈ constraints) (ha : cv tr tp w a ≤ 1)
    (hb : cv tr tp w b ≤ 1) : cv tr tp w a ≤ cv tr tp w b := by
  obtain ⟨q, h⟩ := zd hL hw he
  rpz h []
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with h1 | h1 <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h2 | h2 <;> simp only [h1, h2] at h ⊢ <;> omega

/-- **Kinds.** -/
theorem kinds (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp) :
    cv tr tp w act ≤ 1 ∧ cv tr tp w kK ≤ 1 ∧ cv tr tp w kH ≤ 1 ∧ cv tr tp w kE ≤ 1 ∧
      cv tr tp w kl ≤ 1 ∧ cv tr tp w zk ≤ 1 ∧ cv tr tp w lastf ≤ 1 ∧ cv tr tp w le ≤ 1 ∧
      cv tr tp w act = cv tr tp w kK + cv tr tp w kH + cv tr tp w kE ∧
      cv tr tp w kl ≤ cv tr tp w kK ∧ cv tr tp w le ≤ cv tr tp w kE := by
  have b := fun col (hc : col ∈ boolCols) => bool_of hL hw hc
  have hA := b act (by simp [boolCols]); have hK := b kK (by simp [boolCols])
  have hH := b kH (by simp [boolCols]); have hE := b kE (by simp [boolCols])
  have hl := b kl (by simp [boolCols]); have hz := b zk (by simp [boolCols])
  have hlf := b lastf (by simp [boolCols]); have hle := b le (by simp [boolCols])
  obtain ⟨q, c1⟩ := zd hL hw (e := sub (c act) (.add (c kK) (.add (c kH) (c kE))))
    (by simp [constraints, cKind])
  rpz c1 []
  exact ⟨hA, hK, hH, hE, hl, hz, hlf, hle, by omega,
    le_gate hL hw (by simp [constraints, cKey, ProcBoundaryRepair.cKey, Proc.cKey,List.take,List.drop]) hl hK,
    le_gate hL hw (by simp [constraints, cEnt]) hle hE⟩

/-- An active row is not the last row. -/
theorem act_next (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (ha : cv tr tp w act = 1) : w + 1 < tr.height tp := by
  rcases Nat.lt_or_ge (w + 1) (tr.height tp) with h | h
  · exact h
  · obtain ⟨q, c1⟩ := zd hL hw (e := .mul .isLast (c act)) (by simp [constraints, cKind])
    simp only [zev_mul, zev_c, cur_cv, ha] at c1
    simp only [zev, tenv, if_pos (show w + 1 = tr.height tp by omega)] at c1
    omega

theorem act_of (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (h : cv tr tp w kK = 1 ∨ cv tr tp w kH = 1 ∨ cv tr tp w kE = 1) : cv tr tp w act = 1 := by
  have := kinds hL hw; omega

/-- Padding is a suffix. -/
theorem pad_next (hL : PLocal tr tp pub) {w : Nat} (hw : w + 1 < tr.height tp)
    (ha : cv tr tp w act = 0) : cv tr tp (w + 1) act = 0 := by
  have hw0 : w < tr.height tp := by omega
  have hA := (kinds hL hw).1
  obtain ⟨q, c1⟩ := zd hL hw0 (e := mul3 .isTransition (notE (c act)) (n act))
    (by simp [constraints, cKind])
  rpz c1 [nx hw, ha]
  simp only [zev, Mem.tenv_last_zero hw] at c1
  have := lt (tr := tr) (tp := tp) (w + 1) act
  omega

/-- **First row**: `kc = 0`, `τ = 0`, and an active first row is a key row. -/
theorem row_first (hL : PLocal tr tp pub) (h0 : 0 < tr.height tp) :
    cv tr tp 0 kc = 0 ∧ cv tr tp 0 tau = 0 ∧ (cv tr tp 0 act = 1 → cv tr tp 0 kK = 1) := by
  have hf : (tenv tr tp 0 pub).first = 1 := by simp [tenv]
  have hK := (kinds hL h0).2.1
  obtain ⟨q1, c1⟩ := zd hL h0 (e := .mul .isFirst (c kc)) (by simp [constraints, cKind])
  obtain ⟨q2, c2⟩ := zd hL h0 (e := .mul .isFirst (c tau)) (by simp [constraints, cKind])
  obtain ⟨q3, c3⟩ := zd hL h0 (e := .mul .isFirst (.mul (c act) (notE (c kK))))
    (by simp [constraints, cKind])
  rpz c1 [zev_isFirst, hf]; rpz c2 [zev_isFirst, hf]; rpz c3 [zev_isFirst, hf]
  have := lt (tr := tr) (tp := tp) 0 kc; have := lt (tr := tr) (tp := tp) 0 tau
  refine ⟨by omega, by omega, fun ha => ?_⟩
  rw [ha] at c3
  omega

/-! ## Gadgets -/

/-- **`kl = [kc = 15]`** on key rows, 0 elsewhere. -/
theorem kl_iff (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp) :
    (cv tr tp w kK = 0 → cv tr tp w kl = 0) ∧
      (cv tr tp w kK = 1 → (cv tr tp w kl = 1 ↔ cv tr tp w kc = 15)) := by
  obtain ⟨-, -, -, -, hl, -, -, -, -, hlK, -⟩ := kinds hL hw
  obtain ⟨q1, c1⟩ := zd hL hw (e := sub (c kl) (notE (.mul (sub (c kc) (k 15)) (c ikc))))
    (by simp [constraints, cKey, ProcBoundaryRepair.cKey, Proc.cKey,List.take,List.drop])
  obtain ⟨q2, c2⟩ := zd hL hw (e := .mul (sub (c kc) (k 15)) (c kl)) (by simp [constraints, cKey, ProcBoundaryRepair.cKey, Proc.cKey,List.take,List.drop])
  rpz c1 []; rpz c2 []
  have := lt (tr := tr) (tp := tp) w kc
  refine ⟨fun h => by omega, fun _ => ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
  · rw [h1] at c2; omega
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hl with h2 | h2
    · rw [h1, h2] at c1; omega
    · exact h2

/-- **Header validity.** `T = Tq`; a positive round (`zk = 0`) has `z = 0`, `K ≠ 0`, `zq = 0`;
a 0-round (`zk = 1`) has `K = 0` and `z ≡ zq + 1`. -/
theorem hdr_valid (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (hh : cv tr tp w kH = 1) :
    cv tr tp w T = cv tr tp w Tq ∧
      (cv tr tp w zk = 0 → cv tr tp w z = 0 ∧ cv tr tp w K ≠ 0 ∧ cv tr tp w zq = 0) ∧
      (cv tr tp w zk = 1 → cv tr tp w K = 0 ∧ cv tr tp w z = (cv tr tp w zq + 1) % 2013265921) := by
  obtain ⟨q0, c0⟩ := zd hL hw (e := .mul (c kH) (sub (c T) (c Tq))) (by simp [constraints, cHdr])
  obtain ⟨q1, c1⟩ := zd hL hw (e := mul3 (c kH) (notE (c zk)) (c z)) (by simp [constraints, cHdr])
  obtain ⟨q2, c2⟩ := zd hL hw (e := mul3 (c kH) (c zk) (c K)) (by simp [constraints, cHdr])
  obtain ⟨q3, c3⟩ := zd hL hw (e := mul3 (c kH) (notE (c zk)) (sub (.mul (c K) (c iK)) (k 1)))
    (by simp [constraints, cHdr])
  obtain ⟨q4, c4⟩ := zd hL hw (e := mul3 (c kH) (c zk) (sub (c z) (.add (c zq) (k 1))))
    (by simp [constraints, cHdr])
  obtain ⟨q5, c5⟩ := zd hL hw (e := mul3 (c kH) (notE (c zk)) (c zq)) (by simp [constraints, cHdr])
  rpz c0 [hh]; rpz c1 [hh]; rpz c2 [hh]; rpz c3 [hh]; rpz c4 [hh]; rpz c5 [hh]
  have := lt (tr := tr) (tp := tp) w T; have := lt (tr := tr) (tp := tp) w Tq
  have := lt (tr := tr) (tp := tp) w z; have := lt (tr := tr) (tp := tp) w zq
  have := lt (tr := tr) (tp := tp) w K
  refine ⟨by omega, fun h0 => ?_, fun h1 => ?_⟩
  · rw [h0] at c1 c3 c5
    refine ⟨by omega, fun hK => ?_, by omega⟩
    rw [hK] at c3; omega
  · rw [h1] at c2 c4
    exact ⟨by omega, by omega⟩

/-- **Header comparator**: gate `1 − zk`, operands `(Kq, K + 1)`. -/
theorem cmp_hdr (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (hh : cv tr tp w kH = 1) :
    cv tr tp w cg = 1 - cv tr tp w zk ∧ cv tr tp w cx = cv tr tp w Kq ∧
      cv tr tp w cy = (cv tr tp w K + 1) % 2013265921 := by
  obtain ⟨-, -, -, hE, -, hz, -, -, -, -, -⟩ := kinds hL hw
  have hE0 : cv tr tp w kE = 0 := by have := kinds hL hw; omega
  obtain ⟨q0, c0⟩ := zd hL hw (e := sub (c cg) (.add (.mul (c kH) (notE (c zk))) (c kE)))
    (by simp [constraints, cEnt])
  obtain ⟨q1, c1⟩ := zd hL hw (e := .mul (c kH) (sub (c cx) (c Kq))) (by simp [constraints, cEnt])
  obtain ⟨q2, c2⟩ := zd hL hw (e := .mul (c kH) (sub (c cy) (.add (c K) (k 1))))
    (by simp [constraints, cEnt])
  rpz c0 [hh, hE0]; rpz c1 [hh]; rpz c2 [hh]
  have := lt (tr := tr) (tp := tp) w cg; have := lt (tr := tr) (tp := tp) w cx
  have := lt (tr := tr) (tp := tp) w cy; have := lt (tr := tr) (tp := tp) w Kq
  have := lt (tr := tr) (tp := tp) w K
  exact ⟨by omega, by omega, by omega⟩

/-- **Entry comparator**: gate 1, operands `(next ts or T, ts + 1)`. -/
theorem cmp_ent (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (he : cv tr tp w kE = 1) :
    cv tr tp w cg = 1 ∧ cv tr tp w cy = (cv tr tp w ts + 1) % 2013265921 ∧
      (cv tr tp w le = 1 → cv tr tp w cx = cv tr tp w T) ∧
      (cv tr tp w le = 0 → cv tr tp w cx = cv tr tp (w + 1) ts) := by
  obtain ⟨-, -, -, -, -, -, -, hle, -, -, -⟩ := kinds hL hw
  have hH0 : cv tr tp w kH = 0 := by have := kinds hL hw; omega
  have hw1 := act_next hL hw (act_of hL hw (Or.inr (Or.inr he)))
  obtain ⟨q0, c0⟩ := zd hL hw (e := sub (c cg) (.add (.mul (c kH) (notE (c zk))) (c kE)))
    (by simp [constraints, cEnt])
  obtain ⟨q1, c1⟩ := zd hL hw (e := .mul (c kE) (sub (c cy) (.add (c ts) (k 1))))
    (by simp [constraints, cEnt])
  obtain ⟨q2, c2⟩ := zd hL hw
    (e := .mul (c kE) (sub (c cx) (.add (.mul (c le) (c T)) (.mul (notE (c le)) (n ts)))))
    (by simp [constraints, cEnt])
  rpz c0 [hH0, he]; rpz c1 [he]; rpz c2 [he, nx hw1]
  have := lt (tr := tr) (tp := tp) w cg; have := lt (tr := tr) (tp := tp) w cx
  have := lt (tr := tr) (tp := tp) w cy; have := lt (tr := tr) (tp := tp) w ts
  have := lt (tr := tr) (tp := tp) w T; have := lt (tr := tr) (tp := tp) (w + 1) ts
  refine ⟨by omega, by omega, fun h => ?_, fun h => ?_⟩
  · rw [h] at c2; omega
  · rw [h] at c2; omega

/-- **`zn = za·(z + 1)`** on entry rows. -/
theorem zn_def (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (he : cv tr tp w kE = 1) :
    cv tr tp w zn = (if cv tr tp w alOut = 0 then (cv tr tp w z + 1) % 2013265921 else 0) := by
  obtain ⟨-, -, hza, -⟩ := entry_row hL hw he
  have hb := bool_of hL hw (x := za) (by simp [boolCols])
  obtain ⟨q, c1⟩ := zd hL hw (e := .mul (c kE) (sub (c zn) (.mul (c za) (.add (c z) (k 1)))))
    (by simp [constraints, cEnt])
  rpz c1 [he]
  have := lt (tr := tr) (tp := tp) w zn; have := lt (tr := tr) (tp := tp) w z
  split
  · next h => rw [hza.2 h] at c1; omega
  · next h =>
    have h0 : cv tr tp w za = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with e | e
      · exact e
      · exact absurd (hza.1 e) h
    rw [h0] at c1; omega

/-! ## Key rows -/

/-- **Key register**: limb 0 is the record word, the limbs rotate. -/
theorem key_reg (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (hk : cv tr tp w kK = 1) :
    w + 1 < tr.height tp ∧
      cv tr tp w (colL 0) = (cv tr tp w sbIn + 256 * cv tr tp w sbOut) % 2013265921 ∧
      ∀ i, i < 16 → (cv tr tp w kl=0 ∨ cv tr tp (w+1) kK=0) →
        cv tr tp (w + 1) (colL i) = cv tr tp w (colL ((i + 1) % 16)) := by
  have hw1 := act_next hL hw (act_of hL hw (Or.inl hk))
  obtain ⟨q, c1⟩ := zd hL hw (e := .mul (c kK) (sub (c (colL 0)) (.add (c sbIn) (smul 256 (c sbOut)))))
    (by simp [constraints, cKey, ProcBoundaryRepair.cKey, Proc.cKey,List.take,List.drop])
  rpz c1 [hk]
  have := lt (tr := tr) (tp := tp) w (colL 0)
  refine ⟨hw1, by omega, fun i hi hb => ?_⟩
  obtain ⟨q', c2⟩ := zd hL hw (mem_rot hi)
  unfold ProcBoundaryRepair.rotation at c2
  rpz c2 [hk, nx hw1]
  rcases hb with hb | hb <;> rw [hb] at c2
  all_goals
    have := lt (tr := tr) (tp := tp) (w + 1) (colL i)
    have := lt (tr := tr) (tp := tp) w (colL ((i + 1) % 16))
    try simp only [Int.zero_mul,Int.mul_zero,Int.sub_zero,Int.one_mul] at c2
    omega

/-- **Instance initial values** on key rows. -/
theorem key_init (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (hk : cv tr tp w kK = 1) :
    cv tr tp w kq = 0 ∧ cv tr tp w Tq = T0 ∧ cv tr tp w Kq = KSENT ∧ cv tr tp w zq = 0 := by
  obtain ⟨q1, c1⟩ := zd hL hw (e := .mul (c kK) (c kq)) (by simp [constraints, cKey, ProcBoundaryRepair.cKey, Proc.cKey,List.take,List.drop])
  obtain ⟨q2, c2⟩ := zd hL hw (e := .mul (c kK) (sub (c Tq) (k T0))) (by simp [constraints, cKey, ProcBoundaryRepair.cKey, Proc.cKey,List.take,List.drop])
  obtain ⟨q3, c3⟩ := zd hL hw (e := .mul (c kK) (sub (c Kq) (k KSENT))) (by simp [constraints, cKey, ProcBoundaryRepair.cKey, Proc.cKey,List.take,List.drop])
  obtain ⟨q4, c4⟩ := zd hL hw (e := .mul (c kK) (c zq)) (by simp [constraints, cKey, ProcBoundaryRepair.cKey, Proc.cKey,List.take,List.drop])
  rpz c1 [hk]; rpz c2 [hk, T0]; rpz c3 [hk, KSENT]; rpz c4 [hk]
  have := lt (tr := tr) (tp := tp) w kq; have := lt (tr := tr) (tp := tp) w Tq
  have := lt (tr := tr) (tp := tp) w Kq; have := lt (tr := tr) (tp := tp) w zq
  refine ⟨by omega, ?_, ?_, by omega⟩
  · unfold T0; omega
  · unfold KSENT; omega

/-- **Inside a key block** (`kl = 0`): the next row is a key row with `kc + 1` and the same τ. -/
theorem key_next (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (hk : cv tr tp w kK = 1) (hl : cv tr tp w kl = 0) :
    w + 1 < tr.height tp ∧ cv tr tp (w + 1) kK = 1 ∧
      cv tr tp (w + 1) kc = (cv tr tp w kc + 1) % 2013265921 ∧
      cv tr tp (w + 1) tau = cv tr tp w tau := by
  have hw1 := act_next hL hw (act_of hL hw (Or.inl hk))
  obtain ⟨q1, c1⟩ := zd hL hw (e := .mul (sub (c kK) (c kl)) (notE (n kK)))
    (by simp [constraints, cKey, ProcBoundaryRepair.cKey, Proc.cKey,List.take,List.drop])
  obtain ⟨q2, c2⟩ := zd hL hw (e := .mul (sub (c kK) (c kl)) (sub (n kc) (.add (c kc) (k 1))))
    (by simp [constraints, cKey, ProcBoundaryRepair.cKey, Proc.cKey,List.take,List.drop])
  obtain ⟨q3, c3⟩ := zd hL hw (e := .mul (sub (c kK) (c kl)) (sub (n tau) (c tau)))
    (by simp [constraints, cKey, ProcBoundaryRepair.cKey, Proc.cKey,List.take,List.drop])
  rpz c1 [hk, hl, nx hw1]; rpz c2 [hk, hl, nx hw1]; rpz c3 [hk, hl, nx hw1]
  have := lt (tr := tr) (tp := tp) (w + 1) kK; have := lt (tr := tr) (tp := tp) (w + 1) kc
  have := lt (tr := tr) (tp := tp) w kc; have := lt (tr := tr) (tp := tp) (w + 1) tau
  have := lt (tr := tr) (tp := tp) w tau
  exact ⟨hw1, by omega, by omega, by omega⟩

/-- **A new key block** after a block end (`kl`) or a round end (`le`): `kc = 0`, `τ + 1`. -/
theorem blk_next (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (hb : cv tr tp w kl = 1 ∨ cv tr tp w le = 1) (hw1 : w + 1 < tr.height tp)
    (hk : cv tr tp (w + 1) kK = 1) :
    cv tr tp (w + 1) kc = 0 ∧ cv tr tp (w + 1) tau = (cv tr tp w tau + 1) % 2013265921 := by
  obtain ⟨-, -, -, -, hl, -, -, hle, hA, hlK, hleE⟩ := kinds hL hw
  have hA1 := (kinds hL hw).1
  have hs : cv tr tp w kl + cv tr tp w le = 1 := by omega
  obtain ⟨q1, c1⟩ := zd hL hw (e := mul3 gB (n kK) (n kc)) (by simp [constraints, cKey, ProcBoundaryRepair.cKey, Proc.cKey,List.take,List.drop])
  obtain ⟨q2, c2⟩ := zd hL hw (e := mul3 gB (n kK) (sub (n tau) (.add (c tau) (k 1))))
    (by simp [constraints, cKey, ProcBoundaryRepair.cKey, Proc.cKey,List.take,List.drop])
  rpz c1 [nx hw1, hk]; rpz c2 [nx hw1, hk]
  have e : ((cv tr tp w kl : Int) + cv tr tp w le) = 1 := by omega
  rw [e] at c1 c2
  have := lt (tr := tr) (tp := tp) (w + 1) kc; have := lt (tr := tr) (tp := tp) (w + 1) tau
  have := lt (tr := tr) (tp := tp) w tau
  exact ⟨by omega, by omega⟩

/-! ## Carries -/

/-- **Limbs** are constant over non-key rows (header / entry to a non-key row). -/
theorem limb_next (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (hk : cv tr tp w kH = 1 ∨ cv tr tp w kE = 1) (hw1 : w + 1 < tr.height tp)
    (hk1 : cv tr tp (w + 1) kK = 0) :
    ∀ i, i < 16 → cv tr tp (w + 1) (colL i) = cv tr tp w (colL i) := by
  intro i hi
  have hs : cv tr tp w kH + cv tr tp w kE = 1 := by have := kinds hL hw; omega
  obtain ⟨q, c1⟩ := zd hL hw (mem_lcarry hi)
  rpz c1 [nx hw1, hk1]
  have e : ((cv tr tp w kH : Int) + cv tr tp w kE) = 1 := by omega
  rw [e] at c1
  have := lt (tr := tr) (tp := tp) (w + 1) (colL i); have := lt (tr := tr) (tp := tp) w (colL i)
  omega

/-- **Instance carries** `kq, Tq, Kq, zq, τ` from an entry or key row to a non-key row. -/
theorem inst_next (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (hk : cv tr tp w kE = 1 ∨ cv tr tp w kK = 1) (hw1 : w + 1 < tr.height tp)
    (hk1 : cv tr tp (w + 1) kK = 0) :
    ∀ col, col ∈ instCols → cv tr tp (w + 1) col = cv tr tp w col := by
  intro col hc
  have hs : cv tr tp w kE + cv tr tp w kK = 1 := by have := kinds hL hw; omega
  obtain ⟨q, c1⟩ := zd hL hw (mem_inst hc)
  rpz c1 [nx hw1, hk1]
  have e : ((cv tr tp w kE : Int) + cv tr tp w kK) = 1 := by omega
  rw [e] at c1
  have := lt (tr := tr) (tp := tp) (w + 1) col; have := lt (tr := tr) (tp := tp) w col
  omega

/-- **Round continuation** (header, or an entry that is not last): the next row is an entry
with the round constants `K, z, zk, T, Lr, kend, τ`. -/
theorem round_next (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (hk : cv tr tp w kH = 1 ∨ (cv tr tp w kE = 1 ∧ cv tr tp w le = 0)) :
    w + 1 < tr.height tp ∧ cv tr tp (w + 1) kE = 1 ∧
      ∀ col, col ∈ roundCols → cv tr tp (w + 1) col = cv tr tp w col := by
  have K0 := kinds hL hw
  have hw1 := act_next hL hw (by omega)
  have hs : cv tr tp w kH + cv tr tp w kE - cv tr tp w le = 1 := by omega
  have e : ((cv tr tp w kH : Int) + cv tr tp w kE - cv tr tp w le) = 1 := by omega
  refine ⟨hw1, ?_, fun col hc => ?_⟩
  · obtain ⟨q, c1⟩ := zd hL hw (e := .mul gR (notE (n kE))) (by simp [constraints, cHdr])
    rpz c1 [nx hw1]
    rw [e] at c1
    have := lt (tr := tr) (tp := tp) (w + 1) kE
    omega
  · obtain ⟨q, c1⟩ := zd hL hw (mem_round hc)
    rpz c1 [nx hw1]
    rw [e] at c1
    have := lt (tr := tr) (tp := tp) (w + 1) col; have := lt (tr := tr) (tp := tp) w col
    omega

/-! ## Transitions -/

/-- **Header → entry 0**, with the next header's instance values. -/
theorem hdr_next (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (hh : cv tr tp w kH = 1) :
    w + 1 < tr.height tp ∧ cv tr tp (w + 1) kE = 1 ∧ cv tr tp (w + 1) x = 0 ∧
      cv tr tp (w + 1) Tq = (cv tr tp w T + cv tr tp w Lr) % 2013265921 ∧
      cv tr tp (w + 1) kq = cv tr tp w kend ∧ cv tr tp (w + 1) Kq = cv tr tp w K ∧
      cv tr tp (w + 1) zq = cv tr tp w z := by
  obtain ⟨hw1, hE, -⟩ := round_next hL hw (Or.inl hh)
  obtain ⟨q1, c1⟩ := zd hL hw (e := .mul (c kH) (n x)) (by simp [constraints, cHdr])
  obtain ⟨q2, c2⟩ := zd hL hw (e := .mul (c kH) (sub (n Tq) (.add (c T) (c Lr))))
    (by simp [constraints, cHdr])
  obtain ⟨q3, c3⟩ := zd hL hw (e := .mul (c kH) (sub (n kq) (c kend))) (by simp [constraints, cHdr])
  obtain ⟨q4, c4⟩ := zd hL hw (e := .mul (c kH) (sub (n Kq) (c K))) (by simp [constraints, cHdr])
  obtain ⟨q5, c5⟩ := zd hL hw (e := .mul (c kH) (sub (n zq) (c z))) (by simp [constraints, cHdr])
  rpz c1 [hh, nx hw1]; rpz c2 [hh, nx hw1]; rpz c3 [hh, nx hw1]; rpz c4 [hh, nx hw1]
  rpz c5 [hh, nx hw1]
  have := lt (tr := tr) (tp := tp) (w + 1) x; have := lt (tr := tr) (tp := tp) (w + 1) Tq
  have := lt (tr := tr) (tp := tp) (w + 1) kq; have := lt (tr := tr) (tp := tp) (w + 1) Kq
  have := lt (tr := tr) (tp := tp) (w + 1) zq; have := lt (tr := tr) (tp := tp) w kend
  have := lt (tr := tr) (tp := tp) w K; have := lt (tr := tr) (tp := tp) w z
  exact ⟨hw1, hE, by omega, by omega, by omega, by omega, by omega⟩

/-- **Entry → entry** (not last): `x + 1`. -/
theorem ent_next (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (he : cv tr tp w kE = 1) (hl : cv tr tp w le = 0) :
    w + 1 < tr.height tp ∧ cv tr tp (w + 1) x = (cv tr tp w x + 1) % 2013265921 := by
  obtain ⟨hw1, -, -⟩ := round_next hL hw (Or.inr ⟨he, hl⟩)
  obtain ⟨q, c1⟩ := zd hL hw (e := mul3 (c kE) (notE (c le)) (sub (n x) (.add (c x) (k 1))))
    (by simp [constraints, cEnt])
  rpz c1 [he, hl, nx hw1]
  have := lt (tr := tr) (tp := tp) (w + 1) x; have := lt (tr := tr) (tp := tp) w x
  exact ⟨hw1, by omega⟩

/-- **The last entry** of a round: `x + 1 ≡ Lr`. -/
theorem le_entry (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (hl : cv tr tp w le = 1) :
    cv tr tp w kE = 1 ∧ (cv tr tp w x + 1) % 2013265921 = cv tr tp w Lr := by
  obtain ⟨-, -, -, hE, -, -, -, -, -, -, hleE⟩ := kinds hL hw
  obtain ⟨q, c1⟩ := zd hL hw (e := .mul (c le) (sub (.add (c x) (k 1)) (c Lr)))
    (by simp [constraints, cEnt])
  rpz c1 [hl]
  have := lt (tr := tr) (tp := tp) w x; have := lt (tr := tr) (tp := tp) w Lr
  exact ⟨by omega, by omega⟩

/-- Headers follow a block end or a round end. -/
theorem prev_hdr (hL : PLocal tr tp pub) {w : Nat} (hw1 : w + 1 < tr.height tp)
    (hh : cv tr tp (w + 1) kH = 1) : cv tr tp w kl = 1 ∨ cv tr tp w le = 1 := by
  have hw : w < tr.height tp := by omega
  obtain ⟨-, hK, -, hE, hl, -, -, hle, hA, hlK, hleE⟩ := kinds hL hw
  have := (kinds hL hw).1
  obtain ⟨q, c1⟩ := zd hL hw (e := .mul (n kH) (notE gB)) (by simp [constraints, cHdr])
  rpz c1 [nx hw1, hh]
  omega

/-- Entries follow a header or a non-last entry. -/
theorem prev_ent (hL : PLocal tr tp pub) {w : Nat} (hw1 : w + 1 < tr.height tp)
    (he : cv tr tp (w + 1) kE = 1) :
    cv tr tp w kH = 1 ∨ (cv tr tp w kE = 1 ∧ cv tr tp w le = 0) := by
  have hw : w < tr.height tp := by omega
  obtain ⟨hA, hK, hH, hE, -, -, -, hle, hs, -, hleE⟩ := kinds hL hw
  obtain ⟨q, c1⟩ := zd hL hw (e := .mul (n kE) (notE gR)) (by simp [constraints, cHdr])
  rpz c1 [nx hw1, he]
  omega

/-- **One step of τ**: from an active row, τ stays or (at a new key block) becomes `τ + 1`. -/
theorem tau_step (hL : PLocal tr tp pub) {w : Nat} (hw : w < tr.height tp)
    (ha : cv tr tp w act = 1) (hw1 : w + 1 < tr.height tp) (ha1 : cv tr tp (w + 1) act = 1) :
    cv tr tp (w + 1) tau = cv tr tp w tau ∨
      cv tr tp (w + 1) tau = (cv tr tp w tau + 1) % 2013265921 := by
  have K0 := kinds hL hw
  have K1 := kinds hL hw1
  have tauR : tau ∈ roundCols := by simp [roundCols]
  have tauI : tau ∈ instCols := by simp [instCols]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K1.2.1 with k1 | k1
  · -- the next row is not a key row
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.2.1 with h0 | h0
    · exact Or.inl (inst_next hL hw (by omega) hw1 k1 tau tauI)
    · exact Or.inl ((round_next hL hw (Or.inl h0)).2.2 tau tauR)
  · -- the next row is a key row
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.1 with h0 | h0
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.2.1 with h1 | h1
      · have hE : cv tr tp w kE = 1 := by omega
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.2.2.2.2.2.2.1 with hl | hl
        · have := (round_next hL hw (Or.inr ⟨hE, hl⟩)).2.1; omega
        · exact Or.inr (blk_next hL hw (Or.inr hl) hw1 k1).2
      · have := (round_next hL hw (Or.inl h1)).2.1; omega
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K0.2.2.2.2.1 with hl | hl
      · exact Or.inl (key_next hL hw h0 hl).2.2.2
      · exact Or.inr (blk_next hL hw (Or.inl hl) hw1 k1).2

/-- **`τ ≤ w`** on an active row `w`. -/
theorem tau_le (hL : PLocal tr tp pub) :
    ∀ w, w < tr.height tp → cv tr tp w act = 1 → cv tr tp w tau ≤ w := by
  intro w
  induction w with
  | zero => intro h0 _; rw [(row_first hL h0).2.1]; exact Nat.le_refl _
  | succ w ih =>
    intro hw1 ha1
    have hw : w < tr.height tp := by omega
    have ha : cv tr tp w act = 1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (kinds hL hw).1 with h | h
      · have := pad_next hL hw1 h; omega
      · exact h
    have := ih hw ha
    rcases tau_step hL hw ha hw1 ha1 with h | h <;> rw [h]
    · omega
    · exact Nat.le_trans (Nat.mod_le _ _) (by omega)

end

end ZkFormal.NearV3.Candidates.ProcSound
