import ZkFormal.Chacha.Shuffle.Complete.Bus

/-!
# ZkFormal.Chacha.Shuffle.Complete.Traffic — the bus traffic of the honest `shufV3` trace

Per row, each of the 8 interactions contributes the list `t* X` (its message, with its
multiplicity) of the row descriptor `X` (`rep_*`).  Summed over the table (`count_rows`):

* `busIn` receives `expectedIn` (per instance, `[lid, q, l[q]]` for `q < L`);
* `busMem` sends the writes and receives the reads (`memSends`, `memRecvs`, a permutation of
  each other: `memBal`);
* `busOut` sends `expectedOut` (per instance, `[lid, q, l'[q]]`, `l' = fyLoop js (L−1) l`);
* `busGen` receives `expectedGen` (per step `q = 1 … L−1`,
  `genMsg key (kBefore q) (q+1) (js q) (kBefore (q−1))`);
* `busShuf` sends `expectedShuf` (per instance `[lid] ++ key limbs ++ [kstart, L, kBefore 0]`).
-/

namespace ZkFormal.Chacha.Shuffle.Complete

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Shuffle.Table
open ZkFormal.Chacha.Shuffle.Gen NearSpecV3

/-! ## Expected messages -/

def keyN (key : List Nat) : List Fp :=
  (List.range 16).map (fun q => Fp.ofNat ((key.getD (q / 2) 0 / 2 ^ (16 * (q % 2))) % 65536))

def inMsg (I : SInst) (q : Nat) : List Fp := [Fp.ofNat I.lid, Fp.ofNat q, Fp.ofNat (I.vals.getD q 0)]
def outMsg (I : SInst) (q : Nat) : List Fp := [Fp.ofNat I.lid, Fp.ofNat q, Fp.ofNat (I.final.getD q 0)]
def genStep (I : SInst) (q : Nat) : List Fp :=
  Rng.genMsg I.key (I.kBefore q) (q + 1) (I.js q) (I.kBefore (q - 1))
def shufMsg (I : SInst) : List Fp :=
  [Fp.ofNat I.lid] ++ keyN I.key ++ [Fp.ofNat I.kstart, Fp.ofNat I.L, Fp.ofNat (I.kBefore 0)]

def expectedIn (insts : List SInst) : List (List Fp) :=
  insts.flatMap fun I => (List.range I.L).map (inMsg I)
def expectedOut (insts : List SInst) : List (List Fp) :=
  insts.flatMap fun I => (List.range I.L).map (outMsg I)
def expectedGen (insts : List SInst) : List (List Fp) :=
  insts.flatMap fun I => (List.range (I.L - 1)).map fun i => genStep I (i + 1)
def expectedShuf (insts : List SInst) : List (List Fp) := insts.map shufMsg

def memSends (insts : List SInst) : List (List Fp) :=
  ((honestRows insts).flatMap rowSendN).map (List.map Fp.ofNat)
def memRecvs (insts : List SInst) : List (List Fp) :=
  ((honestRows insts).flatMap rowRecvN).map (List.map Fp.ofNat)

/-! ## Per-row interaction traffic -/

def tIn : Row → List (List Fp)
  | .pos I _ q => [inMsg I q]
  | .pad => []
def tMinit : Row → List (List Fp)
  | .pos I s q => [[s, q, I.L, I.vals.getD q 0].map Fp.ofNat]
  | .pad => []
def tMR1 : Row → List (List Fp)
  | .pos I s q => [[s, q, I.lw q q, (I.arr q).getD q 0].map Fp.ofNat]
  | .pad => []
def tMR2 : Row → List (List Fp)
  | .pos I s q => if I.isS2 q then [[s, I.js q, I.lw q (I.js q), (I.arr q).getD (I.js q) 0].map Fp.ofNat] else []
  | .pad => []
def tMW2 : Row → List (List Fp)
  | .pos I s q => if I.isS2 q then [[s, I.js q, q, (I.arr q).getD q 0].map Fp.ofNat] else []
  | .pad => []
def tOut : Row → List (List Fp)
  | .pos I _ q => [outMsg I q]
  | .pad => []
def tGen : Row → List (List Fp)
  | .pos I _ q => if 1 ≤ q then [genStep I q] else []
  | .pad => []
def tShuf : Row → List (List Fp)
  | .pos I _ q => if q = 0 then [shufMsg I] else []
  | .pad => []

theorem rowCell_pos (I : SInst) (s q r c : Nat) : rowCell (.pos I s q) r c = I.cell s r q c := rfl

theorem multNat_one {tr : Trace Fp} {t r : Nat} {pub : List Fp} {i : Interaction} {b : Expr}
    (hi : i.mult = [b]) {v : Nat} (h : b.eval tr t r pub = Fp.ofNat v) (hv : v ≤ 1) :
    i.multNat tr t r pub = v := by
  unfold Interaction.multNat
  rw [hi]
  simp only [Interaction.multNat.go]
  rw [h]
  rcases (show v = 0 ∨ v = 1 by omega) with e | e <;> subst e <;> decide

theorem eval_nat {tr : Trace Fp} {t r : Nat} {pub : List Fp} {e : Expr} {v : Nat}
    (h : zev (tenv tr t r pub) e = (v : Int)) : e.eval tr t r pub = Fp.ofNat v := by
  rw [eval_eq, h, intCast_ofNat]

/-- The value sent on `busOut` by row `q` is the final list's entry. -/
theorem out_val {I : SInst} (hI : InstOk I) {q : Nat} (hq : q < I.L) :
    (if I.isS2 q then (I.arr q).getD (I.js q) 0 else (I.arr q).getD q 0) = I.final.getD q 0 := by
  have hl : I.L - 1 < I.vals.length := by have : I.L = I.vals.length := rfl; have := hI.L_pos; omega
  unfold SInst.final SInst.arr
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : 1 ≤ q
  · rw [fyLoop_get I.js (I.L - 1) I.vals hl (hjs hI) h1 (by omega)]
    by_cases hS : I.isS2 q = true
    · rw [iteT hS]
    · rw [iteF hS]
      have := js_le hI h1 hq
      have : ¬ (1 ≤ q ∧ I.js q < q) := fun h' => hS ((isS2_iff I q).mpr h')
      rw [show I.js q = q by omega]
  · have hq0 : q = 0 := by omega
    subst hq0
    have hS : ¬ I.isS2 0 = true := fun h => by have := ((isS2_iff I 0).mp h).1; omega
    rw [iteF hS, fyLoop_eq_fyBefore]

section
variable (insts : List SInst) (hok : ∀ I ∈ insts, InstOk I)
  (hrows : (honestRows insts).length ≤ 2 ^ maxLog) (t r : Nat) (pub : List Fp)
  (hr : r < (honestTrace insts).height t)

open ZkFormal.Chacha.Table.E

theorem ceval (x : Nat) :
    (c x).eval (honestTrace insts) t r pub = Fp.ofNat (rowCell (rowAt insts r) r x) := rfl

/-- The multiplicity of a column interaction. -/
theorem rep_col {x : Nat} (hx : x ∈ boolCols) (bus : Nat) (msg : List Expr) (send : Bool) :
    Interaction.multNat ⟨bus, [c x], msg, send⟩ (honestTrace insts) t r pub = rowCell (rowAt insts r) r x :=
  multNat_one rfl (ceval insts t r pub x) (rowCell_bool _ r hx)

include hok hrows hr

theorem rep_gStep (bus : Nat) (msg : List Expr) (send : Bool) :
    Interaction.multNat ⟨bus, [gStep], msg, send⟩ (honestTrace insts) t r pub =
      match rowAt insts r with
      | .pos _ _ q => if 1 ≤ q then 1 else 0
      | .pad => 0 := by
  have h := honest_env insts hok hrows t r pub hr
  have hz : zev (tenv (honestTrace insts) t r pub) gStep =
      (rowCell (rowAt insts r) r colA : Int) - rowCell (rowAt insts r) r colFin := by
    rw [gStep, zev_sub, zev_c, zev_c, h.cur, h.cur]
  generalize hX : rowAt insts r = X at hz
  cases X with
  | pad => show _ = 0; exact multNat_one rfl (eval_nat (v := 0) (by rw [hz]; rfl)) (by omega)
  | pos I s q =>
    show _ = if 1 ≤ q then 1 else 0
    apply multNat_one rfl (eval_nat (v := if 1 ≤ q then 1 else 0) ?_) (by split <;> omega)
    rw [hz]
    show ((I.cell s r q colA : Nat) : Int) - (I.cell s r q colFin : Nat) = _
    rw [c_a, c_fin]
    by_cases e : q = 0
    · rw [iteT e, iteF (by omega)]; rfl
    · rw [iteF e, iteT (by omega)]; rfl

/-- **One row's traffic**, interaction by interaction. -/
theorem rowTraffic_eq (B : Buses) (b : Nat) (s : Bool) :
    rowTraffic B.is (honestTrace insts) t r pub b s =
      (if B.bin = b ∧ false = s then tIn (rowAt insts r) else []) ++
      (if B.mem = b ∧ true = s then tMinit (rowAt insts r) else []) ++
      (if B.mem = b ∧ false = s then tMR1 (rowAt insts r) else []) ++
      (if B.mem = b ∧ false = s then tMR2 (rowAt insts r) else []) ++
      (if B.mem = b ∧ true = s then tMW2 (rowAt insts r) else []) ++
      (if B.bout = b ∧ true = s then tOut (rowAt insts r) else []) ++
      (if B.gen = b ∧ false = s then tGen (rowAt insts r) else []) ++
      (if B.shuf = b ∧ true = s then tShuf (rowAt insts r) else []) := by
  have h := honest_env insts hok hrows t r pub hr
  have mA : colA ∈ boolCols := by decide
  have mS : colS2 ∈ boolCols := by decide
  have mF : colFin ∈ boolCols := by decide
  unfold rowTraffic
  simp only [Buses.is, interactions, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [rep_col insts t r pub mA, rep_col insts t r pub mA, rep_col insts t r pub mA,
    rep_col insts t r pub mS, rep_col insts t r pub mS, rep_col insts t r pub mA,
    rep_gStep insts hok hrows t r pub hr, rep_col insts t r pub mF]
  simp only [Interaction.msgVal, List.map_cons, List.map_nil, List.map_append]
  have hcv : ∀ x, (c x).eval (honestTrace insts) t r pub = Fp.ofNat (rowCell (rowAt insts r) r x) :=
    ceval insts t r pub
  generalize hX : rowAt insts r = X at h hcv
  cases X with
  | pad =>
    have z : ∀ x, x ≠ colRc → rowCell Row.pad r x = 0 := fun x hx => by
      show (if x = colRc then r else 0) = 0; rw [iteF hx]
    simp only [z colA (by decide), z colS2 (by decide), z colFin (by decide), List.replicate_zero]
    simp [tIn, tMinit, tMR1, tMR2, tMW2, tOut, tGen, tShuf]
  | pos I s q =>
    have hv := valid_rowAt insts hok r
    rw [hX] at hv
    obtain ⟨hI, hq, hrs⟩ := hv
    have hc : ∀ x, (c x).eval (honestTrace insts) t r pub = Fp.ofNat (I.cell s r q x) := hcv
    have hcur : ∀ x, (tenv (honestTrace insts) t r pub).cur x = I.cell s r q x := h.cur
    have hkey : keyMsg.map (fun e => e.eval (honestTrace insts) t r pub) = keyN I.key := by
      unfold keyMsg keyN
      rw [List.map_map]
      apply List.map_congr_left
      intro x hx
      have hx' := List.mem_range.mp hx
      show (c (colK (x / 2) (x % 2))).eval (honestTrace insts) t r pub = _
      rw [hc, c_K I s r q (by omega) (Nat.mod_lt _ (by decide))]
    have hout : outE.eval (honestTrace insts) t r pub = Fp.ofNat (I.final.getD q 0) := by
      apply eval_nat
      rw [← out_val hI hq]
      simp only [outE, zev_add, zev_mul, zev_sub, zev_c, zev_k, hcur, c_eq, c_c, c_o]
      by_cases hS : I.isS2 q = true
      · simp [hS]
      · simp [hS]
    have hq1 : (Expr.add (c colQ) (k 1)).eval (honestTrace insts) t r pub = Fp.ofNat (q + 1) := by
      apply eval_nat; simp only [zev_add, zev_c, zev_k, hcur, c_q]; push_cast; rfl
    simp only [hc, hkey, hout, hq1]
    simp only [rowCell_pos, c_a, c_s2, c_fin, c_lid, c_q, c_v0, c_inst, c_L, c_t1, c_c, c_j, c_t2, c_o, c_kq, c_kn,
      c_ks]
    by_cases hS : I.isS2 q = true
    · obtain ⟨h1, -⟩ := (isS2_iff I q).mp hS
      simp only [hS, iteT h1, iteF (show ¬ q = 0 by omega), ite_true, List.replicate_one,
        List.replicate_zero, tIn, tMinit, tMR1, tMR2, tMW2, tOut, tGen, tShuf, inMsg, outMsg, genStep,
        Rng.genMsg, keyN, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]
    · have hS' : I.isS2 q = false := by simpa using hS
      by_cases h1 : 1 ≤ q
      · simp only [hS', iteT h1, iteF (show ¬ q = 0 by omega), Bool.false_eq_true, ite_false,
          List.replicate_one, List.replicate_zero, tIn, tMinit, tMR1, tMR2, tMW2, tOut, tGen, tShuf,
          inMsg, outMsg, genStep, Rng.genMsg, keyN, List.map_cons, List.map_nil, List.cons_append,
          List.nil_append, List.append_assoc]
      · have hq0 : q = 0 := by omega
        subst hq0
        simp only [hS', iteF h1, Bool.false_eq_true, ite_true, ite_false,
          List.replicate_one, List.replicate_zero, tIn, tMinit, tMR1, tMR2, tMW2, tOut, tGen, tShuf,
          inMsg, outMsg, shufMsg, keyN, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_assoc]

end

end ZkFormal.Chacha.Shuffle.Complete
