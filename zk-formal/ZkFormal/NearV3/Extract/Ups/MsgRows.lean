import ZkFormal.NearV3.Extract.Ups.FieldRows

/-!
# ZkFormal.NearV3.Extract.Ups.MsgRows — the messages of a node-part row

A node-part row (`qb = 1`) sends its byte on `BYTES (msgId 12 (512τ + j), qpos, b)`, reads
`UPB (NPOST(sN), spos, rb, plen, pdep, rcid, ·)` when `rd`, looks up `DIGEST (dI, dL, reg)` when
`gD`, and sends / receives `MEMD` when `gMs` / `gMr`; nothing else.  Values are canonical
cells; the ids and `u + 1` are reduced mod `P`.
-/

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- The `UPB` message of a read row, with use count `uu`. -/
def upbN (C : URow) (uu : Nat) : Msg := [(K_NPOST + 16 * C sN) % P, C spos, C rb, C plen, C pdep, C rcid, uu]

/-- The `BYTES` id of part `j` of instance `τ`. -/
def upsIdN (τ jj : Nat) : Nat := (K_VUPS + 16 * (512 * τ + jj)) % P

theorem ofNat0_ne1 : (Fp.ofNat 0 = 1) = False := by decide

theorem ofNat00_ne1 : (Fp.ofNat 0 + Fp.ofNat 0 = 1) = False := by decide

theorem ofNat01_eq1 : Fp.ofNat 0 + Fp.ofNat 1 = 1 := by decide

theorem rep_if (p : Prop) [Decidable p] (m : Msg) : List.replicate (if p then 1 else 0) m = if p then [m] else [] := by
  split <;> rfl

theorem toNat_id (a b' : Nat) :
    (((K_VUPS : Nat) : Fp) + ((16 : Nat) : Fp) * (((512 : Nat) : Fp) * Fp.ofNat a + Fp.ofNat b')).toNat =
      upsIdN a b' := by
  unfold upsIdN
  rw [natCast_eq, natCast_eq, natCast_eq, ofNat_mul', ofNat_add', ofNat_mul', ofNat_add', Fp.toNat_ofNat]

theorem toNat_npost (a : Nat) :
    (((K_NPOST : Nat) : Fp) + ((16 : Nat) : Fp) * Fp.ofNat a).toNat = (K_NPOST + 16 * a) % P := by
  rw [natCast_eq, natCast_eq, ofNat_mul', ofNat_add', Fp.toNat_ofNat]

theorem toNat_succ1 (a : Nat) : (Fp.ofNat a + ((1 : Nat) : Fp)).toNat = (a + 1) % P := by
  rw [natCast_eq, ofNat_add', Fp.toNat_ofNat]

theorem ofNat_one_iff' {v : Nat} (h : v = 0 ∨ v = 1) : Fp.ofNat v = 1 ↔ v = 1 := by
  rcases h with rfl | rfl <;> decide

section
variable {C D : URow} (ok : URowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

theorem tn (x : Nat) : (Fp.ofNat (C x)).toNat = C x := by
  rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (hC x)]

/-- **The messages of a node-part row.** -/
theorem msgsQ (hq : C qb = 1) (bb : Nat) (sd : Bool) :
    uMsgs C D bb sd =
      (if B_DIGEST = bb ∧ false = sd then
        (if C gD = 1 then [[C dI, C dL] ++ (List.range 32).map (fun i => C (reg i))] else []) else []) ++
      (if B_BYTES = bb ∧ true = sd then [[upsIdN (C tau) (C j), C qpos, C b]] else []) ++
      (if B_UPB = bb ∧ false = sd then (if C rd = 1 then [upbN C (C u)] else []) else []) ++
      (if B_UPB = bb ∧ true = sd then (if C rd = 1 then [upbN C ((C u + 1) % P)] else []) else []) ++
      (if B_MEMD = bb ∧ true = sd then
        (if C gMs = 1 then [[C tau, C j, C idx, C rx, C rb, C qlen]] else []) else []) ++
      (if B_MEMD = bb ∧ false = sd then
        (if C gMr = 1 then [[C tau, C jm, C idx, C mBv, C mCv, C clen]] else []) else []) := by
  obtain ⟨-, hact, hwk, bsf, bw1, bw2, bw3, bvb, bqb, -⟩ := kinds ok hC hD
  have b := fun {x} (hx : x ∈ rowBools) => rowBool ok hC hx
  have bmS := b (x := mS) (by simp [rowBools])
  have bmK := b (x := mK) (by simp [rowBools])
  have bmB := b (x := mB) (by simp [rowBools])
  have bgD := b (x := gD) (by simp [rowBools])
  have brd := b (x := rd) (by simp [rowBools])
  have bgMs := b (x := gMs) (by simp [rowBools])
  have bgMr := b (x := gMr) (by simp [rowBools])
  have hm := fact ok (e := .mul (sub (.add (c mS) (.add (c mK) (c mB))) (k 0)) (not (c wk)))
    (by simp [UpsV3.constraints, UpsV3.cWalk])
  have hk := kinds ok hC hD
  have hact1 := hk.1
  -- a node-part row is not a walk or value row
  have hwk0 : C wk = 0 := by
    rcases hk.1 with h | h <;> rcases hk.2.2.2.2.2.2.2.2.2.1 with h' | h' <;> omega
  have hvb0 : C vb = 0 := by
    rcases hk.1 with h | h <;> rcases hk.2.2.2.2.2.2.2.2.2.1 with h' | h' <;> omega
  have z1 : C sf = 0 := by omega
  have z3 : C wt3 = 0 := by omega
  uev_simp
  simp only [cast_ofNat] at hm
  rw [hwk0] at hm
  simp only [cast0, cast1] at hm
  have zm : C mS = 0 ∧ C mK = 0 ∧ C mB = 0 := by
    have := le1 bmS; have := le1 bmK; have := le1 bmB
    have : ((C mS + C mK + C mB : Nat) : Fp) = ((0 : Nat) : Fp) := by
      rw [natCast_add, natCast_add, cast0]; grind
    have := natv (by have := P_gt; omega) (by have := P_gt; omega) this
    omega
  have one : ¬ ((0 : Fp) = 1) := by decide
  have h01 : ¬ ((0 : Fp) + 0 = 1) := by decide
  have hvq : Fp.ofNat (C vb) + Fp.ofNat (C qb) = 1 := by rw [hvb0, hq]; decide
  simp only [uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv, List.flatMap_cons, List.flatMap_nil, uMult, uev,
    Expr.evalWith, uEnv, if_false, Bool.false_eq_true, Dsl.c, Dsl.k, z1, z3, hvb0, hq, zm.1, zm.2.1, zm.2.2,
    ofNat_one_iff' bgD, ofNat_one_iff' brd, ofNat_one_iff' bgMs, ofNat_one_iff' bgMr, ofNat0_ne1, ofNat00_ne1, ofNat01_eq1, List.replicate_one,
    if_true, rep_if, ite_self, List.replicate_zero, List.nil_append, List.append_nil, regs, upbMsg, upsId, mid,
    Dsl.smul, List.map_cons, List.map_nil, List.map_append, List.map_map, Function.comp_def, tn ok hC hD,
    toNat_id, toNat_npost, toNat_succ1, List.cons_append, List.singleton_append, upbN, List.append_assoc]

/-- **The messages of a value row**: `SPOST (τ, pos, b)` in, `BYTES (msgId 12 (512τ + j), pos, b)` out. -/
theorem msgsV (hv : C vb = 1) (bb : Nat) (sd : Bool) :
    uMsgs C D bb sd =
      (if B_SPOST = bb ∧ false = sd then [[C tau, C qpos, C b]] else []) ++
      (if B_BYTES = bb ∧ true = sd then [[upsIdN (C tau) (C j), C qpos, C b]] else []) := by
  obtain ⟨-, hact, hwk, bsf, bw1, bw2, bw3, bvb, bqb, -⟩ := kinds ok hC hD
  have hk := kinds ok hC hD
  have b' := fun {x} (hx : x ∈ rowBools) => rowBool ok hC hx
  have bmS := b' (x := mS) (by simp [rowBools])
  have bmK := b' (x := mK) (by simp [rowBools])
  have bmB := b' (x := mB) (by simp [rowBools])
  have hwk0 : C wk = 0 := by
    rcases hk.1 with h | h <;> rcases hk.2.2.2.2.2.2.2.2.2.1 with h' | h' <;> omega
  have hqb0 : C qb = 0 := by
    rcases hk.1 with h | h <;> rcases hk.2.2.2.2.2.2.2.2.2.1 with h' | h' <;> omega
  have z1 : C sf = 0 := by omega
  have z3 : C wt3 = 0 := by omega
  have hm := fact ok (e := .mul (sub (.add (c mS) (.add (c mK) (c mB))) (k 0)) (not (c wk)))
    (by simp [UpsV3.constraints, UpsV3.cWalk])
  have hr := fact ok (e := .mul (not (c qb)) (c rd)) (by simp [UpsV3.constraints, UpsV3.cBytes])
  have hg := fact ok (e := sub (c gD) (.add (mul3 (c qb) (c fs) winFr) (c wt3)))
    (by simp [UpsV3.constraints, UpsV3.cDigest])
  have hgs := fact ok (e := sub (c gMs) (mul3 (c sMEM) (not (c rootP)) (not (c kNLF))))
    (by simp [UpsV3.constraints, UpsV3.cMem])
  have hgr := fact ok (e := sub (c gMr) (.mul (c sMEM) (c bN))) (by simp [UpsV3.constraints, UpsV3.cMem])
  have hS := stSum ok hC
  have bMEM := le1 (stBool ok hC (x := sMEM) (by simp [states]))
  have zMEM : C sMEM = 0 := by rw [hqb0] at hS; omega
  uev_simp
  simp only [cast_ofNat] at *
  rw [hwk0] at hm; rw [hqb0] at hr hg; rw [z3] at hg; rw [zMEM] at hgs hgr
  simp only [cast0, cast1] at hm hr hg hgs hgr
  have zm : C mS = 0 ∧ C mK = 0 ∧ C mB = 0 := by
    have := le1 bmS; have := le1 bmK; have := le1 bmB
    have : ((C mS + C mK + C mB : Nat) : Fp) = ((0 : Nat) : Fp) := by
      rw [natCast_add, natCast_add, cast0]; grind
    have := natv (by have := P_gt; omega) (by have := P_gt; omega) this
    omega
  have zrd : C rd = 0 := natv (hC _) (by have := P_gt; omega) (by grind)
  have zgD : C gD = 0 := natv (hC _) (by have := P_gt; omega) (by grind)
  have zgs : C gMs = 0 := natv (hC _) (by have := P_gt; omega) (by grind)
  have zgr : C gMr = 0 := natv (hC _) (by have := P_gt; omega) (by grind)
  have ofNat10 : Fp.ofNat 1 + Fp.ofNat 0 = 1 := by decide
  simp only [uMsgs, UpsV3.interactions, Dsl.send, Dsl.recv, List.flatMap_cons, List.flatMap_nil, uMult, uev,
    Expr.evalWith, uEnv, if_false, Bool.false_eq_true, Dsl.c, Dsl.k, z1, z3, hv, hqb0, zm.1, zm.2.1, zm.2.2,
    zrd, zgD, zgs, zgr, ofNat0_ne1, ofNat00_ne1, ofNat10, List.replicate_one,
    if_true, rep_if, ite_self, List.replicate_zero, List.nil_append, List.append_nil, regs, upbMsg, upsId, mid,
    Dsl.smul, List.map_cons, List.map_nil, List.map_append, List.map_map, Function.comp_def, tn ok hC hD,
    toNat_id, List.cons_append, List.singleton_append, List.append_assoc, Lexpr]
  simp [show (Fp.ofNat 1 = 1) from rfl]

end

end ZkFormal.NearV3.UpsRows
