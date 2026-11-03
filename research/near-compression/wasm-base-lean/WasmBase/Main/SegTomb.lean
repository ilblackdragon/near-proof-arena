import WasmBase.Main.SegRowRel
import WasmBase.Main.SegSoundX

/-!
# WasmBase.Main.SegTomb — returned activations are dead at the cut (E2E M4c, CORE)

Discharges `TombDead tr pub (finS tr pub)` (`Main/SegLink.lean`), a named premise of `seg_sound`:
every taken `RET` row's activation id `c` is `< 2^28`, is not `0`, and no message of the out-boundary
block `finS` is a call record (space 4) of slot `c`.

## The argument (a count on the CH bus)

Let `p x := x.space = 4 ∧ x.slot = c`.  The CH balance `seg_hch` is
`initS ++ prods ~ finS ++ conss`, so `#p(initS ++ prods) = #p(finS) + #p(conss)`.

* `#p(conss) ≥ 1`: the taken `RET` row consumes its activation's record `[4, c, …]`.
* `#p(initS ++ prods) ≤ 1`: the list is duplicate-free (`exec_rows_rel`, the channel's `nodup`), and
  all its `p`-members are equal:
  - a space-4 message of `initS` is a record of the in-boundary's caller chain (`h0`: `RelW.live`,
    `CallsOK.chain`; `chain_rec4`): one record per slot, slots in `1 … t_in`;
  - an action row produces a space-4 message only if it is a `CALL` row, and then it is its single
    record send, of slot = the row's time `> t_in` (`instr_send4`, `host_send_no4`; the locals spaces
    `16 + ts`, `16 + cid` do not wrap to 4 because the row's `cid < 2^28`, `RelW.cidLt` at the row,
    from `exec_rows_rel`);
  - distinct rows have distinct times (`exec_rows_rel`).

So `#p(finS) = 0`.  The bounds: `c < 2^28` is `RelW.cidLt` at the `RET` row (`exec_rows_rel`);
`c ≠ 0` is RET's constraint `act · (cid · invc − 1)`.

No new premise: `seg_tombDead` uses only what `seg_sound` already assumes (`HoldsX`, the row facts,
`HostBLinked`/`RegCLinked` for `seg_hch`, `initS` Nodup, the size bounds and `h0`).
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. The call records of a caller chain -/

/-- A space-4 message of a caller chain is a call record whose slot is an activation id of the chain
(`0 < slot ≤ cid`), and it is the only chain message of that slot. -/
theorem chain_rec4 {X : Ctx} {t : Nat} : ∀ {cid sb k : Nat} {rest : List Frame} {sv : List Saved} {x : Msg},
    Chain X t cid sb k rest sv → chainMsgs X cid k rest sv x → x.space = 4 →
    0 < x.slot ∧ x.slot ≤ cid ∧ ∀ y, chainMsgs X cid k rest sv y → y.space = 4 → y.slot = x.slot → y = x
  | _, _, _, [], [], _, _, h, _ => by simp [chainMsgs] at h
  | cid, _, _, fc :: rest, c :: sv, x, hc, h, h4 => by
    obtain ⟨-, -, -, -, hlt, -, -, -, -, -, -, -, hc'⟩ := hc
    have loc : ∀ y, y ∈ localView (16 + c.cid) fc.locals c.tpl → y.space ≠ 4 := by
      intro y hy; obtain ⟨j, -, rfl⟩ := mem_localView.mp hy; rw [enc_space]; omega
    rcases h with rfl | h | h
    · refine ⟨by simp only [callMsg]; omega, by simp only [callMsg]; omega, fun y hy hy4 hys => ?_⟩
      rcases hy with rfl | hy | hy
      · rfl
      · exact absurd hy4 (loc y hy)
      · have := (chain_rec4 hc' hy hy4).2.1
        simp only [callMsg] at hys; omega
    · exact absurd h4 (loc x h)
    · obtain ⟨a, b, u⟩ := chain_rec4 hc' h h4
      refine ⟨a, by omega, fun y hy hy4 hys => ?_⟩
      rcases hy with rfl | hy | hy
      · simp only [callMsg] at hys; omega
      · exact absurd hy4 (loc y hy)
      · exact u y hy hy4 hys
  | _, _, _, [], _ :: _, _, h, _, _ => h.elim
  | _, _, _, _ :: _, [], _, h, _, _ => h.elim

/-- **The in-boundary's call records**: a space-4 message of a live set related at `t0 + 1` is a
call record of slot in `1 … t0`, slot `< 2^28`, and the only live space-4 message of that slot. -/
theorem bnd_rec4 {X : Ctx} {sg : Nat → Nat × Nat} {s0 : St} {t0 S0 : Nat} {m0 : List F} {init : List Msg}
    (h0 : Bnd X sg s0 t0 S0 m0 init) :
    ∀ x ∈ init, x.space = 4 → 0 < x.slot ∧ x.slot ≤ t0 ∧ x.slot < 2 ^ 28 ∧
      ∀ y ∈ init, y.space = 4 → y.slot = x.slot → y = x := by
  obtain ⟨k, pc, sb, cid, -, E, f, tps, tpl, -, -, -, R⟩ := h0
  obtain ⟨sv, hc, -, hout, -⟩ := R.calls.chain
  have hlt := R.calls.cidLtT
  have hcl := R.cidLt
  have toCh : ∀ x ∈ init, x.space = 4 → chainMsgs X E.cid E.k E.rest sv x := by
    intro x hx h4
    rcases (R.live x).mp hx with h | h | h
    · obtain ⟨i, -, rfl⟩ := mem_stackView.mp h; rw [enc_space] at h4; omega
    · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; rw [enc_space] at h4; simp only [Env.lsp] at h4; omega
    · rcases hout x h (Or.inl h4) with h | ⟨d1, -⟩
      · exact h
      · omega
  intro x hx h4
  obtain ⟨a, b, u⟩ := chain_rec4 hc (toCh x hx h4) h4
  exact ⟨a, by omega, by omega, fun y hy hy4 hys => u y (toCh y hy hy4) hy4 hys⟩

/-! ## 2. Which action rows produce a space-4 message -/

/-- The allowed space expressions other than the constant 4. -/
def spAllowedNo4 (T : Table) (loc : Bool) (e : Option Expr) : Bool :=
  decide (e = some (.c 0)) || decide (e = some (.c 2)) || decide (e = some (.c 3)) ||
  decide (e = some (.c 5)) || decide (e = some (.add (.c 16) (stE T 1))) ||
  decide (e = some (.add (.c 16) (stE T 5))) || (loc && decide (e = some Local.space))

theorem spAllowedNo4_of {T : Table} {loc : Bool} {e : Option Expr} (h : spAllowed T loc e = true)
    (h4 : e ≠ some (.c 4)) : spAllowedNo4 T loc e = true := by
  simp only [spAllowed, spAllowedNo4, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · exact absurd h h4
  · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

theorem toNat_16_add {a : F} (h : a.toNat + 16 < P) : ((16 : F) + a).toNat = 16 + a.toNat := by
  conv => lhs; rw [← Fp.cast_toNat a]
  rw [show (16 : F) = ((16 : Nat) : F) from rfl, ← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt (by omega)]

/-- A send whose space expression is allowed and not the constant 4 decodes to a space other than 4,
when the row's time and activation id are small (no wrap of `16 + ·`). -/
theorem space_ne4_of {T : Table} {loc : Bool} {tr : Trace} {pub : List F} {t r : Nat}
    (hloc : loc = true → (Local.isG.eval (tr.row pub t r) = 0 ∨ Local.isG.eval (tr.row pub t r) = 1) ∧
      (v Local.kCid).eval (tr.row pub t r) = (rowIn T tr pub t r).getD 5 0)
    (hl : (lvl (rowIn T tr pub t r)).toNat + 16 < P) (hc : ((rowIn T tr pub t r).getD 5 0).toNat + 16 < P)
    {i : Inter} (hA : spAllowedNo4 T loc i.msg.head? = true) :
    (decMsg (i.msg.map (·.eval (tr.row pub t r)))).space ≠ 4 := by
  have hP := P_val
  have sp : (decMsg (i.msg.map (·.eval (tr.row pub t r)))).space =
      (match i.msg.head? with | some e => e.eval (tr.row pub t r) | none => 0).toNat := by
    cases hmsg : i.msg <;> simp [decMsg, hmsg]
  rw [sp]
  have h1 : (rowIn T tr pub t r).getD 1 0 = lvl (rowIn T tr pub t r) := rfl
  simp only [spAllowedNo4, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hA
  rcases hA with (((((h | h) | h) | h) | h) | h) | ⟨hloc', h⟩ <;> rw [h] <;>
    simp only [Expr.eval, stE_eval]
  · rw [Fp.toNat_cast_of_lt (by omega)]; omega
  · rw [Fp.toNat_cast_of_lt (by omega)]; omega
  · rw [Fp.toNat_cast_of_lt (by omega)]; omega
  · rw [Fp.toNat_cast_of_lt (by omega)]; omega
  · rw [h1, show ((16 : Nat) : F) = (16 : F) from rfl, toNat_16_add hl]; omega
  · rw [show ((16 : Nat) : F) = (16 : F) from rfl, toNat_16_add hc]; omega
  · obtain ⟨hg, hk⟩ := hloc hloc'
    have e : Local.space = (1 - Local.isG) * (16 + v Local.kCid) + 2 * Local.isG := rfl
    rw [e]
    simp only [Expr.eval_add', Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', hk]
    rcases hg with hg | hg <;> rw [hg]
    · have : (((1 : Nat) : F) - 0) * (((16 : Nat) : F) + (rowIn T tr pub t r).getD 5 0) + ((2 : Nat) : F) * 0 =
          (16 : F) + (rowIn T tr pub t r).getD 5 0 := by
        rw [show ((1 : Nat) : F) = 1 from rfl, show ((16 : Nat) : F) = (16 : F) from rfl]; grind
      rw [this, toNat_16_add hc]; omega
    · have : (((1 : Nat) : F) - 1) * (((16 : Nat) : F) + (rowIn T tr pub t r).getD 5 0) + ((2 : Nat) : F) * 1 =
          ((2 : Nat) : F) := by rw [show ((1 : Nat) : F) = 1 from rfl]; grind
      rw [this, Fp.toNat_cast_of_lt (by omega)]; omega

/-- CALL's record send (space 4, slot `ts`). -/
def callRec : Inter :=
  chSend 4 (v cTs) 0 [v cPc + 1, v Call.kSb, v Call.kCid, v Call.charge] (v cTs) (v Call.act)

/-- The decidable check: a CH send with the constant space 4 is CALL's record send. -/
def Rec4 (T : Table) (t : Nat) : Bool :=
  T.inters.all fun i => !(decide (i.bus = busStk) && i.send && decide (i.msg.head? = some (.c 4))) ||
    (decide (t = 13) && decide (i = callRec))

theorem instr_rec4 : ∀ t, IsInstrM2 t → Rec4 (chipM2 t) t = true := by
  intro t ht
  rcases ht with ⟨h1, h14⟩ | rfl | rfl | rfl
  · rcases (show t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11 ∨
      t = 12 ∨ t = 13 ∨ t = 14 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  all_goals decide +kernel

/-- The record message of CALL row `r`. -/
def callRecMsg (tr : Trace) (pub : List F) (r : Nat) : Msg :=
  decMsg (callRec.msg.map (·.eval (tr.row pub 13 r)))

/-- **An instruction row's space-4 production is CALL's record.** -/
theorem instr_send4 {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    {t r : Nat} (htI : IsInstrM2 t) (hr : r < tr.height t) {m : List F}
    (hm : m ∈ rowMsgs (chipM2 t) tr pub t r busStk true)
    (hl : (lvl (rowIn (chipM2 t) tr pub t r)).toNat + 16 < P)
    (hc : ((rowIn (chipM2 t) tr pub t r).getD 5 0).toNat + 16 < P)
    (h4 : (decMsg m).space = 4) : t = 13 ∧ decMsg m = callRecMsg tr pub r := by
  obtain ⟨i, hi, rfl⟩ := mem_rowMsgs hm
  have hb := (List.mem_filter.mp hi).2
  simp only [decide_eq_true_eq] at hb
  have hR := List.all_eq_true.mp (instr_rec4 t htI) i (List.mem_filter.mp hi).1
  by_cases hh : i.msg.head? = some (.c 4)
  · simp only [hb.1, hb.2, hh, decide_true, Bool.and_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
      decide_eq_true_eq] at hR
    obtain ⟨rfl, rfl⟩ := hR
    exact ⟨rfl, rfl⟩
  · exfalso
    have hS := List.all_eq_true.mp (instr_spform t htI) i (List.mem_filter.mp hi).1
    simp only [Bool.or_eq_true, decide_eq_true_eq, hb.1, ne_eq, not_true_eq_false, false_or] at hS
    refine space_ne4_of (fun hl' => ?_) hl hc (spAllowedNo4_of hS hh) h4
    -- LOCAL: `isG` is a bit and `kCid` is the STATE activation id
    have h9 : t = 9 := by simpa using hl'
    subst h9
    have hT : (wasmBaseSegAir nloc ngl).tables[9]'(by simp [seg_air_len]) = Local.table :=
      seg_chipT nloc ngl 9 (by omega) (by omega)
    have hcon := table_constr_eqX H (by simp [seg_air_len]) Local.table hT hr
    obtain ⟨hsum, -⟩ := local_count_vals_of hcon
    have e9 : chipM2 9 = Local.table := rfl
    rw [e9]
    refine ⟨?_, ?_⟩
    · have hP := P_val
      have ev : Local.isG.eval (tr.row pub 9 r) = ((rowNat tr 9 r 26 + rowNat tr 9 r 27 : Nat) : F) := by
        simp only [Local.isG, Local.fGGet, Local.fGSet, v, Expr.eval, Trace.row, rowNat, Fp.cast_toNat,
          Lean.Grind.Semiring.natCast_add]
      rw [ev]
      rcases (by omega : rowNat tr 9 r 26 + rowNat tr 9 r 27 = 0 ∨ rowNat tr 9 r 26 + rowNat tr 9 r 27 = 1) with h | h <;>
        rw [h]
      · left; rfl
      · right; rfl
    · rw [← stE_eval]; rfl

/-- CALL's record has slot = the row's time. -/
theorem callRecMsg_slot (tr : Trace) (pub : List F) (r : Nat) :
    (callRecMsg tr pub r).slot = (lvl (rowIn (chipM2 13) tr pub 13 r)).toNat := by
  have e : lvl (rowIn (chipM2 13) tr pub 13 r) = (stE (chipM2 13) 1).eval (tr.row pub 13 r) := by
    rw [stE_eval]; rfl
  rw [e]; rfl

/-- The tables of a HOST row's productions send only in constant spaces other than 4. -/
def NoSend4 (T : Table) : Bool :=
  T.inters.all fun i => !(decide (i.bus = busStk) && i.send) ||
    match i.msg.head? with
    | some (.c k) => decide (k ≠ 4 ∧ k < 2 ^ 30)
    | _ => false

theorem noSend4_space {T : Table} (hT : NoSend4 T = true) {tr : Trace} {pub : List F} {t r : Nat} {x : Msg}
    (hx : x ∈ rowProd T tr pub t r) : x.space ≠ 4 := by
  have hP := P_val
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
  obtain ⟨i, hi, rfl⟩ := mem_rowMsgs hm
  have hb := (List.mem_filter.mp hi).2
  simp only [decide_eq_true_eq] at hb
  have h := List.all_eq_true.mp hT i (List.mem_filter.mp hi).1
  simp only [hb.1, hb.2, decide_true, Bool.and_self, Bool.not_true, Bool.false_or] at h
  cases hmsg : i.msg with
  | nil => rw [hmsg] at h; simp at h
  | cons e es =>
    rw [hmsg] at h
    simp only [List.head?_cons] at h
    cases e with
    | c k =>
      simp only [decide_eq_true_eq] at h
      simp only [decMsg, List.map_cons, List.getD_cons_zero, Expr.eval]
      rw [Fp.toNat_cast_of_lt (by omega)]; exact h.1
    | _ => simp at h

theorem host_noSend4 : NoSend4 Host.table = true ∧ NoSend4 HostB.table = true ∧ NoSend4 RegW.table = true ∧
    NoSend4 GasT = true := by decide +kernel

/-- **A HOST row produces no space-4 message** (its own sends, its call's `HOSTB` and REG-C net
traffic, its gas register). -/
theorem host_send_no4 {tr : Trace} {pub : List F} {r : Nat} {x : Msg} (hx : x ∈ prodCHS tr pub (22, r)) :
    x.space ≠ 4 := by
  obtain ⟨h1, h2, h3, h4⟩ := host_noSend4
  simp only [prodCHS, prodCHM2, rowProdM, hostbProdH, regProdH, gasProdH, ite_true, List.mem_append] at hx
  have ec : chipTM2 22 = Host.table := rfl
  rw [ec] at hx
  rcases hx with (hx | hx | hx) | hx
  · exact noSend4_space h1 hx
  · simp only [hostbProdOf, List.mem_flatMap] at hx
    obtain ⟨r', -, hx⟩ := hx; exact noSend4_space h2 hx
  · simp only [regProdOf, List.mem_flatMap] at hx
    obtain ⟨r', -, hx⟩ := hx
    unfold regNetProd at hx
    split at hx
    · cases hx
    · exact noSend4_space h3 hx
  · exact noSend4_space h4 hx

/-! ## 3. The count -/

theorem countP_le_one_of {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, ∀ y ∈ l, p x = true → p y = true → x = y) → l.countP p ≤ 1
  | [], _, _ => by simp
  | a :: l, hnd, h => by
    have ha := (List.nodup_cons.mp hnd).1
    have hl := (List.nodup_cons.mp hnd).2
    by_cases hp : p a = true
    · have h0 : l.countP p = 0 := List.countP_eq_zero.mpr fun x hx hpx => by
        have := h x (List.mem_cons_of_mem _ hx) a List.mem_cons_self hpx hp
        subst this; exact ha hx
      rw [List.countP_cons_of_pos hp, h0]; omega
    · rw [List.countP_cons_of_neg hp]
      exact countP_le_one_of hl fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)

theorem mem_rowMsgs_of {T : Table} {tr : Trace} {pub : List F} {t r b : Nat} {s : Bool} {i : Inter}
    (hi : i ∈ T.inters) (hb : i.bus = b) (hs : i.send = s) (hc : (i.count.eval (tr.row pub t r)).toNat = 1) :
    i.msg.map (·.eval (tr.row pub t r)) ∈ rowMsgs T tr pub t r b s := by
  rw [rowMsgs_eq]
  exact List.mem_filterMap.mpr ⟨i, List.mem_filter.mpr ⟨hi, by simp [hb, hs]⟩, by simp [hc]⟩

theorem ret_mem_actListM2 {tr : Trace} {pub : List F} {r : Nat} (hr : r < tr.height 14)
    (ha : (Ret.act.eval (tr.row pub 14 r)).toNat = 1) : (14, r) ∈ actListM2 tr pub := by
  refine List.mem_append_left _ (List.mem_append_left _ ?_)
  simp only [actList, actRows, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  exact ⟨13, by omega, r, ⟨hr, ha⟩, rfl⟩

/-- RET's record receive. -/
def retRec : Inter := chRecv 4 (v Ret.kCid) 0 [v Ret.retpc, v Ret.sbc, v Ret.cidc, v Ret.charge] (v Ret.tpr) Ret.tk

theorem retRec_mem : retRec ∈ Ret.inters := by simp [Ret.inters, retRec]

/-- **`TombDead` from the trace** (core form): from `HoldsX`, the row facts of every action row, the
CH fold premises, the in-boundary relation `h0` and the size bounds, for any final status `st ≤ 2`. -/
theorem seg_tombDead_rows (X : Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr) (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat}
    (hrows : ∀ ρ ∈ actListM2 tr pub,
      RowFactsSegMap X (rowInM tr pub ρ) (rowOutM tr pub ρ) (consCHS tr pub ρ) (prodCHS tr pub ρ) sg)
    (st : Nat) (hst2 : st ≤ 2) (hstN : pub.getD Boundary.pubStatus 0 = ((st : Nat) : F))
    (hinit : (initS tr pub).Nodup)
    (ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P)
    (hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.R * (S - (sg t).1) + g = (sg t).2 →
      X.R * (S + X.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.g0 < 2 ^ 64)
    {s0 : St} (h0 : Bnd X sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) :
    TombDead tr pub (finS tr pub) := by
  have hP := P_val
  have hch := seg_hch H X hb hg
  have hst : (segM0 tr pub :: (actListM2 tr pub).map (rowOutM tr pub)).Perm
      ([pub.getD pubPcOut 0, pub.getD pubTOut 0 + 1, pub.getD pubSOut 0, ((st : Nat) : F), pub.getD pubSbOut 0,
        tr.cell 0 0 (ix Segb.cols "cidf")] :: (actListM2 tr pub).map (rowInM tr pub)) := by
    have h := seg_hst H
    rw [segMF_eq, hstN] at h
    exact h
  obtain ⟨hnd, hinj, hrel⟩ := exec_rows_rel (X := X) (act := actListM2 tr pub) (inS := rowInM tr pub)
    (outS := rowOutM tr pub) (cons := consCHS tr pub) (prod := prodCHS tr pub) (init := initS tr pub)
    (fin := finS tr pub) (pcf := _) (N := _) (Sf := _) sg st hst2 hrows _ _ _ _ _ hst hch hinit
    (fun x hx => Nat.le_of_eq (seg_initS_tp tr pub x hx)) ht hfee hstepgas hg64 h0
    (fun _ _ => True) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) trivial
  -- every row: its time is `t0 + k + 1` and its activation id is `< 2^28`
  have hrow : ∀ ρ ∈ actListM2 tr pub, ∃ k, k < (actListM2 tr pub).length ∧
      (lvl (rowInM tr pub ρ)).toNat = (pub.getD pubTIn 0).toNat + k + 1 ∧ ((rowInM tr pub ρ).getD 5 0).toNat < 2 ^ 28 := by
    intro ρ hρ
    obtain ⟨k, hk, s, q, pc, S, sb, cid, live, hin, -, ⟨E, f, tps, tpl, -, hcid, -, R⟩, -, -⟩ := hrel ρ hρ
    refine ⟨k, hk, ?_, ?_⟩
    · rw [hin]; exact Fp.toNat_cast_of_lt (by omega)
    · rw [hin]
      have := R.cidLt
      show ((cid : Nat) : F).toNat < 2 ^ 28
      rw [Fp.toNat_cast_of_lt (by omega)]; omega
  -- a row's space-4 production is CALL's record, of slot = the row's time
  have hprod : ∀ ρ ∈ actListM2 tr pub, ∀ x ∈ prodCHS tr pub ρ, x.space = 4 →
      ρ.1 = 13 ∧ x = callRecMsg tr pub ρ.2 ∧ x.slot = (lvl (rowInM tr pub ρ)).toNat := by
    intro ρ hρ x hx h4
    obtain ⟨t, r⟩ := ρ
    rcases mem_actListM2 hρ with ⟨h22, -, -⟩ | ⟨htI, hr, -⟩
    · simp only at h22; subst h22; exact absurd h4 (host_send_no4 hx)
    · simp only at htI hr ⊢
      have hne : t ≠ 22 := by rcases htI with ⟨_, h⟩ | h | h | h <;> omega
      obtain ⟨-, eP, eI⟩ := consProd_instr (tr := tr) (pub := pub) (r := r) hne
      obtain ⟨k, hk, hl, hc⟩ := hrow (t, r) hρ
      rw [eP] at hx
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
      rw [eI] at hl hc
      obtain ⟨rfl, e⟩ := instr_send4 H htI hr hm (by omega) (by omega) h4
      refine ⟨rfl, e, ?_⟩
      rw [e, callRecMsg_slot, eI]
  intro r hr htk
  have hcon := table_constr_eqX H (by simp [seg_air_len]) RetT.table (seg_t14' nloc ngl) hr
  obtain ⟨hs, ha, -, htk1⟩ := ret_count_vals_of hcon
  obtain ⟨-, -, -, -, hc0, -, -⟩ := ret_sound (rowNat tr 14 r) (tr.row pub 14 r) (rowNat_lt tr 14 r) hcon
  have htk' : (Ret.tk.eval (tr.row pub 14 r)).toNat = 1 := by omega
  have hmem : (14, r) ∈ actListM2 tr pub := ret_mem_actListM2 hr (by omega)
  -- the activation id is the row's STATE `cid`, `< 2^28`
  have eC : (rowInM tr pub (14, r)).getD 5 0 = tr.cell 14 r Ret.kCid := by
    rw [show rowInM tr pub (14, r) = rowIn Ret.table tr pub 14 r from rfl, ← stE_eval]; rfl
  obtain ⟨-, -, -, hcl⟩ := hrow (14, r) hmem
  rw [eC] at hcl
  refine ⟨hcl, hc0 (by omega), fun x hx h4 hxs => ?_⟩
  -- the count
  let c := rowNat tr 14 r Ret.kCid
  let p : Msg → Bool := fun x => decide (x.space = 4 ∧ x.slot = c)
  have hcnt := hch.countP_eq p
  have e2 : (finS tr pub ++ (actListM2 tr pub).flatMap (consCHS tr pub)).countP p =
      (finS tr pub).countP p + ((actListM2 tr pub).flatMap (consCHS tr pub)).countP p := by
    rw [List.countP_append]
  have hL : (initS tr pub ++ (actListM2 tr pub).flatMap (prodCHS tr pub)).countP p ≤ 1 := by
    refine countP_le_one_of hnd fun x hx y hy px py => ?_
    simp only [p, decide_eq_true_eq] at px py
    have side : ∀ a ∈ initS tr pub, ∀ b ∈ (actListM2 tr pub).flatMap (prodCHS tr pub),
        a.space = 4 → b.space = 4 → a.slot = b.slot → False := by
      intro a ha b hb ha4 hb4 hab
      obtain ⟨ρ, hρ, hbρ⟩ := List.mem_flatMap.mp hb
      obtain ⟨-, -, e⟩ := hprod ρ hρ b hbρ hb4
      obtain ⟨k, -, hl, -⟩ := hrow ρ hρ
      have := (bnd_rec4 h0 a ha ha4).2.1
      omega
    rcases List.mem_append.mp hx with hx | hx <;> rcases List.mem_append.mp hy with hy | hy
    · exact ((bnd_rec4 h0 x hx px.1).2.2.2 y hy py.1 (py.2.trans px.2.symm)).symm
    · exact (side x hx y hy px.1 py.1 (px.2.trans py.2.symm)).elim
    · exact (side y hy x hx py.1 px.1 (py.2.trans px.2.symm)).elim
    · obtain ⟨ρ, hρ, hxρ⟩ := List.mem_flatMap.mp hx
      obtain ⟨ρ', hρ', hyρ'⟩ := List.mem_flatMap.mp hy
      obtain ⟨-, ex, sx⟩ := hprod ρ hρ x hxρ px.1
      obtain ⟨-, ey, sy⟩ := hprod ρ' hρ' y hyρ' py.1
      have hl : lvl (rowInM tr pub ρ) = lvl (rowInM tr pub ρ') := by
        rw [← Fp.cast_toNat (lvl (rowInM tr pub ρ)), ← Fp.cast_toNat (lvl (rowInM tr pub ρ')), ← sx, ← sy,
          px.2, py.2]
      have := hinj ρ hρ ρ' hρ' hl
      subst this
      rw [ex, ey]
  have hC : 1 ≤ ((actListM2 tr pub).flatMap (consCHS tr pub)).countP p := by
    refine List.countP_pos_iff.mpr ⟨decMsg (retRec.msg.map (·.eval (tr.row pub 14 r))),
      List.mem_flatMap.mpr ⟨(14, r), hmem, ?_⟩, ?_⟩
    · obtain ⟨eC', -, -⟩ := consProd_instr (tr := tr) (pub := pub) (r := r) (t := 14) (by omega)
      rw [eC']
      exact List.mem_map_of_mem (mem_rowMsgs_of retRec_mem rfl rfl htk')
    · simp only [p, decide_eq_true_eq]
      refine ⟨?_, rfl⟩
      simp only [retRec, chRecv, decMsg, List.cons_append, List.map_cons, List.getD_cons_zero, Expr.eval]
      exact Fp.toNat_cast_of_lt (by omega)
  have hF : (finS tr pub).countP p = 0 := by omega
  exact List.countP_eq_zero.mp hF x hx (by simp only [p, decide_eq_true_eq]; exact ⟨h4, hxs⟩)

#print axioms seg_tombDead_rows

/-- **`seg_tombDead`: `TombDead` at the out-boundary, from `seg_sound`'s own hypotheses** (any final
status `st ≤ 2`, so also for halting segments): the instruction rows' facts from `seg_rowfacts`
(`CodeOK`/`FuncOK`), the HOST rows' `HoldRowS`, the CH fold (`HostBLinked`, `RegCLinked`), the size
bounds, `initS` Nodup and the in-boundary relation `h0`. -/
theorem seg_tombDead (X : M2Ctx) {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hcode : CodeOK X.toCtx tr) (hfunc : FuncOK X.toCtx tr)
    (hb : HostBLinked tr pub) (hg : RegCLinked tr pub)
    {sg : Nat → Nat × Nat} (hkeep : SegKeepM2 tr pub sg) (hhold : HoldRowS X.toCtx tr pub sg)
    (st : Nat) (hst2 : st ≤ 2) (hstN : pub.getD Boundary.pubStatus 0 = ((st : Nat) : F))
    (hlen : (actListM2 tr pub).length < 2 ^ 28) (htin : (pub.getD pubTIn 0).toNat < 2 ^ 28)
    (hfeeN : (pub.getD pubSIn 0).toNat +
      ((pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat + 1) * (X.toCtx.maxFee + 1) < P)
    (hstepgas : ∀ t S g : Nat, X.toCtx.R * (S - (sg t).1) + g = (sg t).2 →
      X.toCtx.R * (S + X.toCtx.maxFee - (sg t).1) ≤ (sg t).2)
    (hg64 : X.toCtx.g0 < 2 ^ 64)
    (hinit : (initS tr pub).Nodup)
    {s0 : St} (h0 : Bnd X.toCtx sg s0 (pub.getD pubTIn 0).toNat (pub.getD pubSIn 0).toNat (segM0 tr pub)
      (initS tr pub)) :
    TombDead tr pub (finS tr pub) := by
  have hP := P_val
  have hI : SegInstrRows X.toCtx tr pub := fun t r htI hr ha => seg_rowfacts X H hcode hfunc htI hr ha
  have hrows := rowFactsSegMap_seg X.toCtx hI hkeep hhold
  have hlenEq := seg_len H (fun ρ hρ => (hrows ρ hρ).tsOut) (by omega)
  have ht : (pub.getD pubTIn 0).toNat + (actListM2 tr pub).length + 1 + (2 ^ 30 + 2 ^ 16) < P := by omega
  have hfee : (pub.getD pubSIn 0).toNat + ((actListM2 tr pub).length + 1) * (X.toCtx.maxFee + 1) < P := by
    have e : (pub.getD pubTOut 0).toNat - (pub.getD pubTIn 0).toNat = (actListM2 tr pub).length := by omega
    rw [e] at hfeeN; exact hfeeN
  exact seg_tombDead_rows X.toCtx H hb hg hrows st hst2 hstN hinit ht hfee hstepgas hg64 h0

#print axioms seg_tombDead

end WasmBase
