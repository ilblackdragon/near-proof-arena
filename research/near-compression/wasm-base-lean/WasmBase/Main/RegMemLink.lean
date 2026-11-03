import WasmBase.RegMem
import WasmBase.MemIO
import WasmBase.HostCtx
import WasmBase.Main.Rows
/-!
# WasmBase.Main.RegMemLink — REG' write rows ↔ the spec's `read_register` (E2E M1-a)

`WasmBase/RegMem.lean` adds the memory write to the register table: a `read_register` group's byte
rows consume the live memory byte at `ptr + pos` and produce the register byte there at the call's
time `ts`.  This file links those rows to the spec interpreter's `read_register`
(`NearSpecV3/Wasm/Host.lean`, `hostCall "read_register"`):

```
popArgs 2; payBaseH C.base; d ← regGetH a[0]; writeMemH a[1] d
```

## Proved (standard axioms only)

* **Spec side.**
  * `writeBytes_eq`, `writeBytes_facts` — `writeBytes s ptr d` rewrites only `pages`, keeps their
    number and sizes, and sets exactly `[ptr, ptr + |d|)` to `d` (the `writeLE_facts` of `Mem.lean`
    for a byte string);
  * `read_register_h` — the dispatch arm;
  * `regGetH_ok`, `read_register_run` — a successful `read_register` from `s` ends in
    `writeBytes s4 ptr d`, where `d` is the register's content and `s4` differs from the post-pop
    state only in gas (`read_register_state`).
* **Heap side.** `heap_read_register` — `HeapOK` after the write: consuming the old byte messages of
  `[ptr, ptr + |d|)` and producing `encB (ptr + i) d[i] t` gives `HeapOK … (writeBytes s ptr d) (t+1)`.
  This is `StepMem.heap_update` with the write's frame facts.
* **Row side.** `regw_write_msgs` — on a REG' row whose write count `act·(1−kind)·wr` is 1, the row's
  consumed CH messages contain `encB (ptr + pos) ob mtp` and its produced ones
  `encB (ptr + pos) byte ts`: the AIR row *is* the heap update of one byte.
* **Join.** `read_register_rows_heap` — if the write rows of a group are the bytes `pos = 0 … |d|−1`
  of the register `d` at `ptr` (what the group walk and the register channel give), then the
  messages the rows produce are exactly the ones `heap_read_register` consumes, so the heap after
  the rows is the heap of the spec's post-state of `read_register`.
* `regw_pub_result` — the new public constraints force the result limbs to 0 unless the function
  returned a value (`nres = 1`, `status = 1`): the arity-0 gap is closed.

## Open (named)

* The group-walk facts of REG' are REG's (`Main/RegWalk.lean`, proved for `wasmBaseRegAir`'s index
  26); REG' keeps REG's constraints as a prefix (`RegW.constraints_prefix`), but the walk lemmas are
  stated for that AIR and are not yet re-instantiated at `wasmBaseIfRegAir`'s index 27.
* `mtp < ts` on a write row needs R16 lookup soundness for `wasmBaseIfRegAir` (the per-bus send
  bound, proved for `wasmBaseHostAir`/`wasmBaseRegAir` as `host_hsend_r16`/`reg_hsend_r16`); the
  algebraic step is `regw_time_lt`.
* The liveness of the consumed messages is the CH-decomposition interface obligation, as for
  `hostb_mem_consumed` (`Main/MemIOLink.lean`).
-/
namespace WasmBase

open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## `writeBytes` -/

theorem foldl_congr_mem {α β : Type} (f g : α → β → α) :
    ∀ (l : List β) (a : α), (∀ b ∈ l, ∀ x, f x b = g x b) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | b :: l, a, h => by
    simp only [List.foldl_cons]
    rw [h b (by simp) a]
    exact foldl_congr_mem f g l _ (fun c hc => h c (by simp [hc]))

/-- `writeBytes` is a left fold of `writeByte` over the positions. -/
theorem writeBytes_eq (s : St) (a : Nat) (d : ByteArray) :
    writeBytes s a d = (List.range' 0 d.size).foldl (fun s i => writeByte s (a + i) d[i]!) s := by
  unfold writeBytes
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Id.run]
  simp
  rw [← List.foldl_attach (l := List.range' 0 d.size)]
  apply foldl_congr_mem
  intro x _ b
  have hx := x.2
  simp only [List.mem_range'] at hx
  rw [getElem!_pos d x.1 (by omega)]

/-- The prefix-`n` fold, for the induction. -/
theorem writeBytes_prefix_facts {s : St} (hP : PagesOK s) {a : Nat} (d : ByteArray) :
    ∀ n, a + n ≤ memBytes s →
    let S := (List.range' 0 n).foldl (fun s i => writeByte s (a + i) d[i]!) s
    (∃ pg, S = { s with pages := pg }) ∧ S.pages.size = s.pages.size ∧ PagesOK S ∧
    ∀ b, readByte S b = if a ≤ b ∧ b < a + n then d[b - a]! else readByte s b := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨⟨s.pages, rfl⟩, rfl, hP, fun b => ?_⟩
    simp only [List.range'_zero, List.foldl_nil]
    rw [if_neg (by omega)]
  | succ n ih =>
    intro hn
    obtain ⟨⟨pg, hpg⟩, hsz, hok, hrd⟩ := ih (by omega)
    simp only
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
    generalize hS : List.foldl _ s (List.range' 0 n) = S at hpg hsz hok hrd
    have hmS : memBytes S = memBytes s := by unfold memBytes; rw [hsz]
    refine ⟨⟨_, by rw [writeByte_pages, hpg]⟩, by rw [writeByte_size, hsz], writeByte_ok hok _ _,
      fun b => ?_⟩
    rw [readByte_writeByte hok (by rw [hmS]; omega), hrd b]
    by_cases hb : a + n = b
    · subst hb; simp
    · rw [if_neg hb]
      by_cases h1 : a ≤ b ∧ b < a + n
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

/-- **`writeBytes` facts**: only `pages` changes, the page count and sizes are kept, and the bytes
`[a, a + |d|)` become `d`. -/
theorem writeBytes_facts {s : St} (hP : PagesOK s) {a : Nat} {d : ByteArray}
    (ha : a + d.size ≤ memBytes s) :
    (∃ pg, writeBytes s a d = { s with pages := pg }) ∧ (writeBytes s a d).pages.size = s.pages.size ∧
    PagesOK (writeBytes s a d) ∧
    ∀ b, readByte (writeBytes s a d) b = if a ≤ b ∧ b < a + d.size then d[b - a]! else readByte s b := by
  rw [writeBytes_eq]
  exact writeBytes_prefix_facts hP d d.size ha

/-! ## The spec's `read_register` -/

/-- The dispatch arm of `read_register` (`Host.lean`). -/
theorem read_register_h :
    hostCall "read_register" = some
      ((popArgs 2) >>= fun a => (payBaseH C.base) >>= fun _ => (regGetH a[0]) >>= fun d =>
        writeMemH a[1] d) :=
  hostCall.eq_1

/-- A successful gas operation changes only the gas. -/
theorem withGas_ok_state {f : Gas → Gas × Option String} {s s' : St}
    (h : (withGas f).run s = .ok () s') : s' = { s with gas := (f s.gas).1 } := by
  rw [withGas_run] at h
  split at h
  · cases h
  · cases h; rfl

theorem payBaseH_ok_state {c : Cost} {s s' : St} (h : (payBaseH c).run s = .ok () s') :
    s' = { s with gas := (payBase s.gas c).1 } := withGas_ok_state h

theorem payPerH_ok_state {c : Cost} {n : Nat} {s s' : St} (h : (payPerH c n).run s = .ok () s') :
    s' = { s with gas := (payPer s.gas c n).1 } := withGas_ok_state h

/-- **`regGetH` on a present register** returns its bytes (after its two charges). -/
theorem regGetH_ok {s s1 s2 : St} {id k : Nat} {d : ByteArray}
    (hf : s.registers.find? (·.1 = id) = some (k, d))
    (e1 : (payBaseH C.readRegisterBase).run s = .ok () s1)
    (e2 : (payPerH C.readRegisterByte d.size).run s1 = .ok () s2) :
    (regGetH id).run s = .ok d s2 := by
  unfold regGetH
  rw [bind_ok (hmGet_run _)]
  simp only [hf]
  rw [bind_ok e1, bind_ok e2]
  rfl

/-- **A successful `read_register`.**  Popping `(id, ptr)`, the base charge, the register read and
the write's two charges succeed, and `ptr + |d|` is inside memory: the call ends in
`writeBytes s4 ptr d`, i.e. the register's bytes are in memory at `ptr`. -/
theorem read_register_run {s s0 s1 s2 s3 s4 : St} {args : Vector Nat 2} {d : ByteArray}
    (e0 : (popArgs 2).run s = .ok args s0)
    (e1 : (payBaseH C.base).run s0 = .ok () s1)
    (e2 : (regGetH args[0]).run s1 = .ok d s2)
    (e3 : (payBaseH C.writeMemoryBase).run s2 = .ok () s3)
    (e4 : (payPerH C.writeMemoryByte d.size).run s3 = .ok () s4)
    (hb : ¬ (args[1] + d.size > memBytes s4)) :
    ((popArgs 2) >>= fun a => (payBaseH C.base) >>= fun _ => (regGetH a[0]) >>= fun d =>
        writeMemH a[1] d : HM Unit).run s = .ok () (writeBytes s4 args[1] d) := by
  rw [bind_ok e0, bind_ok e1, bind_ok e2]
  exact writeMemH_ok e3 e4 hb

/-- Between the pop and the write, `read_register` changes only the gas (and `regGetH` reads the
registers of the post-pop state): pages, globals and registers are the post-pop state's. -/
theorem read_register_state {s0 s1 s2 s3 s4 : St} {id k : Nat} {d : ByteArray}
    (e1 : (payBaseH C.base).run s0 = .ok () s1)
    (hf : s0.registers.find? (·.1 = id) = some (k, d))
    (e2a : (payBaseH C.readRegisterBase).run s1 = .ok () s2)
    (e2b : (payPerH C.readRegisterByte d.size).run s2 = .ok () s3)
    (e3 : (payBaseH C.writeMemoryBase).run s3 = .ok () s4) :
    (regGetH id).run s1 = .ok d s3 ∧ s4.pages = s0.pages ∧ s4.globals = s0.globals := by
  have h1 := payBaseH_ok_state e1
  have h2 := payBaseH_ok_state e2a
  have h3 := payPerH_ok_state e2b
  have h4 := payBaseH_ok_state e3
  refine ⟨regGetH_ok (by rw [h1]; exact hf) e2a e2b, ?_, ?_⟩ <;> (subst h4 h3 h2 h1; rfl)

/-! ## The heap after the write -/

/-- **The heap after `read_register`'s write.**  The old byte messages of `[ptr, ptr + |d|)` are
consumed and `encB (ptr + i) d[i] t` produced: that is `HeapOK` of `writeBytes s ptr d` at `t + 1`.
`heap_update` with the write's frame facts (`writeBytes_facts`). -/
theorem heap_read_register {E : Env} {s : St} {t ptr : Nat} {d : ByteArray} (H : HeapOK E s t)
    (hb : ptr + d.size ≤ memBytes s) (ob tb : Nat → Nat)
    (hlive : ∀ i, i < d.size → E.live (encB (ptr + i) (ob i) (tb i))) :
    HeapOK { E with live := (stepLive E.live
        ((List.range d.size).map fun i => encB (ptr + i) (ob i) (tb i))
        ((List.range d.size).map fun i => encB (ptr + i) (d[i]!).toNat t)) }
      (writeBytes s ptr d) (t + 1) := by
  obtain ⟨⟨pg, hpg⟩, hsz, hok, hrd⟩ := writeBytes_facts H.pages hb
  refine heap_update H hok (by rw [hpg]) (by unfold memBytes; rw [hsz]) ?_ ob tb
    (fun i => (d[i]!).toNat) hlive ?_
  · intro a ha
    rw [hrd a, if_neg ha]
  · intro i hi
    rw [hrd (ptr + i), if_pos (by omega), show ptr + i - ptr = i by omega]

/-! ## The AIR rows -/

/-- The destination address of a REG' row: `ptr + 2^16·ptrHi + pos`. -/
def regwAddr (tr : Trace) (t r : Nat) : Nat :=
  rowNat tr t r Reg.ptr + 65536 * rowNat tr t r RegW.ptrHi + rowNat tr t r Reg.pos

/-- The memory message a write row consumes: the old byte `ob` at its producer time `mtp`. -/
def regwMemRecv (tr : Trace) (t r : Nat) : Msg :=
  encB (regwAddr tr t r) (rowNat tr t r RegW.ob) (rowNat tr t r RegW.mtp)

/-- The memory message a write row produces: the register byte at the call's time `ts`. -/
def regwMemSend (tr : Trace) (t r : Nat) : Msg :=
  encB (regwAddr tr t r) (rowNat tr t r Reg.bv) (rowNat tr t r Reg.ts)

theorem regw_recv_mem : chRecv 3 RegW.addr 0 [v RegW.ob, 0, 0, 0] (v RegW.mtp) RegW.wcnt ∈
    RegW.table.inters :=
  List.mem_append_right _ List.mem_cons_self

theorem regw_send_mem : chSend 3 RegW.addr 0 [v Reg.bv, 0, 0, 0] (v Reg.ts) RegW.wcnt ∈
    RegW.table.inters :=
  List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem col_eval_nat (tr : Trace) (pub : List F) (t r i : Nat) :
    (v i).eval (tr.row pub t r) = ((rowNat tr t r i : Nat) : F) := by
  simp only [Chips.v, Expr.eval_col, Trace.row, cell_cast]

theorem regw_addr_eval (tr : Trace) (pub : List F) (t r : Nat) :
    RegW.addr.eval (tr.row pub t r) = ((regwAddr tr t r : Nat) : F) := by
  simp only [RegW.addr, regwAddr, Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', col_eval_nat,
    Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]

/-- **A write row is a one-byte heap update.**  When `act·(1−kind)·wr = 1` (and the address is a
canonical field element, which the R16 checks give: `< 2^27 + 2^16`), the row consumes
`encB (ptr + pos) ob mtp` and produces `encB (ptr + pos) byte ts` on the CH bus. -/
theorem regw_write_msgs {tr : Trace} {pub : List F} {t r : Nat}
    (hw : (RegW.wcnt.eval (tr.row pub t r)).toNat = 1) (ha : regwAddr tr t r < P) :
    regwMemRecv tr t r ∈ rowCons RegW.table tr pub t r ∧
      regwMemSend tr t r ∈ rowProd RegW.table tr pub t r := by
  have hdec : ∀ (x tp : Nat), x < P → tp < P →
      decMsg [((3 : Nat) : F), ((regwAddr tr t r : Nat) : F), ((0 : Nat) : F), ((x : Nat) : F),
        ((0 : Nat) : F), ((0 : Nat) : F), ((0 : Nat) : F), ((tp : Nat) : F)] =
        encB (regwAddr tr t r) x tp := by
    intro x tp hx htp
    simp only [decMsg, encB, List.getD_cons_zero, List.getD_cons_succ]
    rw [Fp.toNat_cast_of_lt (by rw [P_val]; omega), Fp.toNat_cast_of_lt ha,
      Fp.toNat_cast_of_lt (by rw [P_val]; omega), Fp.toNat_cast_of_lt hx,
      Fp.toNat_cast_of_lt htp]
  constructor
  · unfold rowCons
    rw [rowMsgs_eq]
    refine List.mem_map.mpr ⟨_, List.mem_filterMap.mpr ⟨_, List.mem_filter.mpr
      ⟨regw_recv_mem, by simp [chRecv, busStk]⟩, by rw [if_pos (by simpa [chRecv] using hw)]⟩, ?_⟩
    simp only [chRecv, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      regw_addr_eval, col_eval_nat, Expr.eval_ofNat']
    exact hdec _ _ (rowNat_lt _ _ _ _) (rowNat_lt _ _ _ _)
  · unfold rowProd
    rw [rowMsgs_eq]
    refine List.mem_map.mpr ⟨_, List.mem_filterMap.mpr ⟨_, List.mem_filter.mpr
      ⟨regw_send_mem, by simp [chSend, busStk]⟩, by rw [if_pos (by simpa [chSend] using hw)]⟩, ?_⟩
    simp only [chSend, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      regw_addr_eval, col_eval_nat, Expr.eval_ofNat']
    exact hdec _ _ (rowNat_lt _ _ _ _) (rowNat_lt _ _ _ _)

/-- The algebraic half of `mtp < ts`: the two `timeChk` values, once known to be 16-bit (R16
soundness), give `mtp + 1 + n = ts` in the naturals with `n < 2^30 + 2^16`, for times below `2^29`
(segment-local times are far below that, plan §3.2: `< 2^24`). -/
theorem regw_time_lt {ts mtp hp x y : Nat} (hts : ts < 2 ^ 29) (hm : mtp < 2 ^ 29)
    (hx : x < 65536) (hy : y < 65536)
    (h1 : ((x : Nat) : F) = ((ts : Nat) : F) - ((mtp : Nat) : F) - ((1 : Nat) : F) -
      ((65536 : Nat) : F) * ((hp : Nat) : F))
    (h2 : ((y : Nat) : F) = ((4 : Nat) : F) * ((hp : Nat) : F)) :
    mtp < ts := by
  have e : ((mtp + 1 + (x + 16384 * y) : Nat) : F) = ((ts : Nat) : F) := by
    simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
    rw [h1, h2]
    have : ((65536 : Nat) : F) = ((16384 : Nat) : F) * ((4 : Nat) : F) := by
      rw [← Lean.Grind.Semiring.natCast_mul]
    rw [this]; grind
  have := congrArg Fp.toNat e
  have hP := P_val
  rw [Fp.toNat_cast, Fp.toNat_cast_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  omega

/-- **Join: the write group's produced messages are the spec's post-heap entries.**  If the write
rows `ρ i` (`i < |d|`) of one group carry `pos = i`, the group's destination `ptr`, the call's time
`ts` and the register's bytes `byte = d[i]` (the facts the group walk and the register channel give),
then the messages they produce are exactly the ones `heap_read_register` adds, so the heap after the
rows is `HeapOK … (writeBytes s ptr d) (ts + 1)`: the heap of the spec's post-state of
`read_register` (`read_register_run`). -/
theorem read_register_rows_heap {E : Env} {s : St} {tr : Trace} {t ts ptr : Nat} {d : ByteArray}
    (ρ : Nat → Nat) (H : HeapOK E s ts) (hb : ptr + d.size ≤ memBytes s)
    (hpos : ∀ i, i < d.size → rowNat tr t (ρ i) Reg.pos = i)
    (hptr : ∀ i, i < d.size →
      rowNat tr t (ρ i) Reg.ptr + 65536 * rowNat tr t (ρ i) RegW.ptrHi = ptr)
    (hts : ∀ i, i < d.size → rowNat tr t (ρ i) Reg.ts = ts)
    (hbv : ∀ i, i < d.size → rowNat tr t (ρ i) Reg.bv = (d[i]!).toNat)
    (hlive : ∀ i, i < d.size → E.live (regwMemRecv tr t (ρ i))) :
    (List.range d.size).map (fun i => regwMemSend tr t (ρ i)) =
      (List.range d.size).map (fun i => encB (ptr + i) (d[i]!).toNat ts) ∧
    HeapOK { E with live := (stepLive E.live
        ((List.range d.size).map fun i => regwMemRecv tr t (ρ i))
        ((List.range d.size).map fun i => regwMemSend tr t (ρ i))) }
      (writeBytes s ptr d) (ts + 1) := by
  have haddr : ∀ i, i < d.size → regwAddr tr t (ρ i) = ptr + i := by
    intro i hi; unfold regwAddr; rw [← hptr i hi, hpos i hi]
  have hsend : (List.range d.size).map (fun i => regwMemSend tr t (ρ i)) =
      (List.range d.size).map (fun i => encB (ptr + i) (d[i]!).toNat ts) := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    unfold regwMemSend
    rw [haddr i hi, hbv i hi, hts i hi]
  have hrecv : (List.range d.size).map (fun i => regwMemRecv tr t (ρ i)) =
      (List.range d.size).map (fun i => encB (ptr + i) (rowNat tr t (ρ i) RegW.ob)
        (rowNat tr t (ρ i) RegW.mtp)) := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    unfold regwMemRecv
    rw [haddr i hi]
  refine ⟨hsend, ?_⟩
  rw [hsend, hrecv]
  exact heap_read_register H hb (fun i => rowNat tr t (ρ i) RegW.ob) (fun i => rowNat tr t (ρ i) RegW.mtp)
    (fun i hi => by have := hlive i hi; unfold regwMemRecv at this; rwa [haddr i hi] at this)

/-! ## The public result -/

/-- **The arity-0 gap is closed.**  On any row of a trace satisfying REG''s constraints, the public
result limbs vanish unless `nres = 1` and `status = 1`.  (Before, BOUNDARY received them only with
count `first·nres·(2−status)`, so for a void function they were free — the accepted milestone-1
mutant `pub.result+1`.) -/
theorem regw_pub_result {c : Nat → Nat} {rw : Row}
    (hc : ∀ e ∈ RegW.table.constraints, e.eval (natRow c rw) = 0) (i : Nat) (hi : i < 4) :
    (1 - rw.pub Boundary.pubNres) * rw.pub (Boundary.pubR + i) = 0 ∧
      (rw.pub Boundary.pubStatus - 1) * rw.pub (Boundary.pubR + i) = 0 := by
  have h1 := hc (RegW.cPubR i) (List.mem_append_right _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))))
  have h2 := hc (RegW.cPubRTrap i) (List.mem_append_right _ (List.mem_append_right _
    (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))
  simp only [RegW.cPubR, RegW.cPubRTrap, Chips.pv, Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat',
    Expr.eval_pub, natRow] at h1 h2
  exact ⟨h1, h2⟩

end WasmBase
