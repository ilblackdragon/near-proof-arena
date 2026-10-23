import WasmBase.Main.HostBus
import WasmBase.MemIO
/-!
# WasmBase.Main.MemIOBus — the HOSTB ↔ space-3 block of the CH decomposition

`HostB.inters` emits the linear-memory message of `ptr + pos` for every **request** byte
(`Chips.HostB.memCnt`): it consumes the live byte at its producer time `mtp` and re-produces it at
`ts`.  Those messages ride the CH bus (space 3), so `HOSTB` is no longer CH-free:
`Main/ExecHost.host_part_nil_env`'s `HOSTB` clause is false, and `msgs_ch_host` adds its block.

## Where the block goes

`actListHost` is `actList … ++ hostActRows`, and **`HOSTB` rows are not action rows**: they carry the
`ts` of their call and never advance time, so they cannot be a `RowFactsSeg` step (`tsOut` is
`lvl inS + 1`).  They belong to the host call they carry — `(ts, hid)` is the group key
(`HostB.cTs`, `HostB.cHidConst`, and the same pair on `HOSTQ`).

So the block is folded into the **host row's** channel messages (`prodCH`/`consCH`,
`Main/SegHarness`), and `hostb_partition` proves the fold is a partition: every active `HOSTB` row
belongs to exactly one active HOST row (given `HostBLinked`, the trace-level grouping premise), and
inactive rows emit nothing (`hostb_inactive_nil`).

## What the link proves

`hostb_mem_consumed` — a request byte's consumed space-3 message is live in the pre-heap, so by
`StepMem.heap_read` it carries the **current memory byte**: `memory[ptr + pos] = byte`, and the
address is in bounds.  This is the `(ptr, len)` → linear-memory link, one row at a time;
`MemIO.heap_retime` turns the same messages into `HeapOK` at `t + 1`.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## List rearrangement helpers

Generic `flatMap` facts the partition needs: splitting a `flatMap` of `++`, and turning a `filter`
into an `if`. -/

/-- A `flatMap` of appended blocks is a permutation of the two `flatMap`s. -/
theorem perm_flatMap_append {α β : Type} (l : List α) (f g : α → List β) :
    List.Perm (l.flatMap fun a => f a ++ g a) (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_cons]
    refine List.Perm.trans (List.Perm.of_eq (List.append_assoc _ _ _)) ?_
    refine List.Perm.trans (List.Perm.append_left (f a) ?_)
      (List.Perm.of_eq (List.append_assoc _ _ _).symm)
    exact List.Perm.trans (List.Perm.append_left (g a) ih)
      (List.perm_append_comm_assoc (g a) (List.flatMap f l) (List.flatMap g l))

/-- Two nested `flatMap`s commute up to `Perm`. -/
theorem perm_flatMap_swap {α β γ : Type} (l₁ : List α) (l₂ : List β) (f : α → β → List γ) :
    List.Perm (l₂.flatMap fun b => l₁.flatMap fun a => f a b)
      (l₁.flatMap fun a => l₂.flatMap fun b => f a b) := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    have h1 : (l₂.flatMap fun b => List.flatMap (fun a => f a b) (a :: l))
        = (l₂.flatMap fun b => f a b ++ List.flatMap (fun a => f a b) l) := by
      simp only [List.flatMap_cons]
    rw [h1, List.flatMap_cons]
    refine List.Perm.trans (perm_flatMap_append l₂ (fun b => f a b)
      (fun b => List.flatMap (fun a => f a b) l)) ?_
    exact List.Perm.append (List.Perm.refl _) ih

/-- A `filter`ed `flatMap` is the `flatMap` of the guarded blocks. -/
theorem filter_flatMap_ite {α β : Type} (l : List α) (p : α → Bool) (f : α → List β) :
    (l.filter p).flatMap f = l.flatMap (fun a => if p a = true then f a else []) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.filter_cons]
    by_cases h : p a = true
    · rw [if_pos h, List.flatMap_cons, List.flatMap_cons, if_pos h, ih]
    · rw [if_neg h, List.flatMap_cons, if_neg h, List.nil_append, ih]

/-- **A `flatMap` of guarded blocks with a unique match.**  If `x` is the only element of `l` whose
predicate holds, the guarded `flatMap` collapses to `f x`. -/
theorem flatMap_key_unique {α β : Type} (l : List α) (p : α → Bool) (f : α → List β) {x : α}
    (hnd : l.Nodup) (hmem : x ∈ l) (hun : ∀ y ∈ l, p y = true → y = x) (hx : p x = true) :
    l.flatMap (fun y => if p y = true then f y else []) = f x := by
  induction l with
  | nil => exact absurd hmem List.not_mem_nil
  | cons a l ih =>
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    rw [List.flatMap_cons]
    by_cases hxa : a = x
    · subst hxa
      rw [if_pos hx]
      have hnil : ∀ y ∈ l, (p y) = false := by
        intro y hy
        have hne : y ≠ a := fun e => hnot (e ▸ hy)
        have : ¬ (p y = true) := fun h => hne (hun y (List.mem_cons_of_mem _ hy) h)
        simpa using this
      rw [List.flatMap_eq_nil_iff.mpr (fun y hy => by
        rw [if_neg (by simpa using hnil y hy)]), List.append_nil]
    · have hpa : p a = false := by
        cases h : p a with
        | false => rfl
        | true => exact absurd (hun a List.mem_cons_self h) hxa
      rw [if_neg (by simpa using hpa), List.nil_append]
      have hmem' : x ∈ l := by
        rcases List.mem_cons.mp hmem with rfl | h
        · exact absurd rfl hxa
        · exact h
      exact ih hnd' hmem' (fun y hy => hun y (List.mem_cons_of_mem _ hy))

/-! ## The memory message of a request byte -/

/-- The space-3 address of a `HOSTB` row: `ptr + pos` (`Chips.HostB.memAddr`). -/
def hostbAddr (tr : Trace) (r : Nat) : Nat :=
  rowNat tr 25 r HostB.ptrLo + 65536 * rowNat tr 25 r HostB.ptrHi + rowNat tr 25 r HostB.pos

/-- The memory message a request byte consumes: `encB (ptr + pos) byte mtp`. -/
def hostbMemRecv (tr : Trace) (r : Nat) : Msg :=
  encB (hostbAddr tr r) (rowNat tr 25 r HostB.bv) (rowNat tr 25 r HostB.mtp)

/-- The memory message a request byte produces: the same byte, re-timed to `ts`. -/
def hostbMemSend (tr : Trace) (r : Nat) : Msg :=
  encB (hostbAddr tr r) (rowNat tr 25 r HostB.bv) (rowNat tr 25 r HostB.ts)

/-- A request byte is `dir = 0`, `reg = 0`. -/
def hostbReq (tr : Trace) (r : Nat) : Prop :=
  rowNat tr 25 r HostB.dir = 0 ∧ rowNat tr 25 r HostB.reg = 0

/-! ## The row shape -/

/-- The `HOSTB` CH interactions, by direction.  A request byte is the table's only space-3 pair. -/
theorem hostb_inters_stk :
    (HostB.table.inters.filter (fun i => i.bus = busStk ∧ i.send = false)) =
      [chRecv 3 HostB.memAddr 0 [v HostB.bv, 0, 0, 0] (v HostB.mtp) HostB.memCnt] ∧
    (HostB.table.inters.filter (fun i => i.bus = busStk ∧ i.send = true)) =
      [chSend 3 HostB.memAddr 0 [v HostB.bv, 0, 0, 0] (v HostB.ts) HostB.memCnt] := by
  constructor <;> decide

/-- **`rowAct` is `memCnt = 1` for `HOSTB`.**  The table's first interaction is counted by `memCnt`,
so activity and a unit memory count are the same statement — which is what lets an inactive row's
space-3 pair be dropped. -/
theorem hostb_rowAct_iff {tr : Trace} {pub : List F} {r : Nat} :
    rowAct HostB.table tr pub 25 r ↔ (HostB.memCnt.eval (tr.row pub 25 r)).toNat = 1 := by
  unfold rowAct HostB.table HostB.inters HostB.memCnt Chips.v
  simp only [List.getD_cons_zero]
  rfl

/-- **An inactive `HOSTB` row emits nothing on the CH bus.**  `rowAct` is `memCnt = 1`, and
`memCnt ≤ 1` (`hostb_memCnt_bit`), so an inactive row has a zero count on both space-3 messages. -/
theorem hostb_inactive_nil {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) {r : Nat} (hr : r < tr.height 25)
    (hneg : ¬ rowAct HostB.table tr pub 25 r) :
    rowMsgs HostB.table tr pub 25 r busStk true = [] ∧
      rowMsgs HostB.table tr pub 25 r busStk false = [] := by
  have hbit := hostb_memCnt_bit H hr
  have hmem0 : (HostB.memCnt.eval (tr.row pub 25 r)).toNat = 0 := by
    have hne : (HostB.memCnt.eval (tr.row pub 25 r)).toNat ≠ 1 :=
      fun hv => hneg (hostb_rowAct_iff.mpr hv)
    omega
  have hcnt : ∀ s : Bool, rowMsgs HostB.table tr pub 25 r busStk s = [] := by
    intro s
    cases s
    · rw [rowMsgs_eq, hostb_inters_stk.1]
      simp only [List.filter_cons, List.filter_nil, decide_true, Bool.true_and,
        List.filterMap_cons, List.filterMap_nil, chRecv]
      rw [hmem0]; rfl
    · rw [rowMsgs_eq, hostb_inters_stk.2]
      simp only [List.filter_cons, List.filter_nil, decide_true, Bool.true_and,
        List.filterMap_cons, List.filterMap_nil, chSend]
      rw [hmem0]; rfl
  exact ⟨hcnt true, hcnt false⟩

/-! ## The block, as the active rows' messages -/

/-- The `HOSTB` rows' produced CH messages, decoded, row by row. -/
theorem hostb_part_ch_send (tr : Trace) (pub : List F) :
    (part HostB.table tr pub 25 busStk true).map decMsg =
      (List.range (tr.height 25)).flatMap fun r => rowProd HostB.table tr pub 25 r := by
  unfold part
  rw [List.map_flatMap]
  rfl

/-- The `HOSTB` rows' consumed CH messages, decoded, row by row. -/
theorem hostb_part_ch_recv (tr : Trace) (pub : List F) :
    (part HostB.table tr pub 25 busStk false).map decMsg =
      (List.range (tr.height 25)).flatMap fun r => rowCons HostB.table tr pub 25 r := by
  unfold part
  rw [List.map_flatMap]
  rfl

/-! ## The partition of the block over the calls -/

/-- **The partition of the `HOSTB` block over the active HOST rows.**  Under `HostBLinked`, the
active `HOSTB` rows, grouped by their call and concatenated in call order, are exactly the active
`HOSTB` rows.  `Perm` because the fold reorders the block (the rows of a call are contiguous in any
generated trace, but that is not a constraint). -/
theorem hostb_partition {nloc ngl : Nat} {tr : Trace} {pub : List F}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (hb : HostBLinked tr pub) (s : Bool) :
    List.Perm
      ((hostActRows tr pub).flatMap (fun ρ => (hostbOf tr pub ρ.2).flatMap
        fun r' => rowMsgs HostB.table tr pub 25 r' busStk s))
      ((List.range (tr.height 25)).flatMap (fun r' =>
        if rowAct HostB.table tr pub 25 r' then rowMsgs HostB.table tr pub 25 r' busStk s else [])) := by
  -- step 1: rewrite each call's block as the `(ts, hid)`-guarded flatMap over the whole table
  have step1 : ∀ ρ ∈ hostActRows tr pub,
      (hostbOf tr pub ρ.2).flatMap (fun r' => rowMsgs HostB.table tr pub 25 r' busStk s)
        = (List.range (tr.height 25)).flatMap (fun r' =>
            if (decide (rowNat tr 25 r' HostB.ts = rowNat tr 22 ρ.2 cTs ∧
                rowNat tr 25 r' HostB.hid = rowNat tr 22 ρ.2 Host.hid)) = true
            then rowMsgs HostB.table tr pub 25 r' busStk s else []) := by
    intro ρ _
    rw [hostbOf, filter_flatMap_ite]
  have e1 : (hostActRows tr pub).flatMap (fun ρ => (hostbOf tr pub ρ.2).flatMap
      fun r' => rowMsgs HostB.table tr pub 25 r' busStk s)
      = (hostActRows tr pub).flatMap (fun ρ =>
          (List.range (tr.height 25)).flatMap (fun r' =>
            if (decide (rowNat tr 25 r' HostB.ts = rowNat tr 22 ρ.2 cTs ∧
                rowNat tr 25 r' HostB.hid = rowNat tr 22 ρ.2 Host.hid)) = true
            then rowMsgs HostB.table tr pub 25 r' busStk s else [])) :=
    flatMap_congr_on _ _ _ step1
  -- step 2: for each `HOSTB` row, at most one call matches
  have key : ∀ r' ∈ List.range (tr.height 25),
      ((hostActRows tr pub).flatMap (fun ρ =>
        if (decide (rowNat tr 25 r' HostB.ts = rowNat tr 22 ρ.2 cTs ∧
            rowNat tr 25 r' HostB.hid = rowNat tr 22 ρ.2 Host.hid)) = true
        then rowMsgs HostB.table tr pub 25 r' busStk s else []))
      = if rowAct HostB.table tr pub 25 r' then rowMsgs HostB.table tr pub 25 r' busStk s
        else [] := by
    intro r' hr'
    rw [List.mem_range] at hr'
    by_cases hact : rowAct HostB.table tr pub 25 r'
    · obtain ⟨r, hr, hract, hts, hhid⟩ := hb.linked r' hr' hact
      have hmem : (22, r) ∈ hostActRows tr pub := by
        simp only [hostActRows, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨r, ⟨hr, hract⟩, rfl⟩
      have hnd : (hostActRows tr pub).Nodup := by
        unfold hostActRows
        refine nodup_map_inj _ ?_ _ (List.nodup_range.filter _)
        intro a b hab
        simp only [Prod.mk.injEq] at hab
        exact hab.2
      have hun : ∀ y ∈ hostActRows tr pub,
          (decide (rowNat tr 25 r' HostB.ts = rowNat tr 22 y.2 cTs ∧
              rowNat tr 25 r' HostB.hid = rowNat tr 22 y.2 Host.hid)) = true → y = (22, r) := by
        intro y hy hp
        obtain ⟨r₂, hr₂, rfl⟩ := List.mem_map.mp hy
        simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hr₂
        simp only [decide_eq_true_eq] at hp
        have h1 : rowNat tr 22 r₂ cTs = rowNat tr 22 r cTs := by rw [← hp.1, hts]
        have h2 : rowNat tr 22 r₂ Host.hid = rowNat tr 22 r Host.hid := by rw [← hp.2, hhid]
        rw [hb.unique r₂ r hr₂.1 hr₂.2 hr hract h1 h2]
      rw [if_pos hact]
      exact flatMap_key_unique _ _ _ hnd hmem hun
        (by simp only [decide_eq_true_eq]; exact ⟨hts, hhid⟩)
    · rw [if_neg hact]
      refine List.flatMap_eq_nil_iff.mpr (fun ρ hρ => ?_)
      have hn := hostb_inactive_nil H hr' hact
      have hz : rowMsgs HostB.table tr pub 25 r' busStk s = [] := by
        cases s
        · exact hn.2
        · exact hn.1
      simp only [hz, ite_self]
  -- step 3: swap the two flatMaps (up to `Perm`) and apply `key` pointwise
  have swap : List.Perm
      ((hostActRows tr pub).flatMap (fun ρ =>
        (List.range (tr.height 25)).flatMap (fun r' =>
          if (decide (rowNat tr 25 r' HostB.ts = rowNat tr 22 ρ.2 cTs ∧
              rowNat tr 25 r' HostB.hid = rowNat tr 22 ρ.2 Host.hid)) = true
          then rowMsgs HostB.table tr pub 25 r' busStk s else [])))
      ((List.range (tr.height 25)).flatMap (fun r' =>
          (hostActRows tr pub).flatMap (fun ρ =>
            if (decide (rowNat tr 25 r' HostB.ts = rowNat tr 22 ρ.2 cTs ∧
                rowNat tr 25 r' HostB.hid = rowNat tr 22 ρ.2 Host.hid)) = true
            then rowMsgs HostB.table tr pub 25 r' busStk s else []))) :=
    perm_flatMap_swap _ _ _
  refine List.Perm.trans (List.Perm.of_eq e1) (List.Perm.trans swap ?_)
  refine List.Perm.of_eq (flatMap_congr_on _ _ _ ?_)
  intro r' hr'
  exact key r' hr'

/-! ## The partition, decoded, on each side

`hostb_partition` is stated over raw `rowMsgs` lists (`List (List F)`); the CH bus and the row
accessors are stated over decoded `Msg`s.  These two lemmas push `decMsg` through the partition so
the fused fold can be compared with the table's block directly. -/

/-- **The partition, decoded, on the produced side.** -/
theorem hostb_partition_prod {nloc ngl : Nat} {tr : Trace} {pub : List F}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (hb : HostBLinked tr pub) :
    List.Perm ((hostActRows tr pub).flatMap (fun ρ => hostbProdOf tr pub ρ.2))
      ((part HostB.table tr pub 25 busStk true).map decMsg) := by
  have h := (hostb_partition (tr := tr) (pub := pub) H hb true).map decMsg
  -- both sides of `h`, re-expressed over `rowProd` (definitionally `(rowMsgs …).map decMsg`)
  have e1 : ((hostActRows tr pub).flatMap (fun ρ => (hostbOf tr pub ρ.2).flatMap
      fun r' => rowMsgs HostB.table tr pub 25 r' busStk true)).map decMsg
      = (hostActRows tr pub).flatMap (fun ρ => hostbProdOf tr pub ρ.2) := by
    rw [List.map_flatMap]
    refine flatMap_congr_on _ _ _ ?_
    intro ρ _
    rw [List.map_flatMap]
    rfl
  have e2 : (((List.range (tr.height 25)).flatMap (fun r' =>
      if rowAct HostB.table tr pub 25 r' then rowMsgs HostB.table tr pub 25 r' busStk true
      else [])).map decMsg)
      = (part HostB.table tr pub 25 busStk true).map decMsg := by
    have e2a : (List.range (tr.height 25)).flatMap (fun r' =>
        if rowAct HostB.table tr pub 25 r' then rowMsgs HostB.table tr pub 25 r' busStk true
        else [])
        = (List.range (tr.height 25)).flatMap (fun r' =>
          rowMsgs HostB.table tr pub 25 r' busStk true) := by
      refine flatMap_congr_on _ _ _ ?_
      intro r hr
      rw [List.mem_range] at hr
      by_cases hact : rowAct HostB.table tr pub 25 r
      · rw [if_pos hact]
      · rw [if_neg hact, (hostb_inactive_nil H hr hact).1]
    rw [e2a, hostb_part_ch_send, List.map_flatMap]
    refine flatMap_congr_on _ _ _ ?_
    intro r _
    rfl
  rw [← e1, ← e2]
  exact h

/-- **The partition, decoded, on the consumed side.** -/
theorem hostb_partition_cons {nloc ngl : Nat} {tr : Trace} {pub : List F}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (hb : HostBLinked tr pub) :
    List.Perm ((hostActRows tr pub).flatMap (fun ρ => hostbConsOf tr pub ρ.2))
      ((part HostB.table tr pub 25 busStk false).map decMsg) := by
  have h := (hostb_partition (tr := tr) (pub := pub) H hb false).map decMsg
  have e1 : ((hostActRows tr pub).flatMap (fun ρ => (hostbOf tr pub ρ.2).flatMap
      fun r' => rowMsgs HostB.table tr pub 25 r' busStk false)).map decMsg
      = (hostActRows tr pub).flatMap (fun ρ => hostbConsOf tr pub ρ.2) := by
    rw [List.map_flatMap]
    refine flatMap_congr_on _ _ _ ?_
    intro ρ _
    rw [List.map_flatMap]
    rfl
  have e2 : (((List.range (tr.height 25)).flatMap (fun r' =>
      if rowAct HostB.table tr pub 25 r' then rowMsgs HostB.table tr pub 25 r' busStk false
      else [])).map decMsg)
      = (part HostB.table tr pub 25 busStk false).map decMsg := by
    have e2a : (List.range (tr.height 25)).flatMap (fun r' =>
        if rowAct HostB.table tr pub 25 r' then rowMsgs HostB.table tr pub 25 r' busStk false
        else [])
        = (List.range (tr.height 25)).flatMap (fun r' =>
          rowMsgs HostB.table tr pub 25 r' busStk false) := by
      refine flatMap_congr_on _ _ _ ?_
      intro r hr
      rw [List.mem_range] at hr
      by_cases hact : rowAct HostB.table tr pub 25 r
      · rw [if_pos hact]
      · rw [if_neg hact, (hostb_inactive_nil H hr hact).2]
    rw [e2a, hostb_part_ch_recv, List.map_flatMap]
    refine flatMap_congr_on _ _ _ ?_
    intro r _
    rfl
  rw [← e1, ← e2]
  exact h

/-! ## The fused fold, as the raw block order

`ch_raw_host` (`Main/HostBus`) presents the CH bus with the HOST block **fused with** its `HOSTB`
block: `Hh ++ Hb` on the produced side, `Hc ++ Hc'` on the consumed side.  These two lemmas say the
fold `prodCH`/`consCH` over `actListHost` is exactly that fused block, so `perm_ch_host` applies
without further bookkeeping. -/

/-- **The produced fold is the raw fused block.** -/
theorem flatMap_prodCH_perm {nloc ngl : Nat} {tr : Trace} {pub : List F}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (hb : HostBLinked tr pub) :
    List.Perm ((actListHost tr pub).flatMap (prodCH tr pub))
      ((actList tr pub).flatMap
          (fun ρ => (rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk true).map decMsg) ++
        ((hostActRows tr pub).flatMap (rowProdH tr pub) ++
          (part HostB.table tr pub 25 busStk true).map decMsg)) := by
  have h1 : List.Perm ((actListHost tr pub).flatMap (prodCH tr pub))
      ((actListHost tr pub).flatMap (rowProdH tr pub) ++
        (actListHost tr pub).flatMap (hostbProdH tr pub)) :=
    perm_flatMap_append _ _ _
  rw [actListHost_flatMap_prod, actListHost_hostb_prod] at h1
  refine List.Perm.trans h1 ?_
  refine List.Perm.trans (List.Perm.append_left _ (hostb_partition_prod H hb)) ?_
  exact List.Perm.of_eq (List.append_assoc _ _ _)

/-- **The consumed fold is the raw fused block.** -/
theorem flatMap_consCH_perm {nloc ngl : Nat} {tr : Trace} {pub : List F}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr) (hb : HostBLinked tr pub) :
    List.Perm ((actListHost tr pub).flatMap (consCH tr pub))
      ((actList tr pub).flatMap
          (fun ρ => (rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk false).map decMsg) ++
        ((hostActRows tr pub).flatMap (rowConsH tr pub) ++
          (part HostB.table tr pub 25 busStk false).map decMsg)) := by
  have h1 : List.Perm ((actListHost tr pub).flatMap (consCH tr pub))
      ((actListHost tr pub).flatMap (rowConsH tr pub) ++
        (actListHost tr pub).flatMap (hostbConsH tr pub)) :=
    perm_flatMap_append _ _ _
  rw [actListHost_flatMap_cons, actListHost_hostb_cons] at h1
  refine List.Perm.trans h1 ?_
  refine List.Perm.trans (List.Perm.append_left _ (hostb_partition_cons H hb)) ?_
  exact List.Perm.of_eq (List.append_assoc _ _ _)

/-! ## The `hch`/`hst` premises of `wasm_base_exec_host`, fused

These are the replacements for the lemmas the fold commit deleted from `Main/HostBus`: the only
change is the fused `prodCH`/`consCH` in place of `rowProdH`/`rowConsH`, and the extra premise
`HostBLinked` that makes the fusion a partition. -/

/-- **`hch` for `wasm_base_exec_host`, discharged from `Holds` plus `HostBLinked`.**  The free
initial/final blocks are the boundary's: `init = I G B M` and `fin = (R F) D`.  `perm_ch_host` moves
the active HOST rows next to the instruction rows on both sides; `flatMap_prodCH_perm` /
`flatMap_consCH_perm` supply the fused block order. -/
theorem host_hch {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr)
    (hb : HostBLinked tr pub) :
    (((initRaw nloc pub).map decMsg ++
        ((globRaw nloc ngl pub).map decMsg ++
          ((budRaw nloc ngl pub).map decMsg ++ (memRaw tr pub).map decMsg))) ++
        (actListHost tr pub).flatMap (prodCH tr pub)).Perm
      (((((if X.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) then
              [resRaw pub tr] else []).map decMsg ++ (finRaw nloc tr).map decMsg) ++
          (drainRaw tr pub).map decMsg)) ++
        (actListHost tr pub).flatMap (consCH tr pub)) := by
  obtain ⟨e1, e2⟩ := ch_raw_host H H0 hpub CF
  have hc := (host_msgs_ch_perm H H0 hpub CF).map decMsg
  rw [e1, e2] at hc
  refine List.Perm.trans (List.Perm.append_left _
    (flatMap_prodCH_perm (nloc := nloc) (ngl := ngl) H hb)) ?_
  refine List.Perm.trans ?_ (List.Perm.append_left _
    (flatMap_consCH_perm (nloc := nloc) (ngl := ngl) H hb).symm)
  exact perm_ch_host _ _ _ _ _ _ _ _ _ _ _ hc

/-- **Both bus premises of `wasm_base_exec_host`, from `Holds` and `HostBLinked`.**  The free
`init`/`fin` blocks are the boundary's (`I G B M` / `(R F) D`); this is the pair the composition
step instantiates. -/
theorem host_buses {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr)
    (hb : HostBLinked tr pub) :
    (stMsg 0 1 0 0 0 0 :: (actListHost tr pub).map (rowOutH tr pub)).Perm
        ([tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
          pub.getD Boundary.pubStatus 0, tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf] ::
          (actListHost tr pub).map (rowInH tr pub)) ∧
      ((((initRaw nloc pub).map decMsg ++
          ((globRaw nloc ngl pub).map decMsg ++
            ((budRaw nloc ngl pub).map decMsg ++ (memRaw tr pub).map decMsg))) ++
          (actListHost tr pub).flatMap (prodCH tr pub))).Perm
        ((((if X.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) then
                [resRaw pub tr] else []).map decMsg ++ (finRaw nloc tr).map decMsg) ++
            (drainRaw tr pub).map decMsg) ++
          (actListHost tr pub).flatMap (consCH tr pub)) :=
  ⟨host_hst H H0 hpub CF, host_hch H H0 hpub CF hb⟩

end WasmBase
