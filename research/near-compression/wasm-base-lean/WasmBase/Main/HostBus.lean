import WasmBase.Main.ExecHost
import WasmBase.Main.SegHarness
import WasmBase.Main.HostChipBits
import WasmBase.Main.Lookups

/-!
# WasmBase.Main.HostBus — the STATE/CH bus decompositions of `wasmBaseHostAir`

`wasm_base_exec_host` (`Main/SegHarness.lean`) takes the STATE- and CH-bus `Perm`s (`hst`, `hch`) as
hypotheses.  **Both are discharged here from `Holds`** (`host_hst`, `host_hch`, and their pair
`host_buses`), so nothing but the AIR relation is left to assume on the bus side.

## Shape

`msgs_state_host` / `msgs_ch_host` (`Main/ExecHost.lean`) split the host AIR's messages into the
base AIR's plus the HOST table's.  `msgs_state` / `msgs_ch` (`Main/Exec.lean`) express the base
AIR's.  Composing, and using `msgs_perm` on each bus, gives

* `host_msgs_state_perm` — the STATE bus is a permutation of the initial message plus the action
  rows' `rowOutH`s against the final message plus the `rowInH`s;
* `host_msgs_ch_perm` — the CH bus likewise, with the initial/final raw message blocks.

Both are stated against `actListHost`, the list `wasm_base_exec_host` uses, so they plug straight in.

## The CH side is not the STATE side

`msgs_ch_host` gives the HOST table's CH messages as a `flatMap` over **all** its rows, but the
induction lists only the **active** ones (`hostActRows`).  Two things close that:

1. `host_trace_ok` (`Main/HostChipFacts.lean`) turns the `act`-gating constraints into `HostTraceOK`,
   so inactive rows contribute nothing; `host_part_ch_recv_active` / `_send_active` then rewrite the
   HOST block to the active rows' `rowCons`/`rowProd`, and `hostActRows_cons`/`_prod` restate it as
   `hostActRows.flatMap`.
2. The HOST block is interleaved differently on the two sides (`msgs_ch` puts the memory block after
   the instruction rows on the true side and the drain block after them on the false side), so
   `perm_ch_host` needs one `perm_mid` swap per side to move the HOST block next to the instruction
   rows.  That is the bookkeeping `List.flatMap_map` could not do directly.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Local
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000

/-! ## `rowOutH`/`rowInH` agree with the base accessors off table 22 -/

theorem rowOutH_eq_of_ne {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ.1 ≠ 22) :
    rowOutH tr pub ρ = rowOut (chipT ρ.1) tr pub ρ.1 ρ.2 := by
  simp [rowOutH, chipTHost, h]

theorem rowInH_eq_of_ne {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ.1 ≠ 22) :
    rowInH tr pub ρ = rowIn (chipT ρ.1) tr pub ρ.1 ρ.2 := by
  simp [rowInH, chipTHost, h]

theorem rowOutH_eq_host {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ.1 = 22) :
    rowOutH tr pub ρ = rowOut Host.table tr pub 22 ρ.2 := by
  simp [rowOutH, chipTHost, h]

theorem rowInH_eq_host {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ.1 = 22) :
    rowInH tr pub ρ = rowIn Host.table tr pub 22 ρ.2 := by
  simp [rowInH, chipTHost, h]

/-- The instruction rows of `actList` are not HOST rows. -/
theorem actList_ne_host {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ ∈ actList tr pub) :
    ρ.1 ≠ 22 := by
  obtain ⟨h1, h9, -⟩ := mem_actList h
  omega

/-- The HOST rows of `hostActRows` are HOST rows. -/
theorem hostActRows_eq_host {tr : Trace} {pub : List F} {ρ : Nat × Nat} (h : ρ ∈ hostActRows tr pub) :
    ρ.1 = 22 := by
  simp only [hostActRows, List.mem_map] at h
  obtain ⟨r, _, rfl⟩ := h
  rfl

/-! ## The STATE bus -/

/-- `actListHost` split into its two parts, with the accessors specialised. -/
theorem actListHost_map_out (tr : Trace) (pub : List F) :
    (actListHost tr pub).map (rowOutH tr pub) =
      (actList tr pub).map (fun ρ => rowOut (chipT ρ.1) tr pub ρ.1 ρ.2) ++
        (hostActRows tr pub).map (fun ρ => rowOut Host.table tr pub 22 ρ.2) := by
  unfold actListHost
  rw [List.map_append]
  congr 1
  · refine List.map_congr_left fun ρ hρ => ?_
    exact rowOutH_eq_of_ne (actList_ne_host hρ)
  · refine List.map_congr_left fun ρ hρ => ?_
    exact rowOutH_eq_host (hostActRows_eq_host hρ)

/-- The same for the inputs. -/
theorem actListHost_map_in (tr : Trace) (pub : List F) :
    (actListHost tr pub).map (rowInH tr pub) =
      (actList tr pub).map (fun ρ => rowIn (chipT ρ.1) tr pub ρ.1 ρ.2) ++
        (hostActRows tr pub).map (fun ρ => rowIn Host.table tr pub 22 ρ.2) := by
  unfold actListHost
  rw [List.map_append]
  congr 1
  · refine List.map_congr_left fun ρ hρ => ?_
    exact rowInH_eq_of_ne (actList_ne_host hρ)
  · refine List.map_congr_left fun ρ hρ => ?_
    exact rowInH_eq_host (hostActRows_eq_host hρ)

/-- **The HOST rows' outputs**, as the `msgs_state_host` flatMap produces them. -/
theorem hostActRows_rowOut (tr : Trace) (pub : List F) :
    (hostActRows tr pub).map (fun ρ => rowOut Host.table tr pub 22 ρ.2) =
      (List.range (tr.height 22)).flatMap (fun r =>
        if rowAct Host.table tr pub 22 r then [rowOut Host.table tr pub 22 r] else []) := by
  unfold hostActRows
  induction (List.range (tr.height 22)) with
  | nil => rfl
  | cons a l ih =>
    by_cases h : rowAct Host.table tr pub 22 a <;> simp [h, ih]

/-- **The HOST rows' inputs**, likewise. -/
theorem hostActRows_rowIn (tr : Trace) (pub : List F) :
    (hostActRows tr pub).map (fun ρ => rowIn Host.table tr pub 22 ρ.2) =
      (List.range (tr.height 22)).flatMap (fun r =>
        if rowAct Host.table tr pub 22 r then [rowIn Host.table tr pub 22 r] else []) := by
  unfold hostActRows
  induction (List.range (tr.height 22)) with
  | nil => rfl
  | cons a l ih =>
    by_cases h : rowAct Host.table tr pub 22 a <;> simp [h, ih]

/-! ## The active HOST rows as a `flatMap`

`msgs_ch_host` gives the HOST table's CH messages as a `flatMap` over **all** rows; the induction
only lists the **active** ones (`hostActRows`).  `hostActRows_flatMap` is the congruence that moves
between the two forms, and `hostActRows_prod` / `hostActRows_cons` specialise it to the CH sends and
receives. -/

/-- **`hostActRows` as a filtered `flatMap`.**  A `flatMap` over the active rows is the same as one
over all rows with the inactive ones contributing `[]`. -/
theorem hostActRows_flatMap {β : Type} (tr : Trace) (pub : List F) (f : Nat → List β) :
    (hostActRows tr pub).flatMap (fun ρ => f ρ.2) =
      (List.range (tr.height 22)).flatMap (fun r =>
        if rowAct Host.table tr pub 22 r then f r else []) := by
  unfold hostActRows
  induction (List.range (tr.height 22)) with
  | nil => rfl
  | cons a l ih =>
    by_cases h : rowAct Host.table tr pub 22 a <;> simp [h, ih]

/-- **The HOST rows' CH sends**, in the active-row form. -/
theorem hostActRows_prod (tr : Trace) (pub : List F) :
    (hostActRows tr pub).flatMap (rowProdH tr pub) =
      (List.range (tr.height 22)).flatMap (fun r =>
        if rowAct Host.table tr pub 22 r then
          (if rowNat tr 22 r Host.nres = 1 then [wordMsg tr r] else []) else []) := by
  rw [← hostActRows_flatMap (tr := tr) (pub := pub)
    (f := fun r => if rowNat tr 22 r Host.nres = 1 then [wordMsg tr r] else [])]
  refine flatMap_congr_on _ _ _ ?_
  intro ρ hρ
  obtain ⟨t, r⟩ := ρ
  obtain rfl : t = 22 := hostActRows_eq_host hρ
  have hp : rowProdH tr pub (22, r) = rowProd Host.table tr pub 22 r := by
    simp [rowProdH, chipTHost]
  rw [hp, host_row_prod]

/-- **The HOST rows' CH receives**, in the active-row form. -/
theorem hostActRows_cons (tr : Trace) (pub : List F) :
    (hostActRows tr pub).flatMap (rowConsH tr pub) =
      (List.range (tr.height 22)).flatMap (fun r =>
        if rowAct Host.table tr pub 22 r then
          (Host.argRange.flatMap fun j =>
            (if rowNat tr 22 r (Host.pf j) = 1 then [argMsg tr r j] else [])) else []) := by
  rw [← hostActRows_flatMap (tr := tr) (pub := pub)
    (f := fun r => Host.argRange.flatMap fun j =>
      (if rowNat tr 22 r (Host.pf j) = 1 then [argMsg tr r j] else []))]
  refine flatMap_congr_on _ _ _ ?_
  intro ρ hρ
  obtain ⟨t, r⟩ := ρ
  obtain rfl : t = 22 := hostActRows_eq_host hρ
  have hc : rowConsH tr pub (22, r) = rowCons Host.table tr pub 22 r := by
    simp [rowConsH, chipTHost]
  rw [hc, host_row_cons]

/-- **`actListHost`'s CH sends split** into the instruction rows' and the HOST rows'. -/
theorem actListHost_flatMap_prod (tr : Trace) (pub : List F) :
    (actListHost tr pub).flatMap (rowProdH tr pub) =
      (actList tr pub).flatMap
          (fun ρ => (rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk true).map decMsg) ++
        (hostActRows tr pub).flatMap (rowProdH tr pub) := by
  unfold actListHost
  rw [List.flatMap_append]
  congr 1
  refine flatMap_congr_on _ _ _ ?_
  intro ρ hρ
  obtain ⟨t, r⟩ := ρ
  have hne : t ≠ 22 := actList_ne_host hρ
  simp only [rowProdH, chipTHost, hne, if_false, rowProd]

/-- **`actListHost`'s CH receives split** likewise. -/
theorem actListHost_flatMap_cons (tr : Trace) (pub : List F) :
    (actListHost tr pub).flatMap (rowConsH tr pub) =
      (actList tr pub).flatMap
          (fun ρ => (rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk false).map decMsg) ++
        (hostActRows tr pub).flatMap (rowConsH tr pub) := by
  unfold actListHost
  rw [List.flatMap_append]
  congr 1
  refine flatMap_congr_on _ _ _ ?_
  intro ρ hρ
  obtain ⟨t, r⟩ := ρ
  have hne : t ≠ 22 := actList_ne_host hρ
  simp only [rowConsH, chipTHost, hne, if_false, rowCons]

/-! ## The two association permutations the `ch` side needs -/

/-- A block `P` sitting before `M` moves after it (with the tail `S` kept in place). -/
theorem perm_mid {α : Type} (P M S : List α) : (P ++ (M ++ S)).Perm (M ++ (P ++ S)) := by
  rw [← List.append_assoc P M S, ← List.append_assoc M P S]
  exact (List.perm_append_comm (l₁ := P) (l₂ := M)).append_right S

/-- The true side of the CH bus: `I G B P (M S)` rearranges to `(I G B M) (P S)`. -/
theorem perm_true_host {α : Type} (I G B P M S : List α) :
    (I ++ (G ++ (B ++ (P ++ (M ++ S))))).Perm ((I ++ (G ++ (B ++ M))) ++ (P ++ S)) := by
  have h : (I ++ (G ++ (B ++ (P ++ (M ++ S))))).Perm
      (I ++ (G ++ (B ++ (M ++ (P ++ S))))) :=
    List.Perm.append_left I (List.Perm.append_left G (List.Perm.append_left B (perm_mid P M S)))
  simpa only [List.append_assoc] using h

/-- The false side of the CH bus: `((A C) D) E` rearranges to `(A D) (C E)`. -/
theorem perm_false_host {α : Type} (A C D E : List α) :
    (((A ++ C) ++ D) ++ E).Perm ((A ++ D) ++ (C ++ E)) := by
  have h : (((A ++ C) ++ D) ++ E).Perm (((A ++ D) ++ C) ++ E) :=
    (perm_swap3 A C D).append_right E
  simpa only [List.append_assoc] using h

/-- The false side with the result/final block fused: `((A C) D) E` rearranges to `(A D) (C E)`. -/
theorem perm_false_host5 {α : Type} (A B C D E : List α) :
    ((((A ++ B) ++ C) ++ D) ++ E).Perm (((A ++ B) ++ D) ++ (C ++ E)) :=
  perm_false_host (A ++ B) C D E

/-! ## The two bus permutations -/

/-- **The STATE bus of a host trace is a permutation** of `initMsg :: outputs` against
`finalMsg :: inputs`, with the action rows being `actListHost`.  This is the `hst` premise of
`wasm_base_exec_host`. -/
theorem host_msgs_state_perm {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr) :
    (msgs (wasmBaseHostAir nloc ngl) tr pub busState true).Perm
      (msgs (wasmBaseHostAir nloc ngl) tr pub busState false) :=
  msgs_perm H busState
    (fun o ho hk => occ_bits_host H H0 hpub CF o ho (Or.inl hk))

/-- **The CH bus of a host trace is a permutation.**  This is the `hch` premise. -/
theorem host_msgs_ch_perm {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr) :
    (msgs (wasmBaseHostAir nloc ngl) tr pub busStk true).Perm
      (msgs (wasmBaseHostAir nloc ngl) tr pub busStk false) :=
  msgs_perm H busStk
    (fun o ho hk => occ_bits_host H H0 hpub CF o ho (Or.inr hk))

/-! ## The `hst`/`hch` premises of `wasm_base_exec_host`

`wasm_base_exec_host` wants the perms in terms of `actListHost` and the `rowOutH`/`rowInH`
accessors.  These two lemmas rewrite the `msgs` perms above into that form. -/

/-- `msgs` on the STATE bus, expanded over `actListHost`. -/
theorem msgs_state_host_expand {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr) (hpub : PubOK X nloc ngl pub) :
    msgs (wasmBaseHostAir nloc ngl) tr pub busState true =
      stMsg 0 1 0 0 0 0 :: (actListHost tr pub).map (rowOutH tr pub) ∧
    msgs (wasmBaseHostAir nloc ngl) tr pub busState false =
      [tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
        pub.getD Boundary.pubStatus 0, tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf] ::
        (actListHost tr pub).map (rowInH tr pub) := by
  obtain ⟨ms1, ms2⟩ := msgs_state H0 hpub
  obtain ⟨mh1, mh2⟩ := msgs_state_host (nloc := nloc) (ngl := ngl) tr pub
  constructor
  · rw [mh1, ms1, actListHost_map_out, hostActRows_rowOut]
    simp only [List.cons_append, List.nil_append]
  · rw [mh2, ms2, actListHost_map_in, hostActRows_rowIn]
    simp only [List.cons_append, List.nil_append]

/-- **`hst` for `wasm_base_exec_host`, discharged from `Holds`.** -/
theorem host_hst {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr) :
    (stMsg 0 1 0 0 0 0 :: (actListHost tr pub).map (rowOutH tr pub)).Perm
      ([tr.cell 0 0 Boundary.pcf, pub.getD Boundary.pubN 0, pub.getD Boundary.pubS 0,
        pub.getD Boundary.pubStatus 0, tr.cell 0 0 Boundary.sbf, tr.cell 0 0 Boundary.cidf] ::
        (actListHost tr pub).map (rowInH tr pub)) := by
  obtain ⟨e1, e2⟩ := msgs_state_host_expand (X := X) H0 hpub
  rw [← e1, ← e2]
  exact host_msgs_state_perm H H0 hpub CF


/-! ## The CH bus, expanded over `actListHost`

`msgs_ch` (`Main/Exec.lean`) writes the base CH bus as

```
true :  (I ++ (G ++ (B ++ (A_true ++ M))))        -- initRaw, glob, budget, act rows, memRaw
false:  (((R ++ F) ++ A_false) ++ D)              -- result, final, act rows, drain
```

where `I`/`G`/`B`/`M`/`R`/`F`/`D` are the raw boundary blocks and `A_*` the instruction rows'
messages.  `msgs_ch_host` appends the HOST and HOSTB tables'.  `host_part_ch_recv_active` /
`host_part_ch_send_active` (via `HostTraceOK`, discharged by `host_trace_ok`) rewrite the HOST block
to the **active** rows' `rowProdH`/`rowConsH`; `actListHost_flatMap_prod`/`_cons` then split the
`actListHost` block back into instruction rows and HOST rows.

`ch_raw_host` states the result in the fully right-associated shape, with the `HOSTB` block after the
HOST block on both sides; `host_hch` is then two `perm_mid` swaps (the HOST blocks cross the memory /
drain block) between it and the `actListHost` form `wasm_base_exec_host` asks for. -/

/-- The host AIR's CH bus, decoded, right-associated over `I G B A M H` / `R F A D H`:
`I` = `initRaw`, `G` = `globRaw`, `B` = `budRaw(== budget)`, `A` = instruction rows, `M` = `memRaw`,
`H` = active HOST rows, `R` = result, `F` = `finRaw`, `D` = `drainRaw`. -/
theorem ch_raw_host {X : Ctx} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    (H : Holds (wasmBaseHostAir nloc ngl) pub tr)
    (H0 : Holds (wasmBaseAir nloc ngl) pub tr)
    (hpub : PubOK X nloc ngl pub) (CF : ChipFacts X nloc ngl pub tr) :
    (msgs (wasmBaseHostAir nloc ngl) tr pub busStk true).map decMsg =
      (initRaw nloc pub).map decMsg ++
        ((globRaw nloc ngl pub).map decMsg ++
          ((budRaw nloc ngl pub).map decMsg ++
            ((actList tr pub).flatMap
                (fun ρ => (rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk true).map decMsg) ++
              ((memRaw tr pub).map decMsg ++
                ((hostActRows tr pub).flatMap (rowProdH tr pub) ++
                  (part HostB.table tr pub 25 busStk true).map decMsg))))) ∧
    (msgs (wasmBaseHostAir nloc ngl) tr pub busStk false).map decMsg =
      ((if X.ck.arity = 1 ∧ pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) then
          [resRaw pub tr] else []).map decMsg ++
        ((finRaw nloc tr).map decMsg ++
          ((actList tr pub).flatMap
              (fun ρ => (rowMsgs (chipT ρ.1) tr pub ρ.1 ρ.2 busStk false).map decMsg) ++
            ((drainRaw tr pub).map decMsg ++
              ((hostActRows tr pub).flatMap (rowConsH tr pub) ++
                (part HostB.table tr pub 25 busStk false).map decMsg))))) := by
  obtain ⟨mc1, mc2⟩ := msgs_ch H0 hpub CF
  obtain ⟨mh1, mh2⟩ := msgs_ch_host (nloc := nloc) (ngl := ngl) tr pub
  have hTS := host_trace_ok H
  have hsnd := host_part_ch_send_active H hTS
  have hrcv := host_part_ch_recv_active H hTS
  constructor
  · rw [mh1]
    simp only [List.map_append]
    rw [mc1]
    simp only [List.map_append, List.map_flatMap]
    rw [hsnd, ← hostActRows_prod]
    simp only [List.append_assoc]
  · rw [mh2]
    simp only [List.map_append]
    rw [mc2]
    simp only [List.map_append, List.map_flatMap]
    rw [hrcv, ← hostActRows_cons]
    simp only [List.append_assoc]

/-- **The association step from the raw CH order to the `actListHost` order.**  The raw form has the
HOST block `Hh` after the memory block `M` (and `Hc` after the drain block `D`); the induction's form
has both blocks adjacent to the instruction rows.  Each side is one `perm_mid` swap.

`Hh`/`Hc` are the host rows' own messages **fused with** the `HOSTB` block of the same call
(`Hh = Hhost ++ Hb`, `Hc = Hhost' ++ Hb'`), which is exactly how the fold `prodCH`/`consCH` presents
them: the fusion is by construction, so this lemma is stated over the fused lists. -/
theorem perm_ch_host {α : Type} (I G B A M Hh R F Ac D Hc : List α) :
    (I ++ (G ++ (B ++ (A ++ (M ++ Hh))))).Perm (R ++ (F ++ (Ac ++ (D ++ Hc)))) →
    ((I ++ (G ++ (B ++ M))) ++ (A ++ Hh)).Perm (((R ++ F) ++ D) ++ (Ac ++ Hc)) := by
  intro h
  have s1 : (I ++ (G ++ (B ++ (A ++ (M ++ Hh))))).Perm
      (I ++ (G ++ (B ++ (M ++ (A ++ Hh))))) :=
    List.Perm.append_left I (List.Perm.append_left G
      (List.Perm.append_left B (perm_mid A M Hh)))
  have s3 : (R ++ (F ++ (Ac ++ (D ++ Hc)))).Perm (R ++ (F ++ (D ++ (Ac ++ Hc)))) :=
    List.Perm.append_left R (List.Perm.append_left F (perm_mid Ac D Hc))
  have e1' : ((I ++ (G ++ (B ++ M))) ++ (A ++ Hh)) =
      (I ++ (G ++ (B ++ (M ++ (A ++ Hh))))) := by simp [List.append_assoc]
  have e2' : (((R ++ F) ++ D) ++ (Ac ++ Hc)) =
      (R ++ (F ++ (D ++ (Ac ++ Hc)))) := by simp [List.append_assoc]
  rw [e1', e2']
  exact s1.symm.trans (h.trans s3)

end WasmBase
