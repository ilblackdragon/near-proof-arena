import StateM5a.BrOslSplit

/-!
# StateM5a.SnSplitBus — the split protocol's messages on the `SN` side (`SPR`, `EPQ`, `SXQ`/`SXR`)

* Message lists and single-sender facts: `SPR` is sent by `BR.oSL` and `SN.oEP` only
  (`spr_src`), `EPQ` by the `SN` split rows only (`epq_src`), `SXR` by `SN.oEM` only (`sxr_src`),
  `SXQ` by the `SN` extension-split rows only (`sxq_src`).
* `snQ`: a split row's request decoded from its own columns; `oslQ_eq`: the `oSL` row that received
  its `SPQ` decodes the same request (`BrOslSplit.oslQ`).
-/

namespace StateM5a.SnSplitBus

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.KcChain StateM5a.KeyDecode
open StateM5a.RowSn StateM5a.RowSnMsg StateM5a.BrSib StateM5a.BrMat StateM5a.BrRange StateM5a.WalkEnd
open StateM5a.KeyLookups StateM5a.BrOsl StateM5a.BrOslSplit

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Messages -/

def snSprR : List Expr :=
  [Sn.c "w", Sn.c "d", Sn.c "shf"] ++ ((List.range 16).map fun i => Sn.c "sh" i) ++
    (List.range 4).map fun t => Sn.c "sm" t
def snSprS : List Expr := [Sn.c "w", Sn.c "d", Sn.c "nref"] ++ pack2 (fun b => Sn.c "hn" b) ++ Sn.NM
def brSprS : List Expr := [Br.c "w", Br.c "d", Br.c "nref"] ++ pack2 (fun b => Br.c "hn" b) ++ Br.NM
def snSprP : List Expr :=
  [Sn.c "w", Sn.c "d" + Sn.c "klen", Sn.c "nxf"] ++ pack2 (fun b => Sn.c "nx" b) ++
    (List.range 4).map fun t => Sn.c "unm" t
def snEpqS : List Expr := [Sn.c "w", Sn.c "d", Sn.c "d" + Sn.c "jm", Sn.c "kid"]
def snEpqR : List Expr := [Sn.c "w", Sn.c "d", Sn.c "d" + Sn.c "klen", Sn.c "kid"]
def snSxqS : List Expr :=
  [Sn.c "w", Sn.c "d" + Sn.c "jm" + 1, Sn.c "kid2", Sn.c "d" + Sn.c "klen", Sn.c "xf"] ++
    pack2 (fun b => Sn.c "x" b) ++ Sn.CM
def snSxqR : List Expr :=
  [Sn.c "w", Sn.c "d", Sn.c "kid", Sn.c "d" + Sn.c "klen", Sn.c "nxf"] ++ pack2 (fun b => Sn.c "nx" b) ++
    (List.range 4).map fun t => Sn.c "unm" t
def snSxrS : List Expr := [Sn.c "w", Sn.c "d", Sn.c "kid", Sn.c "nref"] ++ pack2 (fun b => Sn.c "hn" b) ++ Sn.NM
def snSxrR : List Expr :=
  [Sn.c "w", Sn.c "d" + Sn.c "jm" + 1, Sn.c "kid2", Sn.c "sxhf"] ++ ((List.range 16).map fun i => Sn.c "sxh" i) ++
    (List.range 4).map fun t => Sn.c "sxm" t

theorem sn_spr_s : Sn.interactions.filter (fun i => decide (i.bus = B_SPR ∧ i.send = true)) =
    [snd B_SPR (Sn.c "oEP") snSprS] := by decide
theorem br_spr_s : Br.interactions.filter (fun i => decide (i.bus = B_SPR ∧ i.send = true)) =
    [snd B_SPR (Br.c "oSL") brSprS] := by decide
theorem sn_spr_rX : rcv B_SPR Sn.gX snSprR ∈ Sn.interactions := memD_mem (by decide)
theorem sn_spr_rP : rcv B_SPR (Sn.c "oEP") snSprP ∈ Sn.interactions := memD_mem (by decide)
theorem sn_epq_s : Sn.interactions.filter (fun i => decide (i.bus = B_EPQ ∧ i.send = true)) =
    [snd B_EPQ (Sn.gX * (1 - Sn.c "j0")) snEpqS] := by decide
theorem sn_epq_r : rcv B_EPQ (Sn.c "oEP") snEpqR ∈ Sn.interactions := memD_mem (by decide)
theorem sn_sxq_s : Sn.interactions.filter (fun i => decide (i.bus = B_SXQ ∧ i.send = true)) =
    [snd B_SXQ (Sn.c "oEX" * (1 - Sn.c "z")) snSxqS] := by decide
theorem sn_sxq_r : rcv B_SXQ (Sn.c "oEM") snSxqR ∈ Sn.interactions := memD_mem (by decide)
theorem sn_sxr_s : Sn.interactions.filter (fun i => decide (i.bus = B_SXR ∧ i.send = true)) =
    [snd B_SXR (Sn.c "oEM") snSxrS] := by decide
theorem sn_sxr_r : rcv B_SXR (Sn.c "oEX" * (1 - Sn.c "z")) snSxrR ∈ Sn.interactions := memD_mem (by decide)

theorem spr_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 2 → t ≠ 3 →
    sendsOn ((m5aAir D).tables[t]).interactions B_SPR = false
  | 0, _, _, _ => by show sendsOn shaTable.interactions B_SPR = false; decide
  | 1, _, _, _ => by show sendsOn Key.interactions B_SPR = false; decide
  | 2, _, h, _ => absurd rfl h
  | 3, _, _, h => absurd rfl h
  | 4, _, _, _ => by show sendsOn Kcmp.interactions B_SPR = false; decide
  | 5, _, _, _ => by show sendsOn Wsb.interactions B_SPR = false; decide
  | 6, _, _, _ => by show sendsOn Wsn.interactions B_SPR = false; decide
  | 7, _, _, _ => by show sendsOn Wsa.interactions B_SPR = false; decide
  | 8, _, _, _ => by show sendsOn Snc.interactions B_SPR = false; decide
  | 9, _, _, _ => by show sendsOn Rng.interactions B_SPR = false; decide
  | 10, _, _, _ => by show sendsOn Wsl.interactions B_SPR = false; decide
  | 11, _, _, _ => by show sendsOn Wsp.interactions B_SPR = false; decide
  | n + 12, h, _, _ => absurd h (by simp [m5aAir])

/-- Only `SN` sends on bus `b` (for `EPQ`, `SXQ`, `SXR`). -/
theorem sn_only (D b : Nat) (h0 : sendsOn shaTable.interactions b = false)
    (h1 : sendsOn Key.interactions b = false) (h2 : sendsOn Br.interactions b = false)
    (h4 : sendsOn Kcmp.interactions b = false) (h5 : sendsOn Wsb.interactions b = false)
    (h6 : sendsOn Wsn.interactions b = false) (h7 : sendsOn Wsa.interactions b = false)
    (h8 : sendsOn Snc.interactions b = false) (h9 : sendsOn Rng.interactions b = false)
    (h10 : sendsOn Wsl.interactions b = false) (h11 : sendsOn Wsp.interactions b = false) :
    ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 3 → sendsOn ((m5aAir D).tables[t]).interactions b = false
  | 0, _, _ => h0
  | 1, _, _ => h1
  | 2, _, _ => h2
  | 3, _, h => absurd rfl h
  | 4, _, _ => h4
  | 5, _, _ => h5
  | 6, _, _ => h6
  | 7, _, _ => h7
  | 8, _, _ => h8
  | 9, _, _ => h9
  | 10, _, _ => h10
  | 11, _, _ => h11
  | n + 12, h, _ => absurd h (by simp [m5aAir])

theorem epq_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 3 →
    sendsOn ((m5aAir D).tables[t]).interactions B_EPQ = false :=
  sn_only D B_EPQ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem sxq_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 3 →
    sendsOn ((m5aAir D).tables[t]).interactions B_SXQ = false :=
  sn_only D B_SXQ (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem sxr_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 3 →
    sendsOn ((m5aAir D).tables[t]).interactions B_SXR = false :=
  sn_only D B_SXR (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem ev_gm2 {tr : Trace Fp} {r : Nat} {pub : List Fp} {g x : Expr} (h : ev tr 2 r pub g = 1) :
    ev tr 2 r pub (g * x) = ev tr 2 r pub x := by
  rw [ev_hmul, h, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _)]

/-! ## Senders -/

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
  (hH : Holds (fullAir D extra nb np) pub tr)

include hH in
/-- **An `SPR` message** was sent by a `BR.oSL` row or an `SN.oEP` row. -/
theorem spr_src (hxP : ∀ T ∈ extra, sendsOn T.interactions B_SPR = false) {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub B_SPR false) :
    (∃ r, r < tr.height 2 ∧ ev tr 2 r pub (Br.c "oSL") = 1 ∧ m = brSprS.map (E tr 2 r pub)) ∨
    (∃ p, p < tr.height 3 ∧ ev tr 3 p pub (Sn.c "oEP") = 1 ∧ m = snSprS.map (E tr 3 p pub)) := by
  rcases sender_m5a2 B_SPR 2 3 (by simp [m5aAir]) (by simp [m5aAir]) (spr_only D) hxP (recv_sent hH hm) with
    ⟨r, hr, i, hi, hb, hs, hp, he⟩ | ⟨r, hr, i, hi, hb, hs, hp, he⟩
  · change i ∈ Br.interactions at hi
    obtain rfl := filter_one_mem br_spr_s hi hb hs
    exact .inl ⟨r, hr, eval_one_ev (multNat_one_bit rfl hp), he⟩
  · change i ∈ Sn.interactions at hi
    obtain rfl := filter_one_mem sn_spr_s hi hb hs
    exact .inr ⟨r, hr, eval_one_ev (multNat_one_bit rfl hp), he⟩

include hH in
/-- **An `EPQ` an `oEP` row received** was sent by a split row with `j0 = 0`. -/
theorem epq_src (hxE : ∀ T ∈ extra, sendsOn T.interactions B_EPQ = false) {p : Nat} (hp : p < tr.height 3)
    (h1 : ev tr 3 p pub (Sn.c "oEP") = 1) :
    ∃ s, s < tr.height 3 ∧ ev tr 3 s pub (Sn.gX * (1 - Sn.c "j0")) = 1 ∧
      snEpqS.map (E tr 3 s pub) = snEpqR.map (E tr 3 p pub) := by
  have h3 : 3 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 3) h3
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact sn_epq_r) hp rfl (ev_one_eval h1)
  obtain ⟨s, hs, i, hi, hb, hss, hpp, he⟩ :=
    sender_m5a B_EPQ 3 (by simp [m5aAir]) (epq_only D) hxE (recv_sent hH hm)
  change i ∈ Sn.interactions at hi
  obtain rfl := filter_one_mem sn_epq_s hi hb hss
  exact ⟨s, hs, eval_one_ev (multNat_one_bit rfl hpp), he.symm⟩

include hH in
/-- **An `SXQ` an `oEM` row received** was sent by an extension-split row with `z = 0`. -/
theorem sxq_src (hxS : ∀ T ∈ extra, sendsOn T.interactions B_SXQ = false) {p : Nat} (hp : p < tr.height 3)
    (h1 : ev tr 3 p pub (Sn.c "oEM") = 1) :
    ∃ s, s < tr.height 3 ∧ ev tr 3 s pub (Sn.c "oEX" * (1 - Sn.c "z")) = 1 ∧
      snSxqS.map (E tr 3 s pub) = snSxqR.map (E tr 3 p pub) := by
  have h3 : 3 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 3) h3
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact sn_sxq_r) hp rfl (ev_one_eval h1)
  obtain ⟨s, hs, i, hi, hb, hss, hpp, he⟩ :=
    sender_m5a B_SXQ 3 (by simp [m5aAir]) (sxq_only D) hxS (recv_sent hH hm)
  change i ∈ Sn.interactions at hi
  obtain rfl := filter_one_mem sn_sxq_s hi hb hss
  exact ⟨s, hs, eval_one_ev (multNat_one_bit rfl hpp), he.symm⟩

include hH in
/-- **The `SXR` an extension-split row received** was sent by an `oEM` row. -/
theorem sxr_src (hxS : ∀ T ∈ extra, sendsOn T.interactions B_SXR = false) {s : Nat} (hs : s < tr.height 3)
    (h1 : ev tr 3 s pub (Sn.c "oEX" * (1 - Sn.c "z")) = 1) :
    ∃ p, p < tr.height 3 ∧ ev tr 3 p pub (Sn.c "oEM") = 1 ∧
      snSxrS.map (E tr 3 p pub) = snSxrR.map (E tr 3 s pub) := by
  have h3 : 3 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 3) h3
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact sn_sxr_r) hs rfl (ev_one_eval h1)
  obtain ⟨p, hp, i, hi, hb, hss, hpp, he⟩ :=
    sender_m5a B_SXR 3 (by simp [m5aAir]) (sxr_only D) hxS (recv_sent hH hm)
  change i ∈ Sn.interactions at hi
  obtain rfl := filter_one_mem sn_sxr_s hi hb hss
  exact ⟨p, hp, eval_one_ev (multNat_one_bit rfl hpp), he.symm⟩

end

/-! ## A split row's request -/

section
variable (tr : Trace Fp) (pub : List Fp) (s : Nat)

/-- The old side a split row requests: the leaf `(L, A)` (`oLX`) or the node `(xhf, xh)` with
memory `xm` (`oEX`). -/
def snOs : OldSide :=
  if ev tr 3 s pub (Sn.c "oLX") = 1 then
    .leaf (ev tr 3 s pub (Sn.vlenOf fun t => Sn.c "x" t)) (bytesOf ((pack2 fun b => Sn.c "x" (4 + b)).map (E tr 3 s pub)))
  else .node (refOf (E tr 3 s pub (Sn.c "xhf")) (((List.range 16).map fun i => Sn.c "xh" i).map (E tr 3 s pub)))
    (le4 (((List.range 4).map fun t => Sn.c "xm" t).map (E tr 3 s pub)))

/-- **A split row's request**, from its own columns. -/
def snQ : SpQ :=
  ⟨ev tr 3 s pub (Sn.c "kid"), ev tr 3 s pub (Sn.c "kid2"), snOs tr pub s, ev tr 3 s pub (Sn.c "dvlen"),
    bytesOf (((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub))⟩

end

theorem snSpQ_h : ∀ i : Nat, i < 16 → snSpQ[5 + i]? = some (Sn.c "oLX" *
    (K 256 * Sn.c "x" (4 + 2 * i) + Sn.c "x" (4 + (2 * i + 1))) + Sn.c "xh" i) := by decide
theorem snSpQ_dvh : ∀ i : Nat, i < 16 → snSpQ[28 + i]? = some (Sn.c "dvh" i) := by decide
theorem snSpQ_xm : ∀ k : Nat, k < 4 → snSpQ[23 + k]? = some (Sn.c "xm" k) := by decide

theorem sn_mem_xh (i : Nat) (hi : i < 16) : Sn.c "xh" i - Sn.c "oEX" * (Sn.c "z" * (sm 256 (Sn.c "x" (2 * i)) +
    Sn.c "x" (2 * i + 1)) + (1 - Sn.c "z") * Sn.c "sxh" i) ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_map, List.mem_range]; memfind

section
variable {tr : Trace Fp} {pub : List Fp}

set_option maxHeartbeats 8000000 in
/-- **The `oSL` row decodes its split row's request.** -/
theorem oslQ_eq {s r : Nat} (hcs : ∀ e ∈ Sn.table.constraints, e.eval tr 3 s pub = 0)
    (hX : ev tr 3 s pub Sn.gX = 1) (hq : snSpQ.map (E tr 3 s pub) = brSpQ.map (E tr 2 r pub)) :
    oslQ tr pub r = snQ tr pub s := by
  obtain ⟨-, -, -, hXs⟩ := split_flags hcs hX
  have bX := FieldRows2.sn_hold hcs (e := bool (Sn.c "oLX")) (by unfold Sn.constraints; simp [Sn.ops])
  have bX' := bool_le bX
  have q2 := toNat_eq (at_eq2 hq (k := 2) rfl rfl)
  have q3 := toNat_eq (at_eq2 hq (k := 3) rfl rfl)
  have q4 := at_eq2 hq (k := 4) rfl rfl
  have q27 := toNat_eq (at_eq2 hq (k := 27) rfl rfl)
  have qh : ((List.range 16).map fun i => Br.c "dvh" i).map (E tr 2 r pub) =
      ((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 s pub) := by
    simp only [List.map_map]
    apply List.map_congr_left; intro i hi
    exact (at_eq2 hq (snSpQ_dvh i (List.mem_range.1 hi)) (brSpQ_dvh i (List.mem_range.1 hi))).symm
  have hos : oslOs tr pub r = snOs tr pub s := by
    unfold oslOs snOs
    rcases (by omega : ev tr 3 s pub (Sn.c "oLX") = 1 ∨ ev tr 3 s pub (Sn.c "oLX") = 0) with h1 | h0
    · have hxl : ev tr 2 r pub (Br.c "xl") = 1 := by rw [← toNat_eq q4]; exact h1
      have hE0 : ev tr 3 s pub (Sn.c "oEX") = 0 := by omega
      rw [if_pos hxl, if_pos h1]
      have e1 := ev_one_eval h1
      have e1' := ev_one_eval hxl
      have q22 := at_eq2 hq (k := 22) rfl rfl
      have l1 : ev tr 2 r pub (Br.c "lvlen2") = ev tr 3 s pub (Sn.vlenOf fun t => Sn.c "x" t) := by
        apply toNat_eq
        have := q22.symm
        simp only [E, eval_mul, e1, e1'] at this ⊢
        grind
      have l2 : ((List.range 16).map fun i => Br.c "lvh2" i).map (E tr 2 r pub) =
          (pack2 fun b => Sn.c "x" (4 + b)).map (E tr 3 s pub) := by
        simp only [List.map_map, pack2]
        apply List.map_congr_left; intro i hi
        have hi' := List.mem_range.1 hi
        have a := at_eq2 hq (snSpQ_h i hi') (brSpQ_h i hi')
        have xh0 : (Sn.c "xh" i).eval tr 3 s pub = 0 := by
          have := eq_of_sub (FieldRows2.sn_hold hcs (sn_mem_xh i hi'))
          rw [RowSnN.ev_gm0 hE0] at this
          exact fp_of_ev0 this
        simp only [Function.comp, E, eval_mul, eval_add, eval_sub, eval_lit, e1, e1', xh0] at a ⊢
        grind
      rw [l1, l2]
    · have hxl : ev tr 2 r pub (Br.c "xl") = 0 := by rw [← toNat_eq q4]; exact h0
      rw [if_neg (by omega), if_neg (by omega)]
      have z0 := fp_of_ev0 hxl
      have n1 : E tr 2 r pub (Br.c "nh2f") = E tr 3 s pub (Sn.c "xhf") := by
        have := at_eq2 hq (k := 21) rfl rfl
        simp only [E, eval_mul, eval_sub, eval_lit, z0] at this ⊢
        grind
      have n2 : (pack2 fun b => Br.c "nh2" b).map (E tr 2 r pub) =
          ((List.range 16).map fun i => Sn.c "xh" i).map (E tr 3 s pub) := by
        simp only [List.map_map, pack2]
        apply List.map_congr_left; intro i hi
        have hi' := List.mem_range.1 hi
        have a := at_eq2 hq (snSpQ_h i hi') (brSpQ_h i hi')
        have l0 := fp_of_ev0 h0
        simp only [Function.comp, E, eval_mul, eval_add, eval_sub, eval_lit, z0, l0] at a ⊢
        grind
      have n3 : le4 (((List.range 4).map fun k => Br.c "nm2" k).map (E tr 2 r pub)) =
          le4 (((List.range 4).map fun t => Sn.c "xm" t).map (E tr 3 s pub)) := by
        simp only [le4_map4]
        have a := fun k (hk : k < 4) => toNat_eq (at_eq2 hq (snSpQ_xm k hk) (brSpQ_nm k hk))
        have g : ∀ k, k < 4 → ev tr 2 r pub ((1 - Br.c "xl") * Br.c "nm2" k) = ev tr 2 r pub (Br.c "nm2" k) := by
          intro k hk
          rw [ev_gm2 (FieldRows2.ev_one_sub0 hxl)]
        have := a 0 (by decide); have := a 1 (by decide); have := a 2 (by decide); have := a 3 (by decide)
        have := g 0 (by decide); have := g 1 (by decide); have := g 2 (by decide); have := g 3 (by decide)
        change ev tr 2 r pub (Br.c "nm2" 0) + 65536 * ev tr 2 r pub (Br.c "nm2" 1) +
          4294967296 * ev tr 2 r pub (Br.c "nm2" 2) + 281474976710656 * ev tr 2 r pub (Br.c "nm2" 3) =
          ev tr 3 s pub (Sn.c "xm" 0) + 65536 * ev tr 3 s pub (Sn.c "xm" 1) +
          4294967296 * ev tr 3 s pub (Sn.c "xm" 2) + 281474976710656 * ev tr 3 s pub (Sn.c "xm" 3)
        omega
      rw [n1, n2, n3]
  unfold oslQ snQ
  rw [q2.symm, q3.symm, q27.symm, qh, hos]

end

end StateM5a.SnSplitBus
