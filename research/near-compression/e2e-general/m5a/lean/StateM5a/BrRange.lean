import StateM5a.BrDigest

/-!
# StateM5a.BrRange — the range facts of the active `BR` rows (`BrRangesW`) from `Holds`

Each 16-bit memory limb a `BR` row uses is traced to bytes:

* **new node** (`br_NM_lt`, rows with `gnew`): hashed (`gfin`: its memory bytes are SHA-256 message
  bytes, `BrDigest.br_new_node`) or published under a version id (`nref`: `RNG` lookups of the
  memory bytes);
* **old node** (`br_M_lt`, active rows): hashed (`gsha`: `BrDigest.br_old_node`) or read on `VER`
  (`VerRead.br_rd_part`, part 16 carries the limbs): the publisher hashed it, or published it as
  its new node (`br_NM_lt`);
* **child answers** (`br_nmom_lt`, rows with `gnew`): `nm` / `om` arrive on `UP` from a `BR` row
  (its `gnew·NM`, `(mU+mD)·M`: the two cases above) or an `SN` row (premise `SnUpLimbs`), or on
  `MATR` from an `SN` row (premise `SnMatLimbs`); they are `0` on the other ops;
* **old value length** (`br_vl_lt`): bytes on a hashing row; on a reading row a premise
  (`hVl`: the limbs are carried along version chains, kept values in rows publishing under a
  version id are not re-checked), with `brVlen < P` (a value is at most 4 MiB).

**`brRangesW_of`**: `BrRangesW` for every active `BR` row.
-/

namespace StateM5a.BrRange

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrN StateM5a.KcChain
open StateM5a.KeyDecode StateM5a.KeyDigest StateM5a.BrSer StateM5a.VerStore StateM5a.BrDigest
open StateM5a.RowHloc StateM5a.VerRead StateM5a.VerDec

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Message positions -/

theorem ui_nm (k : Nat) (hk : k < 4) : brW.ui[20 + k]? = some ((Br.c "oUD" + Br.c "oDH") * Br.c "nm" k) := by
  rw [br_ui]; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
theorem ui_om (k : Nat) (hk : k < 4) : brW.ui[24 + k]? = some (Br.c "om" k) := by
  rw [br_ui]; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
theorem uo_nm (k : Nat) (hk : k < 4) : brW.uo[20 + k]? = some (Br.c "gnew" * Br.NM.getD k 0) := by
  rw [br_uo]; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
theorem uo_om (k : Nat) (hk : k < 4) : brW.uo[24 + k]? = some ((Br.c "mU" + Br.c "mD") * Br.M.getD k 0) := by
  rw [br_uo]; rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- `BR`'s `MATR` answer to its `MATQ` (`oDL`, `oUN`, `oSL`). -/
def brMatR : List Expr :=
  [Br.c "w", Br.c "d" + 1, Br.c "kid2", Br.c "nhf"] ++ pack2 (fun b => Br.c "nh" b) ++
    (List.range 4).map fun k => Br.c "nm" k
def snMatR : List Expr :=
  [Sn.c "w", Sn.c "d", Sn.c "kid", Sn.c "nref"] ++ pack2 (fun b => Sn.c "hn" b) ++ Sn.NM

theorem brMatR_nm (k : Nat) (hk : k < 4) : brMatR[20 + k]? = some (Br.c "nm" k) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
theorem snMatR_nm (k : Nat) (hk : k < 4) : snMatR[20 + k]? = some (Sn.NM.getD k 0) := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

theorem br_matr_r : rcv B_MATR (Br.c "oDL" + Br.c "oUN" + Br.c "oSL") brMatR ∈ Br.interactions :=
  memD_mem (by decide)
theorem sn_matr_s : Sn.interactions.filter (fun i => decide (i.bus = B_MATR ∧ i.send = true)) =
    [snd B_MATR (Sn.c "oLM") snMatR] := by decide

theorem br_up_r : { bus := B_UP, mult := [brW.gdn], msg := brW.ui, send := false } ∈ Br.interactions :=
  (List.mem_filter.1 (by rw [br_ur]; exact List.mem_singleton_self _)).1

theorem M_get (k : Nat) (hk : k < 4) : Br.M.getD k 0 = limb16 (fun b => Br.c "mem" b) k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
theorem NM_get (k : Nat) (hk : k < 4) : Br.NM.getD k 0 = limb16 (fun b => Br.c "nmem" b) k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

/-! ## Senders -/

theorem up_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 2 → t ≠ 3 →
    sendsOn ((m5aAir D).tables[t]).interactions B_UP = false
  | 0, _, _, _ => by show sendsOn shaTable.interactions B_UP = false; decide
  | 1, _, _, _ => by show sendsOn Key.interactions B_UP = false; decide
  | 2, _, h, _ => absurd rfl h
  | 3, _, _, h => absurd rfl h
  | 4, _, _, _ => by show sendsOn Kcmp.interactions B_UP = false; decide
  | 5, _, _, _ => by show sendsOn Wsb.interactions B_UP = false; decide
  | 6, _, _, _ => by show sendsOn Wsn.interactions B_UP = false; decide
  | 7, _, _, _ => by show sendsOn Wsa.interactions B_UP = false; decide
  | 8, _, _, _ => by show sendsOn Snc.interactions B_UP = false; decide
  | 9, _, _, _ => by show sendsOn Rng.interactions B_UP = false; decide
  | 10, _, _, _ => by show sendsOn Wsl.interactions B_UP = false; decide
  | 11, _, _, _ => by show sendsOn Wsp.interactions B_UP = false; decide
  | n + 12, h, _, _ => absurd h (by simp [m5aAir])

theorem matr_only (D : Nat) : ∀ t (ht : t < (m5aAir D).tables.length), t ≠ 3 →
    sendsOn ((m5aAir D).tables[t]).interactions B_MATR = false
  | 0, _, _ => by show sendsOn shaTable.interactions B_MATR = false; decide
  | 1, _, _ => by show sendsOn Key.interactions B_MATR = false; decide
  | 2, _, _ => by show sendsOn Br.interactions B_MATR = false; decide
  | 3, _, h => absurd rfl h
  | 4, _, _ => by show sendsOn Kcmp.interactions B_MATR = false; decide
  | 5, _, _ => by show sendsOn Wsb.interactions B_MATR = false; decide
  | 6, _, _ => by show sendsOn Wsn.interactions B_MATR = false; decide
  | 7, _, _ => by show sendsOn Wsa.interactions B_MATR = false; decide
  | 8, _, _ => by show sendsOn Snc.interactions B_MATR = false; decide
  | 9, _, _ => by show sendsOn Rng.interactions B_MATR = false; decide
  | 10, _, _ => by show sendsOn Wsl.interactions B_MATR = false; decide
  | 11, _, _ => by show sendsOn Wsp.interactions B_MATR = false; decide
  | n + 12, h, _ => absurd h (by simp [m5aAir])

theorem br_nm_rng : ∀ b, b < 8 → memD (rcv B_RNG (Br.c "nref") [Br.c "nmem" b]) Br.interactions = true := by
  decide

set_option maxHeartbeats 4000000 in
theorem br_mem_vl0 (t : Nat) (ht : t < 4) : (1 - Br.c "hasv") * Br.c "vl" t ∈ Br.constraints := by brmem
set_option maxHeartbeats 4000000 in
theorem br_mem_dnm (k : Nat) (hk : k < 4) : Br.c "oDN" * Br.c "nm" k ∈ Br.constraints := by brmem
set_option maxHeartbeats 4000000 in
theorem br_mem_unom (k : Nat) (hk : k < 4) : (Br.c "oUN" + Br.c "oSL") * Br.c "om" k ∈ Br.constraints := by brmem

theorem getD_map_some {tr : Trace Fp} {t r : Nat} {pub : List Fp} {l : List Expr} {k : Nat} {e : Expr}
    (h : l[k]? = some e) : (l.map fun x => x.eval tr t r pub).getD k 0 = e.eval tr t r pub := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, h]

theorem map_getD_eq {l l' : List Expr} {f g : Expr → Fp} (h : l.map f = l'.map g) {k : Nat}
    (hk : k < l.length) (hk' : k < l'.length) : f (l.getD k 0) = g (l'.getD k 0) := by
  have := congrArg (fun x => x[k]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk', Option.map_some,
    Option.some.injEq] at this
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
    List.getElem?_eq_getElem hk']; exact this

section
variable {tr : Trace Fp} {pub : List Fp}

theorem pay16_M (r : Nat) : (brOldPay tr pub r 16).drop 35 = Br.M.map (E tr 2 r pub) := by
  simp only [brOldPay, brPay, show ¬ (16 < 16) from by decide, ↓reduceIte, List.map_append]
  exact List.drop_left' (by simp)

theorem pay16_NM (r : Nat) : (brNewPay tr pub r 16).drop 35 = Br.NM.map (E tr 2 r pub) := by
  simp only [brNewPay, brPay, show ¬ (16 < 16) from by decide, ↓reduceIte, List.map_append]
  exact List.drop_left' (by simp)

theorem pay16_vl (r : Nat) (k : Nat) (hk : k < 2) :
    (brOldPay tr pub r 16)[1 + k]? = some (E tr 2 r pub (limb16 (fun t => Br.c "vl" t) k)) := by
  simp only [brOldPay, brPay, show ¬ (16 < 16) from by decide, ↓reduceIte, List.map_append]
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> rfl

theorem pay16_nvl (r : Nat) (k : Nat) (hk : k < 2) :
    (brNewPay tr pub r 16)[1 + k]? = some (E tr 2 r pub (limb16 (fun t => Br.c "nvl" t) k)) := by
  simp only [brNewPay, brPay, show ¬ (16 < 16) from by decide, ↓reduceIte, List.map_append]
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> rfl

end

/-! ## The new node's and the old node's memory limbs -/

/-- The `SN` rows' memory limbs on `UP` (positions `20..27`: `nm`, `om`) are 16-bit (premise,
the `SN` side). -/
def SnUpLimbs (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → ev tr 3 r pub snW.g = 1 → ∀ k, 20 ≤ k → k < 28 →
    ((vals tr 3 r pub snW.uo).getD k 0).toNat < 65536

/-- The memory limbs of an `SN` row's `MATR` answer (`oLM`) are 16-bit (premise, the `SN` side). -/
def SnMatLimbs (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → ev tr 3 r pub (Sn.c "oLM") = 1 → ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
  (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)

theorem full2 : (fullAir D extra nb np).tables[2]! = Br.table := by
  rw [WsDecode.full_get 2 (by decide)]; rfl

include hH hxB hxD hxK hxr in
/-- **The new node's memory limbs** (rows with a new node). -/
theorem br_NM_lt {r : Nat} (hr : r < tr.height 2) (hg : ev tr 2 r pub (Br.c "gnew") = 1) :
    ∀ k, k < 4 → ev tr 2 r pub (Br.NM.getD k 0) < 65536 := by
  intro k hk
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have hn := flag_le hc "nref" (by simp)
  rw [NM_get k hk]
  rcases (by omega : ev tr 2 r pub (Br.c "nref") = 0 ∨ ev tr 2 r pub (Br.c "nref") = 1) with h0 | h1
  · have hB := (br_new_node hH hxB hxD hxK hr (ev_gfin hg h0)).1
    exact ev_limb16_byte (hB.mb _ (by omega)) (hB.mb _ (by omega))
  · have rb : ∀ b, b < 8 → ev tr 2 r pub (Br.c "nmem" b) < 256 := fun b hb =>
      WsDecode3.rng_rcv hH hxr (t := 2) (by simp [fullAir, m5aAir])
        (by rw [full2]; exact memD_mem (br_nm_rng b hb)) hr (ev_one_eval h1)
    exact ev_limb16_byte (rb _ (by omega)) (rb _ (by omega))

include hH hxB hxD hxK hxr in
/-- **The old node's memory limbs** (active rows). -/
theorem br_M_lt (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false) {r : Nat} (hr : r < tr.height 2)
    (hg : ev tr 2 r pub Br.gold = 1) : ∀ k, k < 4 → ev tr 2 r pub (Br.M.getD k 0) < 65536 := by
  intro k hk
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have hs := flag_le hc "gsha" (by simp)
  have hl : k < Br.M.length := by simp [Br.M, memLimbs]; omega
  have hl' : k < Br.NM.length := by simp [Br.NM, memLimbs]; omega
  rcases (by omega : ev tr 2 r pub (Br.c "gsha") = 0 ∨ ev tr 2 r pub (Br.c "gsha") = 1) with h0 | h1
  · have hgr : (Br.gold - Br.c "gsha").eval tr 2 r pub = 1 := ev_one_eval (by rw [ev_sub, hg, h0])
    obtain ⟨r', hr', (⟨hs', he⟩ | ⟨hn', he⟩)⟩ := br_rd_part hH hxV hr hgr 16 (by decide)
    · have e2 := congrArg (List.drop 35) (rd_old he).2.2
      rw [pay16_M, pay16_M] at e2
      have e3 := congrArg Fp.toNat (map_getD_eq e2 hl hl)
      change ev tr 2 r pub _ = ev tr 2 r' pub _ at e3
      rw [e3, M_get k hk]
      have hB := (br_old_node hH hxB hxD hxK hr' hs').1
      exact ev_limb16_byte (hB.mb _ (by omega)) (hB.mb _ (by omega))
    · have e2 := congrArg (List.drop 35) (rd_new he).2.2
      rw [pay16_M, pay16_NM] at e2
      have e3 := congrArg Fp.toNat (map_getD_eq e2 hl hl')
      change ev tr 2 r pub _ = ev tr 2 r' pub _ at e3
      rw [e3]
      exact br_NM_lt hH hxB hxD hxK hxr hr' hn' k hk
  · have hB := (br_old_node hH hxB hxD hxK hr h1).1
    rw [M_get k hk]
    exact ev_limb16_byte (hB.mb _ (by omega)) (hB.mb _ (by omega))

include hH hxB hxD hxK in
/-- **The old value-length limbs of a hashing row** are 16-bit. -/
theorem br_vl_hashed {r : Nat} (hr : r < tr.height 2) (hs : ev tr 2 r pub (Br.c "gsha") = 1) :
    ∀ k, k < 2 → ev tr 2 r pub (limb16 (fun t => Br.c "vl" t) k) < 65536 := by
  intro k hk
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have hB := (br_old_node hH hxB hxD hxK hr hs).1
  have hv := bool_le (FieldRows.hold rfl hc RowBrF.br_bool_hasv)
  rcases (by omega : ev tr 2 r pub (Br.c "hasv") = 0 ∨ ev tr 2 r pub (Br.c "hasv") = 1) with h0 | h1
  · have z : ∀ t, t < 4 → ev tr 2 r pub (Br.c "vl" t) = 0 := fun t ht =>
      FieldVer.gate_zero (FieldRows.hold rfl hc (br_mem_vl0 t ht)) (by rw [ev_sub, h0]; rfl)
    exact ev_limb16_byte (by rw [z _ (by omega)]; omega) (by rw [z _ (by omega)]; omega)
  · exact ev_limb16_byte (hB.vl h1 _ (by omega)) (hB.vl h1 _ (by omega))

theorem ev_gate_lt {g x : Expr} {r : Nat} (hg : ev tr 2 r pub g ≤ 1) (hx : ev tr 2 r pub g = 1 → ev tr 2 r pub x < 65536) :
    ev tr 2 r pub (g * x) < 65536 := by
  rw [ev_hmul]
  rcases (by omega : ev tr 2 r pub g = 0 ∨ ev tr 2 r pub g = 1) with h | h
  · rw [h]; simp
  · rw [h, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _)]; exact hx h

include hH hxB hxD hxK hxr in
/-- **The memory limbs of every `UP` message sent** (positions `20..27`) are 16-bit. -/
theorem up_sent_lt (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false)
    (hxU : ∀ T ∈ extra, sendsOn T.interactions B_UP = false) (hSU : SnUpLimbs tr pub) {m : List Fp}
    (hm : m ∈ busList (fullAir D extra nb np) tr pub B_UP true) :
    ∀ k, 20 ≤ k → k < 28 → (m.getD k 0).toNat < 65536 := by
  intro k hk1 hk2
  rcases sender_m5a2 B_UP 2 3 (by simp [m5aAir]) (by simp [m5aAir]) (up_only D) hxU hm with
    ⟨r, hr, i, hi, hb, hs, hp, rfl⟩ | ⟨r, hr, i, hi, hb, hs, hp, rfl⟩
  · change i ∈ Br.interactions at hi
    obtain rfl := filter_one_mem br_us hi hb hs
    have hg : ev tr 2 r pub Br.gold = 1 := eval_one_ev (multNat_one_bit (g := brW.g) rfl hp)
    have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
    brfacts hc hg
    rcases (by omega : k < 24 ∨ 24 ≤ k) with h | h
    · obtain ⟨j, rfl⟩ : ∃ j, k = 20 + j := ⟨k - 20, by omega⟩
      show ((brW.uo.map fun x => x.eval tr 2 r pub).getD (20 + j) 0).toNat < 65536
      rw [getD_map_some (uo_nm j (by omega))]
      exact ev_gate_lt (by omega) (fun h1 => br_NM_lt hH hxB hxD hxK hxr hr h1 j (by omega))
    · obtain ⟨j, rfl⟩ : ∃ j, k = 24 + j := ⟨k - 24, by omega⟩
      show ((brW.uo.map fun x => x.eval tr 2 r pub).getD (24 + j) 0).toNat < 65536
      rw [getD_map_some (uo_om j (by omega))]
      have e : ev tr 2 r pub (Br.c "mU" + Br.c "mD") = ev tr 2 r pub (Br.c "mU") + ev tr 2 r pub (Br.c "mD") :=
        ev_add_lt (by omega)
      exact ev_gate_lt (by omega) (fun _ => br_M_lt hH hxB hxD hxK hxr hxV hr hg j (by omega))
  · change i ∈ Sn.interactions at hi
    obtain rfl := filter_one_mem sn_us hi hb hs
    exact hSU r hr (eval_one_ev (multNat_one_bit (g := snW.g) rfl hp)) k hk1 hk2

/-- **The memory limbs of every `MATR` message sent** (positions `20..23`) are 16-bit. -/
theorem matr_sent_lt (hxM : ∀ T ∈ extra, sendsOn T.interactions B_MATR = false) (hSM : SnMatLimbs tr pub)
    {m : List Fp} (hm : m ∈ busList (fullAir D extra nb np) tr pub B_MATR true) :
    ∀ k, 20 ≤ k → k < 24 → (m.getD k 0).toNat < 65536 := by
  intro k hk1 hk2
  obtain ⟨r, hr, i, hi, hb, hs, hp, rfl⟩ := sender_m5a B_MATR 3 (by simp [m5aAir]) (matr_only D) hxM hm
  change i ∈ Sn.interactions at hi
  obtain rfl := filter_one_mem sn_matr_s hi hb hs
  have h1 := eval_one_ev (multNat_one_bit (g := Sn.c "oLM") rfl hp)
  obtain ⟨j, rfl⟩ : ∃ j, k = 20 + j := ⟨k - 20, by omega⟩
  show ((snMatR.map fun x => x.eval tr 3 r pub).getD (20 + j) 0).toNat < 65536
  rw [getD_map_some (snMatR_nm j (by omega))]
  exact hSM r hr h1 j (by omega)

include hH hxB hxD hxK hxr in
set_option maxHeartbeats 4000000 in
/-- **The child answer limbs `nm` / `om`** of an active row with a new node. -/
theorem br_nmom_lt (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false)
    (hxU : ∀ T ∈ extra, sendsOn T.interactions B_UP = false)
    (hxM : ∀ T ∈ extra, sendsOn T.interactions B_MATR = false) (hSU : SnUpLimbs tr pub) (hSM : SnMatLimbs tr pub)
    {r : Nat} (hr : r < tr.height 2) (hg : ev tr 2 r pub Br.gold = 1) (hn : ev tr 2 r pub (Br.c "gnew") = 1) :
    ∀ k, k < 4 → ev tr 2 r pub (Br.c "nm" k) < 65536 ∧ ev tr 2 r pub (Br.c "om" k) < 65536 := by
  intro k hk
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have h2 : 2 < (fullAir D extra nb np).tables.length := by simp [fullAir, m5aAir]
  -- the `UP` answer
  have hup : ev tr 2 r pub (Br.c "gdn") = 1 →
      ev tr 2 r pub ((Br.c "oUD" + Br.c "oDH") * Br.c "nm" k) < 65536 ∧ ev tr 2 r pub (Br.c "om" k) < 65536 := by
    intro hd
    have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 2) h2
      (by rw [fullAir_get (by simp [m5aAir]) _]; exact br_up_r) hr rfl (ev_one_eval hd)
    have hs := up_sent_lt hH hxB hxD hxK hxr hxV hxU hSU (recv_sent hH hm)
    have a := hs (20 + k) (by omega) (by omega)
    have b := hs (24 + k) (by omega) (by omega)
    simp only [Interaction.msgVal] at a b
    rw [getD_map_some (ui_nm k hk)] at a
    rw [getD_map_some (ui_om k hk)] at b
    exact ⟨a, b⟩
  -- the `MATR` answer
  have hmat : ev tr 2 r pub (Br.c "oDL" + Br.c "oUN" + Br.c "oSL") = 1 → ev tr 2 r pub (Br.c "nm" k) < 65536 := by
    intro hd
    have hm := msg_mem_busList (A := fullAir D extra nb np) (t := 2) h2
      (by rw [fullAir_get (by simp [m5aAir]) _]; exact br_matr_r) hr rfl (ev_one_eval hd)
    have a := matr_sent_lt hxM hSM (recv_sent hH hm) (20 + k) (by omega) (by omega)
    simp only [rcv, Interaction.msgVal] at a
    rwa [getD_map_some (brMatR_nm k hk)] at a
  brfacts hc hg
  have g2 : ∀ {a b : Expr}, ev tr 2 r pub a ≤ 1 → ev tr 2 r pub b ≤ 1 →
      ev tr 2 r pub (a + b) = ev tr 2 r pub a + ev tr 2 r pub b := fun ha hb => ev_add_lt (by omega)
  have eUD := g2 (a := Br.c "oUD") (b := Br.c "oDH") (by omega) (by omega)
  have eUN := g2 (a := Br.c "oUN") (b := Br.c "oSL") (by omega) (by omega)
  have eUV := g2 (a := Br.c "oUV") (b := Br.c "oDV") (by omega) (by omega)
  have eL1 := g2 (a := Br.c "oDL") (b := Br.c "oUN") (by omega) (by omega)
  have eL2 := g2 (a := Br.c "oDL" + Br.c "oUN") (b := Br.c "oSL") (by omega) (by omega)
  have hgate : ∀ {x : Expr}, ev tr 2 r pub (Br.c "oUD" + Br.c "oDH") = 1 →
      ev tr 2 r pub ((Br.c "oUD" + Br.c "oDH") * x) = ev tr 2 r pub x := fun h => by
    rw [ev_hmul, h, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _)]
  -- the ops with a new node
  rcases (by omega : ev tr 2 r pub (Br.c "oUV") + ev tr 2 r pub (Br.c "oDV") = 1 ∨
      ev tr 2 r pub (Br.c "oUD") + ev tr 2 r pub (Br.c "oDH") = 1 ∨ ev tr 2 r pub (Br.c "oDL") = 1 ∨
      ev tr 2 r pub (Br.c "oDN") = 1 ∨ ev tr 2 r pub (Br.c "oUN") = 1) with h | h | h | h | h
  · have z1 := FieldVer.gate_zero (FieldRows.hold rfl hc (RowBrV.br_mem_v0 k hk).1) (by rw [eUV]; exact h)
    have z2 := FieldVer.gate_zero (FieldRows.hold rfl hc (RowBrV.br_mem_v0 k hk).2) (by rw [eUV]; exact h)
    omega
  · have := hup (by omega)
    rw [hgate (by rw [eUD]; exact h)] at this
    exact this
  · exact ⟨hmat (by rw [eL2, eL1]; omega), (hup (by omega)).2⟩
  · have z := FieldVer.gate_zero (FieldRows.hold rfl hc (br_mem_dnm k hk)) h
    exact ⟨by omega, (hup (by omega)).2⟩
  · have z := FieldVer.gate_zero (FieldRows.hold rfl hc (br_mem_unom k hk)) (by rw [eUN]; omega)
    exact ⟨hmat (by rw [eL2, eL1]; omega), by omega⟩

include hH hxB hxD hxK hxr in
/-- **`BrRangesW` of every active `BR` row**, from `Holds`, the `SN` side's limb ranges, and the
old value length (16-bit limbs on rows reading their node on `VER`, and `< P`). -/
theorem brRangesW_of (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false)
    (hxU : ∀ T ∈ extra, sendsOn T.interactions B_UP = false)
    (hxM : ∀ T ∈ extra, sendsOn T.interactions B_MATR = false) (hSU : SnUpLimbs tr pub) (hSM : SnMatLimbs tr pub)
    (hVl : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → ev tr 2 r pub (Br.c "gsha") = 0 →
      ∀ k, k < 2 → ev tr 2 r pub (limb16 (fun t => Br.c "vl" t) k) < 65536)
    (hVP : ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → brVlen tr pub r < 2013265921)
    {r : Nat} (hr : r < tr.height 2) (hg : ev tr 2 r pub Br.gold = 1) : BrRangesW tr pub r := by
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  refine ⟨br_M_lt hH hxB hxD hxK hxr hxV hr hg, fun k hk => ?_, hVP r hr hg, fun hn k hk =>
    ⟨br_NM_lt hH hxB hxD hxK hxr hr hn k hk,
     (br_nmom_lt hH hxB hxD hxK hxr hxV hxU hxM hSU hSM hr hg hn k hk).1,
     (br_nmom_lt hH hxB hxD hxK hxr hxV hxU hxM hSU hSM hr hg hn k hk).2⟩⟩
  have hs := flag_le hc "gsha" (by simp)
  rcases (by omega : ev tr 2 r pub (Br.c "gsha") = 0 ∨ ev tr 2 r pub (Br.c "gsha") = 1) with h0 | h1
  · exact hVl r hr hg h0 k hk
  · exact br_vl_hashed hH hxB hxD hxK hr h1 k hk

end

end StateM5a.BrRange
