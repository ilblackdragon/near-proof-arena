import StateM5a.BrRange

/-!
# StateM5a.BrVl — the old value length of every active `BR` row from `Holds` (`hVl`, `hVP`)

`BrRange.brRangesW_of` took two premises on the old value length `vl` of an active `BR` row:
`hVl` (its two 16-bit limbs are `< 2^16` on rows reading their node on `VER`) and `hVP`
(`brVlen < P`).  Both now follow from `Holds`:

* **publishers** — every `BR` record on `VER` has value-length bytes `ℓ₀, ℓ₁, ℓ₂ < 256` and
  `ℓ₃ = 0`: a hashing row's old node (`gsha`: SHA-256 message bytes, `hasv·vl₃ = 0`,
  `br_vl_pubOld`), a row's new node (`gnew`: hashed — SHA-256 bytes — or published under a version
  id — the M5a-6 `RNG` lookups of `nvl` under `nref`; `nvl₃ = 0` from `oUV·nvl₃ = 0` on a written
  value, and from `hasv·vl₃ = 0` through the kept-value equations otherwise; `br_nvl_pubNew`);
* **readers** — part 16 of a record read on `VER` carries the two limbs (`VerRead.br_rd_part`,
  `pay16_vl`/`pay16_nvl`), so they are the publisher's: `limb₀ < 2^16`, `limb₁ < 2^8`;
* hence **`br_vl_limbs`** on every active row, **`hVl_of`**, and **`hVP_of`**
  (`brVlen < 2^24 < P`).

Before M5a-6 a kept value under a version id copied `vl` unchecked, so the reader's bound needed an
induction along version chains; the `RNG [nvl]` lookups (commit 7e176cb9a) make it one step.
-/

namespace StateM5a.BrVl

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowBrN StateM5a.KcChain
open StateM5a.KeyDecode StateM5a.KeyDigest StateM5a.BrSer StateM5a.VerStore StateM5a.BrDigest
open StateM5a.RowHloc StateM5a.VerRead StateM5a.VerDec StateM5a.BrRange

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Constraint and interaction membership -/

theorem br_nvl_rng : ∀ t, t < 4 → memD (rcv B_RNG (Br.c "nref") [Br.c "nvl" t]) Br.interactions = true := by
  decide

set_option maxHeartbeats 4000000 in
theorem br_mem_nvl0 (t : Nat) (ht : t < 4) : (1 - Br.c "nhv") * Br.c "nvl" t ∈ Br.constraints := by brmem
set_option maxHeartbeats 4000000 in
theorem br_mem_nvlk (t : Nat) (ht : t < 4) :
    (Br.c "gnew" - Br.c "oUV" - Br.c "oDV") * (Br.c "nvl" t - Br.c "vl" t) ∈ Br.constraints := by brmem
set_option maxHeartbeats 4000000 in
theorem br_mem_nhvk : (Br.c "gnew" - Br.c "oUV" - Br.c "oDV") * (Br.c "nhv" - Br.c "hasv") ∈ Br.constraints := by
  brmem
set_option maxHeartbeats 4000000 in
theorem br_mem_uvl3 : Br.c "oUV" * Br.c "nvl" 3 ∈ Br.constraints := by brmem
set_option maxHeartbeats 4000000 in
theorem br_mem_vl3 : Br.c "hasv" * Br.c "vl" 3 ∈ Br.constraints := by brmem
set_option maxHeartbeats 4000000 in
theorem br_mem_dvnhv : Br.c "oDV" * Br.c "nhv" ∈ Br.constraints := by brmem
set_option maxHeartbeats 4000000 in
theorem br_mem_slhv : Br.c "oSL" * Br.c "hasv" ∈ Br.constraints := by brmem

/-! ## Limbs of `(ℓ₀, ℓ₁, ℓ₂, 0)` -/

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem ev_limb16_val {v : Nat → Expr} {k : Nat} (ha : ev tr 2 r pub (v (2 * k)) < 256)
    (hb : ev tr 2 r pub (v (2 * k + 1)) < 256) :
    ev tr 2 r pub (limb16 v k) = ev tr 2 r pub (v (2 * k)) + 256 * ev tr 2 r pub (v (2 * k + 1)) := by
  unfold limb16
  rw [ev_hadd, ev_hmul, show K 256 = Expr.const 256 from rfl, ev_const]
  simp only [Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (show 256 * ev tr 2 r pub (v (2 * k + 1)) < P by omega),
    Nat.mod_eq_of_lt (show ev tr 2 r pub (v (2 * k)) + 256 * ev tr 2 r pub (v (2 * k + 1)) < P by omega)]

/-- Value-length bytes `(ℓ₀, ℓ₁, ℓ₂ < 256, ℓ₃ = 0)`. -/
def LenOK (tr : Trace Fp) (pub : List Fp) (r : Nat) (v : Nat → Expr) : Prop :=
  (∀ t, t < 3 → ev tr 2 r pub (v t) < 256) ∧ ev tr 2 r pub (v 3) = 0

theorem limbs_of_lenOK {v : Nat → Expr} (h : LenOK tr pub r v) :
    ev tr 2 r pub (limb16 v 0) < 65536 ∧ ev tr 2 r pub (limb16 v 1) < 256 := by
  obtain ⟨hb, h3⟩ := h
  refine ⟨ev_limb16_byte (hb 0 (by omega)) (hb 1 (by omega)), ?_⟩
  rw [ev_limb16_val (k := 1) (hb 2 (by omega)) (by rw [h3]; omega), h3]
  have := hb 2 (by omega)
  omega

theorem lenOK_zero {v : Nat → Expr} (h : ∀ t, t < 4 → ev tr 2 r pub (v t) = 0) : LenOK tr pub r v :=
  ⟨fun t ht => by rw [h t (by omega)]; omega, h 3 (by omega)⟩

theorem ev_gate3 {g u x : Expr} (hg : ev tr 2 r pub g = 1) (hu : ev tr 2 r pub u = 0) (hx : ev tr 2 r pub x = 0) :
    ev tr 2 r pub (g - u - x) = 1 := by
  rw [ev_sub, ev_sub, hg, hu, hx]

end

/-! ## Publishers -/

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
  (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)

include hH hxB hxD hxK in
/-- **A hashing row's old value length** is `(ℓ₀, ℓ₁, ℓ₂, 0)`. -/
theorem br_vl_pubOld {r : Nat} (hr : r < tr.height 2) (hs : ev tr 2 r pub (Br.c "gsha") = 1) :
    LenOK tr pub r (fun t => Br.c "vl" t) := by
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have hv := bool_le (FieldRows.hold rfl hc RowBrF.br_bool_hasv)
  rcases (by omega : ev tr 2 r pub (Br.c "hasv") = 0 ∨ ev tr 2 r pub (Br.c "hasv") = 1) with h0 | h1
  · exact lenOK_zero fun t ht =>
      FieldVer.gate_zero (FieldRows.hold rfl hc (br_mem_vl0 t ht)) (by rw [ev_sub, h0]; rfl)
  · have hB := (br_old_node hH hxB hxD hxK hr hs).1
    exact ⟨fun t ht => hB.vl h1 t (by omega), FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_vl3) h1⟩

include hH hxB hxD hxK hxr in
set_option maxHeartbeats 4000000 in
/-- **A row's new value length** (`gnew`) is `(ℓ₀, ℓ₁, ℓ₂, 0)`. -/
theorem br_nvl_pubNew {r : Nat} (hr : r < tr.height 2) (hn : ev tr 2 r pub (Br.c "gnew") = 1) :
    LenOK tr pub r (fun t => Br.c "nvl" t) := by
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have hb : ∀ s ∈ flagNames, ev tr 2 r pub (Br.c s) ≤ 1 := fun s hs => bool_le (FieldRows.hold rfl hc (br_bool' s hs))
  have bUV := hb "oUV" (by simp [flagNames]); have bDV := hb "oDV" (by simp [flagNames])
  have bSL := hb "oSL" (by simp [flagNames])
  have hv := bool_le (FieldRows.hold rfl hc RowBrF.br_bool_hasv)
  have hnv := br_bool_nhv hc
  have hnr := flag_le hc "nref" (by simp)
  rcases (by omega : ev tr 2 r pub (Br.c "nhv") = 0 ∨ ev tr 2 r pub (Br.c "nhv") = 1) with h0 | h1
  · exact lenOK_zero fun t ht =>
      FieldVer.gate_zero (FieldRows.hold rfl hc (br_mem_nvl0 t ht)) (by rw [ev_sub, h0]; rfl)
  -- the bytes: `RNG` under a version id, SHA-256 message bytes when hashed
  have hbytes : ∀ t, t < 4 → ev tr 2 r pub (Br.c "nvl" t) < 256 := by
    intro t ht
    rcases (by omega : ev tr 2 r pub (Br.c "nref") = 0 ∨ ev tr 2 r pub (Br.c "nref") = 1) with n0 | n1
    · exact (br_new_node hH hxB hxD hxK hr (ev_gfin hn n0)).1.vl h1 t ht
    · exact WsDecode3.rng_rcv hH hxr (t := 2) (by simp [fullAir, m5aAir])
        (by rw [full2]; exact memD_mem (br_nvl_rng t ht)) hr (ev_one_eval n1)
  refine ⟨fun t ht => hbytes t (by omega), ?_⟩
  -- the top byte: a written value (`oUV·nvl₃ = 0`); a removed one has no value (`oDV·nhv = 0`);
  -- otherwise the value is kept (`nvl = vl`, `nhv = hasv`) and `hasv·vl₃ = 0`
  rcases (by omega : ev tr 2 r pub (Br.c "oUV") = 1 ∨ ev tr 2 r pub (Br.c "oUV") = 0) with u1 | u0
  · exact FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_uvl3) u1
  rcases (by omega : ev tr 2 r pub (Br.c "oDV") = 1 ∨ ev tr 2 r pub (Br.c "oDV") = 0) with d1 | d0
  · have := FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_dvnhv) d1
    omega
  have hk := ev_gate3 (r := r) (tr := tr) (pub := pub) hn u0 d0
  have e1 := eq_of_sub (FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_nhvk) hk)
  have e2 := eq_of_sub (FieldVer.gate_zero (FieldRows.hold rfl hc (br_mem_nvlk 3 (by omega))) hk)
  rw [e2]
  exact FieldVer.gate_zero (FieldRows.hold rfl hc br_mem_vl3) (by omega)

include hH hxB hxD hxK hxr in
set_option maxHeartbeats 4000000 in
/-- **The old value-length limbs of every active `BR` row**: `limb₀ < 2^16`, `limb₁ < 2^8`. -/
theorem br_vl_limbs (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false) {r : Nat} (hr : r < tr.height 2)
    (hg : ev tr 2 r pub Br.gold = 1) :
    ev tr 2 r pub (limb16 (fun t => Br.c "vl" t) 0) < 65536 ∧ ev tr 2 r pub (limb16 (fun t => Br.c "vl" t) 1) < 256 := by
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have hs := flag_le hc "gsha" (by simp)
  rcases (by omega : ev tr 2 r pub (Br.c "gsha") = 0 ∨ ev tr 2 r pub (Br.c "gsha") = 1) with h0 | h1
  · have hgr : (Br.gold - Br.c "gsha").eval tr 2 r pub = 1 := ev_one_eval (by rw [ev_sub, hg, h0])
    obtain ⟨r', hr', (⟨hs', he⟩ | ⟨hn', he⟩)⟩ := br_rd_part hH hxV hr hgr 16 (by decide)
    · have e2 := (rd_old he).2.2
      have ek : ∀ k, k < 2 → ev tr 2 r pub (limb16 (fun t => Br.c "vl" t) k) =
          ev tr 2 r' pub (limb16 (fun t => Br.c "vl" t) k) := by
        intro k hk
        have e3 := congrArg (fun l => l[1 + k]?) e2
        simp only [pay16_vl _ k hk, Option.some.injEq] at e3
        exact congrArg Fp.toNat e3
      rw [ek 0 (by omega), ek 1 (by omega)]
      exact limbs_of_lenOK (br_vl_pubOld hH hxB hxD hxK hr' hs')
    · have e2 := (rd_new he).2.2
      have ek : ∀ k, k < 2 → ev tr 2 r pub (limb16 (fun t => Br.c "vl" t) k) =
          ev tr 2 r' pub (limb16 (fun t => Br.c "nvl" t) k) := by
        intro k hk
        have e3 := congrArg (fun l => l[1 + k]?) e2
        simp only [pay16_vl _ k hk, pay16_nvl _ k hk, Option.some.injEq] at e3
        exact congrArg Fp.toNat e3
      rw [ek 0 (by omega), ek 1 (by omega)]
      exact limbs_of_lenOK (br_nvl_pubNew hH hxB hxD hxK hxr hr' hn')
  · exact limbs_of_lenOK (br_vl_pubOld hH hxB hxD hxK hr h1)

include hH hxB hxD hxK hxr in
/-- **`hVl` of `BrRange.brRangesW_of` from `Holds`.** -/
theorem hVl_of (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false) :
    ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → ev tr 2 r pub (Br.c "gsha") = 0 →
      ∀ k, k < 2 → ev tr 2 r pub (limb16 (fun t => Br.c "vl" t) k) < 65536 := by
  intro r hr hg _ k hk
  have := br_vl_limbs hH hxB hxD hxK hxr hxV hr hg
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> omega

include hH hxB hxD hxK hxr in
/-- **`hVP` from `Holds`**: the old value length of an active row is `< 2^24 < P`. -/
theorem hVP_of (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false) :
    ∀ r, r < tr.height 2 → ev tr 2 r pub Br.gold = 1 → brVlen tr pub r < 2013265921 := by
  intro r hr hg
  have := br_vl_limbs hH hxB hxD hxK hxr hxV hr hg
  have e : brVlen tr pub r = ev tr 2 r pub (limb16 (fun t => Br.c "vl" t) 0) +
      65536 * ev tr 2 r pub (limb16 (fun t => Br.c "vl" t) 1) := rfl
  omega

end

end StateM5a.BrVl
