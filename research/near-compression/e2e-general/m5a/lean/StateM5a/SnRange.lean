import StateM5a.SnStore2

/-!
# StateM5a.SnRange — the range facts of the `SN` heads with `cont = 0` from `Holds`

* **new node** (`gnew`): its memory bytes and (leaf) payload bytes are bytes — published under a
  version id (`nref`: the `RNG` lookups of `nmem` and, for a leaf, of `nx`) or hashed (`gfin`:
  SHA-256 message bytes, `SnRec.sn_new_node`);
* **old node** (`gold`): its memory limbs are 16-bit — hashed here (`gsha`) or read on `VER`
  (`SnVer.sn_rd_part`, part 0 carries the limbs): from a publisher's old (hashed) or new node;
* the new leaf's memory (`oLR`, `oLM`) is `< 2^25 < P` (`nmem₃ ∈ {0,1}`, `nmem₄..₇ = 0`).

Hence `sn_limbs3_at` (`SnAssembly.SnLimbsAt3` of a `cont = 0` walk row), `sn_leafMem_lt`
(`SnLeafMemLt` / `SnMatLeaf` at `cont = 0` rows) and `sn_nm_lt` (`SnMatLimbs` at `cont = 0`).
-/

namespace StateM5a.SnRange

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KeyDecode StateM5a.KeyDigest StateM5a.SnSer StateM5a.SnHashed StateM5a.SnRec
open StateM5a.SnVer StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnN StateM5a.SnStore StateM5a.SnStore2

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem sn_rng_nmem : ∀ b, b < 8 → memD (rcv B_RNG (Sn.c "nref") [Sn.c "nmem" b]) Sn.interactions = true := by
  decide
theorem sn_rng_nx : ∀ t, t < 36 → memD (rcv B_RNG (Sn.c "nref" * Sn.c "isL") [Sn.c "nx" t]) Sn.interactions = true := by
  decide

theorem sn_mem_nm4 (t : Nat) (ht : t < 4) : (Sn.c "oLR" + Sn.c "oLM") * Sn.c "nmem" (4 + t) ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_map, List.mem_range]
  memfind
theorem sn_mem_nm3 : (Sn.c "oLR" + Sn.c "oLM") * Sn.c "nmem" 3 * (Sn.c "nmem" 3 - 1) ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxB : XSbHi D extra nb np tr pub)
  (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
  (hxV : ∀ T ∈ extra, sendsOn T.interactions B_VER = false)

theorem rng3 {g e : Expr} (hi : memD (rcv B_RNG g [e]) Sn.interactions = true) {r : Nat} (hr : r < tr.height 3)
    (hg : g.eval tr 3 r pub = 1) (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)
    (hH : Holds (fullAir D extra nb np) pub tr) : ev tr 3 r pub e < 256 :=
  WsDecode3.rng_rcv hH hxr (t := 3) (by simp [fullAir, m5aAir]) (by rw [full3]; exact memD_mem hi) hr hg

include hH hxB hxD hxK hN hxr in
/-- **A new node's memory bytes** (`gnew`, `cont = 0`). -/
theorem sn_nmem_bytes {r : Nat} (hr : r < tr.height 3) (hg : ev tr 3 r pub (Sn.c "gnew") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) : ∀ b, b < 8 → ev tr 3 r pub (Sn.c "nmem" b) < 256 := by
  intro b hb
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hnb := sn_flag_le' hc "nref" (Or.inl rfl)
  rcases (by omega : ev tr 3 r pub (Sn.c "nref") = 0 ∨ ev tr 3 r pub (Sn.c "nref") = 1) with h0 | h1
  · exact (sn_new_node hH hxB hxD hxK hN hxr hr hg h0 hcont).1.atMb hb
  · exact rng3 (sn_rng_nmem b hb) hr (ev_one_eval h1) hxr hH

include hH hxB hxD hxK hN hxr in
/-- **A new leaf's payload bytes** (`gnew`, `isL`, `cont = 0`). -/
theorem sn_nx_bytes {r : Nat} (hr : r < tr.height 3) (hg : ev tr 3 r pub (Sn.c "gnew") = 1)
    (hL : ev tr 3 r pub (Sn.c "isL") = 1) (hcont : ev tr 3 r pub (Sn.c "cont") = 0) :
    ∀ t, t < 36 → ev tr 3 r pub (Sn.c "nx" t) < 256 := by
  intro t ht
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hnb := sn_flag_le' hc "nref" (Or.inl rfl)
  rcases (by omega : ev tr 3 r pub (Sn.c "nref") = 0 ∨ ev tr 3 r pub (Sn.c "nref") = 1) with h0 | h1
  · exact (sn_new_node hH hxB hxD hxK hN hxr hr hg h0 hcont).1.atX (by unfold payLen; omega)
  · exact rng3 (sn_rng_nx t ht) hr (ev_one_eval (by rw [ev_hmul, h1, hL])) hxr hH

theorem limbs_of_bytes {r : Nat} {v : Nat → Expr} (h : ∀ b, b < 8 → ev tr 3 r pub (v b) < 256) :
    ∀ k, k < 4 → ev tr 3 r pub (limb16 v k) < 65536 := by
  intro k hk
  rw [ev3_limb16 v k (h _ (by omega)) (h _ (by omega))]
  have := h (2 * k) (by omega); have := h (2 * k + 1) (by omega)
  omega

theorem NM_get (k : Nat) (hk : k < 4) : Sn.NM.getD k 0 = limb16 (fun b => Sn.c "nmem" b) k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl
theorem M_get (k : Nat) (hk : k < 4) : Sn.M.getD k 0 = limb16 (fun b => Sn.c "mem" b) k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> rfl

include hH hxB hxD hxK hN hxr in
/-- **A new node's memory limbs** (`gnew`, `cont = 0`). -/
theorem sn_NM_lt {r : Nat} (hr : r < tr.height 3) (hg : ev tr 3 r pub (Sn.c "gnew") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) : ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536 := by
  intro k hk
  rw [NM_get k hk]
  exact limbs_of_bytes (sn_nmem_bytes hH hxB hxD hxK hN hxr hr hg hcont) k hk

include hH hxB hxD hxK hN hxr hxV in
set_option maxHeartbeats 4000000 in
/-- **An old node's memory limbs** (`gold`, `cont = 0`). -/
theorem sn_M_lt {r : Nat} (hr : r < tr.height 3) (hg : ev tr 3 r pub (Sn.c "gold") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) : ∀ k, k < 4 → ev tr 3 r pub (Sn.M.getD k 0) < 65536 := by
  intro k hk
  rw [M_get k hk]
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hsb := sn_flag_le' hc "gsha" (by simp)
  by_cases hs : ev tr 3 r pub (Sn.c "gsha") = 1
  · exact limbs_of_bytes (fun b hb => (sn_old_node hH hxB hxD hxK hN hxr hr hs hcont).1.atMb hb) k hk
  have hs0 : ev tr 3 r pub (Sn.c "gsha") = 0 := by omega
  have hrd : (Sn.c "gold" - Sn.c "gsha").eval tr 3 r pub = 1 := ev_one_eval (by rw [ev_sub, hg, hs0])
  obtain ⟨r', hr', hco, hp⟩ := sn_rd_part hH hxV hr hrd 0 (by decide)
  have tr0 : ∀ nw, (sRdE 0).map (E tr 3 r pub) = (pE nw 0).map (E tr 3 r' pub) →
      (∀ b, b < 8 → ev tr 3 r' pub (pMB nw b) < 256) → ev tr 3 r pub (limb16 (fun b => Sn.c "mem" b) k) < 65536 := by
    intro nw hm hb
    have e := map_range_eq (fields0 hm).mem k hk
    have e' : ev tr 3 r pub (limb16 (fun b => Sn.c "mem" b) k) = ev tr 3 r' pub (limb16 (pMB nw) k) :=
      congrArg Fp.toNat e
    rw [e']
    exact limbs_of_bytes hb k hk
  rcases hp with ⟨hgs, hm⟩ | ⟨hgn, hm⟩
  · exact tr0 false hm (fun b hb => (sn_old_node hH hxB hxD hxK hN hxr hr' hgs hco).1.atMb hb)
  · exact tr0 true hm (sn_nmem_bytes hH hxB hxD hxK hN hxr hr' hgn hco)

include hH hxB hxD hxK hN hxr in
/-- **The new leaf's memory is `< P`** (`oLR` / `oLM`, `cont = 0`), and its length bytes are bytes. -/
theorem sn_leafMem_lt {r : Nat} (hr : r < tr.height 3)
    (hop : ev tr 3 r pub (Sn.c "oLR") = 1 ∨ ev tr 3 r pub (Sn.c "oLM") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) :
    (∀ t, t < 3 → ev tr 3 r pub (Sn.c "nx" t) < 256) ∧ snNMem tr pub r < P := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  obtain ⟨hfl, h1, h2, h3, h4, h5, h6, -, h9⟩ := sn_ops hc
  have := hfl "oLR" (by simp [snNames]); have := hfl "oLM" (by simp [snNames])
  have := hfl "act" (by simp [snNames])
  have hg : ev tr 3 r pub (Sn.c "gnew") = 1 := by omega
  have hL : ev tr 3 r pub (Sn.c "isL") = 1 := by omega
  have hRM : ev tr 3 r pub (Sn.c "oLR" + Sn.c "oLM") = 1 := by rw [ev_hadd]; omega
  have hb := sn_nmem_bytes hH hxB hxD hxK hN hxr hr hg hcont
  refine ⟨fun t ht => sn_nx_bytes hH hxB hxD hxK hN hxr hr hg hL hcont t (by omega), ?_⟩
  have z : ∀ t, t < 4 → ev tr 3 r pub (Sn.c "nmem" (4 + t)) = 0 := fun t ht =>
    FieldVer.gate_zero (FieldRows.hold rfl hc (sn_mem_nm4 t ht)) hRM
  have h3' : ev tr 3 r pub (Sn.c "nmem" 3) ≤ 1 := by
    have e := FieldRows.hold rfl hc sn_mem_nm3
    have e1 : ev tr 3 r pub ((Sn.c "oLR" + Sn.c "oLM") * Sn.c "nmem" 3) = ev tr 3 r pub (Sn.c "nmem" 3) := by
      rw [ev_hmul, hRM, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _)]
    apply bool_le
    show ev tr 3 r pub (Sn.c "nmem" 3 * (Sn.c "nmem" 3 - 1)) = 0
    rw [ev_hmul] at e ⊢
    rw [e1] at e
    exact e
  have hv : snNMem tr pub r = ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 0) +
      65536 * ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 1) +
      4294967296 * ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 2) +
      281474976710656 * ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 3) := rfl
  rw [hv, ev3_limb16 _ 0 (hb _ (by omega)) (hb _ (by omega)), ev3_limb16 _ 1 (hb _ (by omega)) (hb _ (by omega)),
    ev3_limb16 _ 2 (hb _ (by omega)) (hb _ (by omega)), ev3_limb16 _ 3 (hb _ (by omega)) (hb _ (by omega))]
  have z0 := z 0 (by omega); have z1 := z 1 (by omega); have z2 := z 2 (by omega); have z3 := z 3 (by omega)
  have b0 := hb 0 (by omega); have b1 := hb 1 (by omega); have b2 := hb 2 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero] at z0 z1 z2 z3 b0 b1 b2 h3' ⊢
  omega

end

end StateM5a.SnRange
