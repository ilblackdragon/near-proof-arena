import StateM5a.RowSnMsg

/-!
# StateM5a.RowSnF — `LocalOK` of the `SN` find rows (`oLF`, `oEF`; key facts)

For a decoded `SN` walk row (`snRow`) with a head key (`cont = 0`): from the table's constraints,
the row's old record (`OldOK σ snIn snOld`, a premise: `VER` / SHA-256, as for `BR`), the `NIB` /
`KLEN` lookups in interface form (`KeyLookups.sn_nib`, `sn_klen_leaf`) and the depth bound, the
row's `LocalOK (Sem σ keyOf)` — via `BusWalk.step_leafHit` / `step_extFind`.

* `sn_key_prefix`: with `gA = 0` (every key nibble looked up against the walk key) the walk key
  from depth `d` starts with the row's key: `K.drop d = snKey ++ K.drop (d + klen)`;
* `localOK_oLF` (find hit at a leaf), `localOK_oEF` (find through an extension).
-/

namespace StateM5a.RowSnF

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowSn StateM5a.RowSnMsg

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Keys -/

theorem drop_prefix {K : List Nat} {d L : Nat} {kk : Nat → Nat} (h : ∀ j < L, K[d + j]? = some (kk j)) :
    K.drop d = (List.range L).map kk ++ K.drop (d + L) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop]
  by_cases hi : i < L
  · rw [List.getElem?_append_left (by simp; omega), h i hi, List.getElem?_map, List.getElem?_range hi]; rfl
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop]
    simp only [List.length_map, List.length_range]
    congr 1; omega

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}

theorem sn_mem_ba (j : Nat) (hj : j < 64) : (1 - Sn.c "gA") * (Sn.b j - Sn.a j) ∈ Sn.constraints := by
  unfold Sn.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  mem_search j hj

theorem sn_b_lt (j : Nat) (hj : j < 64) : Sn.b j = Sn.c "b" j := by simp [Sn.b, KMAX, hj]

/-- With `gA = 0`, the looked-up nibbles are the key's: `b_j = a_j`. -/
theorem sn_b_eq_a (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hA : ev tr 3 r pub (Sn.c "gA") = 0) (j : Nat) (hj : j < 64) :
    ev tr 3 r pub (Sn.b j) = ev tr 3 r pub (Sn.a j) := by
  have h := FieldRows2.sn_hold hc (sn_mem_ba j hj)
  change ev tr 3 r pub (Expr.mul _ _) = 0 at h
  rw [ev_mul_gate _ (FieldRows2.ev_one_sub0 hA)] at h
  exact eq_of_sub h

theorem ev_dK (j : Nat) (hd : ev tr 3 r pub (Sn.c "d") + j < P) :
    ev tr 3 r pub (Sn.c "d" + K j) = ev tr 3 r pub (Sn.c "d") + j := by
  rw [ev_hadd, show K j = Expr.const j from rfl, ev_const]
  omega

/-- **The walk key starts with the row's key** (every key nibble looked up: `gA = 0`). -/
theorem sn_key_prefix {keyOf : Nat → List Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) (hA : ev tr 3 r pub (Sn.c "gA") = 0)
    (hd : ev tr 3 r pub (Sn.c "d") + 64 < P)
    (hnib : ∀ j < 64, (Sn.b j).eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d" + K j)]? = some (ev tr 3 r pub (Sn.k j))) :
    (keyOf (ev tr 3 r pub (Sn.c "kid"))).drop (ev tr 3 r pub (Sn.c "d")) =
      snKey tr pub r ++ (keyOf (ev tr 3 r pub (Sn.c "kid"))).drop
        (ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen")) := by
  obtain ⟨hL, hf⟩ := FieldRows2.sn_flags hc hcont
  apply drop_prefix
  intro j hj
  have hj64 : j < 64 := by omega
  have hb : ev tr 3 r pub (Sn.b j) = 1 := by
    rw [sn_b_eq_a hc hA j hj64, FieldRows2.sn_a_lt j hj64, hf j hj64, if_pos hj]
  have := hnib j hj64 (fp_of_ev1 hb)
  rw [ev_dK j (by omega), FieldRows2.sn_k_lt j hj64] at this
  exact this

end

/-! ## Find ops -/

theorem snpay_mode (m : Expr) (f : Expr → Fp) :
    (payOf ((payE (fun s j => Sn.c s j) m).map f)).mode = (f m).toNat := rfl
theorem snpay_kid (m : Expr) (f : Expr → Fp) :
    (payOf ((payE (fun s j => Sn.c s j) m).map f)).kid = (f (Sn.c "kid")).toNat := rfl

/-- Field values of composite expressions, goal only. -/
macro "evsn" : tactic => `(tactic| simp only [eval_add, eval_sub, eval_mul, eval_sm, eval_K, eval_lit,
  Sn.mode, Sn.gS, Sn.gX, Sn.vlenOf, rkE, gnu])

macro "s0" : term => `(fp_of_ev0 (by omega))
macro "s1" : term => `(fp_of_ev1 (by omega))

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem fp_zero_ne_one' : (0 : Fp) ≠ 1 := by decide

set_option maxHeartbeats 4000000 in
/-- **`SN.oLF`**: find hit at a leaf. -/
theorem localOK_oLF {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hg : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1) (h1 : ev tr 3 r pub (Sn.c "oLF") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) (hd : ev tr 3 r pub (Sn.c "d") + 64 < P)
    (hnib : ∀ j < 64, (Sn.b j).eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d" + K j)]? = some (ev tr 3 r pub (Sn.k j)))
    (hklen : (Sn.c "isL" * (1 - Sn.c "gA")).eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d" + Sn.c "klen"))
    (hold : OldOK σ (snIn tr pub r) (snOld tr pub r)) :
    LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eLF : (Sn.c "oLF").eval tr 3 r pub = 1 := s1
  have eEF : (Sn.c "oEF").eval tr 3 r pub = 0 := s0
  have eED : (Sn.c "oED").eval tr 3 r pub = 0 := s0
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 0 := s0
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 0 := s0
  have eIsL : (Sn.c "isL").eval tr 3 r pub = 1 := s1
  have eGA : (Sn.c "gA").eval tr 3 r pub = 0 := s0
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 0 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 0
    rw [show Sn.mode.eval tr 3 r pub = 0 by evsn; grind]; rfl
  have hK := sn_key_prefix hc hcont (ev_of_eval eGA) hd hnib
  have hlen := hklen (by evsn; grind)
  rw [ev_hadd, Nat.mod_eq_of_lt (by
    have := (FieldRows2.sn_flags hc hcont).1; omega)] at hlen
  rw [List.drop_eq_nil_of_le (show (keyOf (ev tr 3 r pub (Sn.c "kid"))).length ≤
    ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") by omega), List.append_nil] at hK
  unfold LocalOK
  simp only [snRow]
  rw [if_neg (show ¬ snW.gdn.eval tr 3 r pub = 1 from fun h => fp_zero_ne_one' (eGdn.symm.trans h))]
  dsimp only
  rw [sn_din, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid]
  refine step_leafHit (k := snKey tr pub r) (m := snMem tr pub r) ?_ hK ?_
  · have e1 : snOld tr pub r = .leaf (snKey tr pub r) (snVal tr pub r) (snMem tr pub r) := by
      unfold snOld; rw [if_pos (by omega)]
    have e2 : snVal tr pub r = .ref (ev tr 3 r pub (Sn.c "oLF" * Sn.vlenOf (fun t => Sn.c "x" t) +
        (Sn.c "oEF" + Sn.c "oED") * Sn.c "alen"))
        (bytesOf (((pack2 fun b => Sn.c "x" (4 + b)).zip ((List.range 16).map fun i => Sn.c "avh" i)).map
          (fun (p, q) => Sn.c "oLF" * p + (Sn.c "oEF" + Sn.c "oED") * q) |>.map (E tr 3 r pub))) := by
      unfold snVal
      rw [map_zip_left (Sn.c "oLF") (Sn.c "oEF" + Sn.c "oED") (fun p => p) _ eLF (by evsn; grind) _
        (by simp [pack2])]
      congr 1
      apply ev_eq_of_eval; evsn; grind
    rw [e1, e2] at hold
    exact hold
  · exact eval_one_ev (by evsn; grind)

end

theorem snKey_length {tr : Trace Fp} {pub : List Fp} {r : Nat} :
    (snKey tr pub r).length = ev tr 3 r pub (Sn.c "klen") := by
  simp [snKey, FieldRows2.keyOf]

set_option maxHeartbeats 4000000 in
/-- **`SN.oEF`**: find through an extension: the child's answer. -/
theorem localOK_oEF {tr : Trace Fp} {pub : List Fp} {r : Nat} {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hg : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1) (h1 : ev tr 3 r pub (Sn.c "oEF") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) (hd : ev tr 3 r pub (Sn.c "d") + 64 < P)
    (hnib : ∀ j < 64, (Sn.b j).eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d" + K j)]? = some (ev tr 3 r pub (Sn.k j)))
    (hold : OldOK σ (snIn tr pub r) (snOld tr pub r)) :
    LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eLF : (Sn.c "oLF").eval tr 3 r pub = 0 := s0
  have eEF : (Sn.c "oEF").eval tr 3 r pub = 1 := s1
  have eED : (Sn.c "oED").eval tr 3 r pub = 0 := s0
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 0 := s0
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 1 := s1
  have eGA : (Sn.c "gA").eval tr 3 r pub = 0 := s0
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 0 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 0
    rw [show Sn.mode.eval tr 3 r pub = 0 by evsn; grind]; rfl
  have hK := sn_key_prefix hc hcont (ev_of_eval eGA) hd hnib
  have hkl : ev tr 3 r pub (Sn.c "d" + Sn.c "klen") = ev tr 3 r pub (Sn.c "d") + (snKey tr pub r).length := by
    rw [snKey_length, ev_hadd, Nat.mod_eq_of_lt (by have := (FieldRows2.sn_flags hc hcont).1; omega)]
  rw [← snKey_length] at hK
  have e1 : snOld tr pub r = .ext (snKey tr pub r) (snChild tr pub r) (snMem tr pub r) := by
    unfold snOld; rw [if_neg (by omega)]
  rw [e1] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_pos (show snW.gdn.eval tr 3 r pub = 1 from eGdn)]
  dsimp only
  rw [sn_din, sn_dout, sn_uin, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid, hkl]
  intro hch
  refine step_extFind hold hK ?_ ?_ ?_ hch
  · apply ev_eq_of_eval; evsn; grind
  · apply ev_eq_of_eval; evsn; grind
  · show bytesOf _ = bytesOf _
    rw [map_zip_right (Sn.c "oLF") (Sn.c "oEF" + Sn.c "oED") (fun p => p) _ eLF (by evsn; grind) _
      (by simp [pack2]), map_gate (Sn.c "oEF" + Sn.c "oED") (fun i => Sn.c "avh" i) (by evsn; grind),
      List.map_map]
    rfl

end StateM5a.RowSnF
