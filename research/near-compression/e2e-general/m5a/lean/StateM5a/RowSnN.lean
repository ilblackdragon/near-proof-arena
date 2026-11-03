import StateM5a.RowSnD

/-!
# StateM5a.RowSnN — an `SN` row's new record; `LocalOK` of `oLR` (leaf replace) and `oEU`
(extension descend)

* `snNew` / `snOut`: the record an `SN` row with `gnew` publishes (a leaf `snKey ↦ (vlen nx, nx)`
  with memory `nmem`, or an extension `snKey → (nxf, nx)`) and its output ref (`nref`, `hn`) — the
  `VER` part-0 / SHA-256 payload `nx` of `Sn.rec` / `Sn.serBytes`;
* `sn_mem_eu`: the `memChain (oEU + gfr)` of an `oEU` row: `nmem + uom = mem + unm` exactly, given
  16-bit limbs;
* `sn_leaf_nmem`: the new leaf's memory `leafMem snKey vlen` (`oLR`, `oLM`) — **given
  `snNMem < P`**: the AIR states `limb₀ + 65536·limb₁ = 100 + 2·hplen + vlen` as one field
  equation, so the 32-bit value `limb₀ + 65536·limb₁` may exceed the honest memory by `P`;
* `localOK_oLR` (`BusWalk.step_leafRep`), `localOK_oEU` (`BusWalk.step_extDesc`).
-/

namespace StateM5a.RowSnN

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnF
open StateM5a.RowSnM

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## The new record -/

section
variable (tr : Trace Fp) (pub : List Fp) (r : Nat)

def snNMem : Nat := le4 (Sn.NM.map (sE tr pub r))
def snNVal : Slot :=
  .ref (ev tr 3 r pub (Sn.vlenOf fun t => Sn.c "nx" t)) (bytesOf ((pack2 fun b => Sn.c "nx" (4 + b)).map (sE tr pub r)))
def snNChild : Ref := refOf (sE tr pub r (Sn.c "nxf")) ((pack2 fun b => Sn.c "nx" b).map (sE tr pub r))

/-- **The new record** of an `SN` row (`gnew`). -/
def snNew : Rec :=
  if ev tr 3 r pub (Sn.c "isL") = 1 then .leaf (snKey tr pub r) (snNVal tr pub r) (snNMem tr pub r)
  else .ext (snKey tr pub r) (snNChild tr pub r) (snNMem tr pub r)

/-- The output ref of an `SN` row. -/
def snOut : Ref := refOf (sE tr pub r (Sn.c "nref")) ((pack2 fun b => Sn.c "hn" b).map (sE tr pub r))

end

theorem snNew_leaf {tr : Trace Fp} {pub : List Fp} {r : Nat} (h : ev tr 3 r pub (Sn.c "isL") = 1) :
    snNew tr pub r = .leaf (snKey tr pub r) (snNVal tr pub r) (snNMem tr pub r) := by
  unfold snNew; rw [if_pos h]
theorem snNew_ext {tr : Trace Fp} {pub : List Fp} {r : Nat} (h : ev tr 3 r pub (Sn.c "isL") ≠ 1) :
    snNew tr pub r = .ext (snKey tr pub r) (snNChild tr pub r) (snNMem tr pub r) := by
  unfold snNew; rw [if_neg h]

theorem snpay_vlen (m : Expr) (f : Expr → Fp) :
    (payOf ((payE (fun s j => Sn.c s j) m).map f)).vlen = (f (Sn.c "dvlen")).toNat := rfl

theorem snpay_vh (m : Expr) (f : Expr → Fp) :
    (payOf ((payE (fun s j => Sn.c s j) m).map f)).vh =
      bytesOf (((List.range 16).map fun i => Sn.c "dvh" i).map f) := by
  simp [payOf, payE]
  rw [List.take_of_length_le (by simp)]

/-! ## Constraint membership -/

theorem sn_mem_chainU {e : Expr} (he : e ∈ memChain (Sn.c "oEU" + Sn.c "gfr") Sn.NM
    ((List.range 4).map fun t => (1 - Sn.c "gfr") * Sn.M.getD t 0)
    ((List.range 4).map fun t => Sn.c "unm" t + (if t = 0 then Sn.c "gfr" * Sn.own else 0))
    ((List.range 4).map fun t => (1 - Sn.c "gfr") * Sn.c "uom" t) (fun t => Sn.c "cy" t)) :
    e ∈ Sn.constraints := by
  unfold Sn.constraints; exact List.mem_append_left _ (List.mem_append_right _ he)

theorem sn_mem_vl : (Sn.c "oLR" + Sn.c "oLM") * (Sn.c "dvlen" - Sn.vlenOf fun t => Sn.c "nx" t) ∈ Sn.constraints := by
  unfold Sn.constraints; simp
theorem sn_mem_lm : (Sn.c "oLR" + Sn.c "oLM") * (limb16 (fun b => Sn.c "nmem" b) 0 +
    sm 65536 (limb16 (fun b => Sn.c "nmem" b) 1) - 100 - sm 2 (Sn.c "hplen") - Sn.vlenOf fun t => Sn.c "nx" t) ∈
    Sn.constraints := by
  unfold Sn.constraints; simp
theorem sn_mem_dvh (i : Nat) (hi : i < 16) : (Sn.c "oLR" + Sn.c "oLM") *
    (Sn.c "dvh" i - (sm 256 (Sn.c "nx" (4 + 2 * i)) + Sn.c "nx" (5 + 2 * i))) ∈ Sn.constraints := by
  unfold Sn.constraints
  simp only [List.mem_append, List.mem_map, List.mem_range]
  mem_search i hi
theorem sn_mem_nm0 (t : Nat) (ht : t < 4) : (Sn.c "oLR" + Sn.c "oLM") * Sn.c "nmem" (4 + t) ∈ Sn.constraints := by
  unfold Sn.constraints
  simp only [List.mem_append, List.mem_map, List.mem_range]
  mem_search t ht
theorem sn_mem_rkU : Sn.c "oEU" * (Sn.c "rkc" - K RK_H) ∈ Sn.constraints := by
  unfold Sn.constraints; simp

/-! ## Gated lists -/

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}

theorem map_zip3_fst (g h k : Expr) (hg : g.eval tr 3 r pub = 1) (hh : h.eval tr 3 r pub = 0)
    (hk : k.eval tr 3 r pub = 0) :
    ∀ (A B C : List Expr), A.length = B.length → B.length = C.length →
      (((A.zip B).zip C).map (fun ((p, q), s) => g * p + h * q + k * s)).map (E tr 3 r pub) = A.map (E tr 3 r pub)
  | [], [], [], _, _ => rfl
  | a :: A, b :: B, c :: C, h1, h2 => by
    simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq]
    refine ⟨?_, map_zip3_fst g h k hg hh hk A B C (by simpa using h1) (by simpa using h2)⟩
    simp only [E, eval_add, eval_mul, hg, hh, hk]; grind
  | [], _ :: _, _, h1, _ => by simp at h1
  | _ :: _, [], _, h1, _ => by simp at h1
  | _, [], _ :: _, _, h2 => by simp at h2
  | _, _ :: _, [], _, h2 => by simp at h2

/-- The `gnu` result: the row's output ref. -/
theorem nu_ref (eNu : gnu.eval tr 3 r pub = 1) (eS : Sn.gS.eval tr 3 r pub = 0)
    (eX : Sn.gX.eval tr 3 r pub = 0) :
    refOf (E tr 3 r pub (gnu * Sn.c "nref" + Sn.gS * Sn.c "oref" + Sn.gX * Sn.c "shf"))
        ((((pack2 (fun b => Sn.c "hn" b)).zip (pack2 fun b => Sn.c "ho" b)).zip
          ((List.range 16).map fun i => Sn.c "sh" i)).map
          (fun ((p, q), s) => gnu * p + Sn.gS * q + Sn.gX * s) |>.map (E tr 3 r pub)) = snOut tr pub r := by
  rw [map_zip3_fst gnu Sn.gS Sn.gX eNu eS eX _ _ _ (by simp [pack2]) (by simp [pack2])]
  unfold snOut
  congr 1
  simp only [E, eval_add, eval_mul, eNu, eS, eX]; grind

/-- The `gnu` result: the row's new memory. -/
theorem nu_nm (eNu : gnu.eval tr 3 r pub = 1) (eX : Sn.gX.eval tr 3 r pub = 0) :
    le4 (((Sn.NM.zip ((List.range 4).map fun t => Sn.c "sm" t)).map fun (p, s) => gnu * p + Sn.gX * s).map
      (E tr 3 r pub)) = snNMem tr pub r := by
  rw [map_zip_left gnu Sn.gX (fun p => p) _ eNu eX _ (by simp [Sn.NM, memLimbs])]
  rfl

theorem ev_gm {g x : Expr} (h : ev tr 3 r pub g = 1) : ev tr 3 r pub (g * x) = ev tr 3 r pub x := by
  change ev tr 3 r pub (Expr.mul g x) = _; exact ev_mul_gate _ h

theorem ev_gm0 {g x : Expr} (h : ev tr 3 r pub g = 0) : ev tr 3 r pub (g * x) = 0 := by
  rw [ev_hmul, h]; simp

theorem getD_r4 (f : Nat → Expr) {k : Nat} (hk : k < 4) : ((List.range 4).map f).getD k 0 = f k := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]

end

/-! ## Memory -/

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}

set_option maxHeartbeats 8000000 in
/-- **`oEU` memory**: `nmem + uom = mem + unm` (16-bit limbs). -/
theorem sn_mem_eu (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (eG : ev tr 3 r pub (Sn.c "oEU" + Sn.c "gfr") = 1) (eF : ev tr 3 r pub (Sn.c "gfr") = 0)
    (hM : ∀ k, k < 4 → ev tr 3 r pub (Sn.M.getD k 0) < 65536)
    (hN : ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536)
    (hu : ∀ k, k < 4 → ev tr 3 r pub (Sn.c "unm" k) < 65536)
    (ho : ∀ k, k < 4 → ev tr 3 r pub (Sn.c "uom" k) < 65536) :
    snNMem tr pub r + le4 (((List.range 4).map fun t => Sn.c "uom" t).map (E tr 3 r pub)) =
      snMem tr pub r + le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 r pub)) := by
  have e1 := FieldRows2.ev_one_sub0 (tr := tr) (t := 3) (r := r) (pub := pub) eF
  have em : ∀ k, k < 4 → ev tr 3 r pub (((List.range 4).map fun t => (1 - Sn.c "gfr") * Sn.M.getD t 0).getD k 0) =
      ev tr 3 r pub (Sn.M.getD k 0) := fun k hk => by rw [getD_r4 _ hk, ev_gm e1]
  have eo : ∀ k, k < 4 → ev tr 3 r pub (((List.range 4).map fun t => (1 - Sn.c "gfr") * Sn.c "uom" t).getD k 0) =
      ev tr 3 r pub (Sn.c "uom" k) := fun k hk => by rw [getD_r4 _ hk, ev_gm e1]
  have ep : ∀ k, k < 4 → ev tr 3 r pub (((List.range 4).map fun t =>
      Sn.c "unm" t + (if t = 0 then Sn.c "gfr" * Sn.own else 0)).getD k 0) = ev tr 3 r pub (Sn.c "unm" k) := by
    intro k hk
    rw [getD_r4 _ hk, ev_hadd]
    have : ev tr 3 r pub (if k = 0 then Sn.c "gfr" * Sn.own else 0) = 0 := by
      split
      · exact ev_gm0 eF
      · exact ev_const 0
    rw [this, Nat.add_zero, Nat.mod_eq_of_lt (ev_lt _)]
  have q := memChain_sound _ _ _ _ _ _ (fun e he => FieldRows2.sn_hold hc (sn_mem_chainU he)) eG (by
    intro k hk
    rw [em k hk, ep k hk, eo k hk]
    exact ⟨by have := hN k hk; omega, by have := hM k hk; omega, by have := hu k hk; omega,
      by have := ho k hk; omega⟩)
  unfold V4 at q
  rw [em 0 (by decide), em 1 (by decide), em 2 (by decide), em 3 (by decide),
    ep 0 (by decide), ep 1 (by decide), ep 2 (by decide), ep 3 (by decide),
    eo 0 (by decide), eo 1 (by decide), eo 2 (by decide), eo 3 (by decide)] at q
  unfold snNMem snMem le4
  simp only [Sn.NM, Sn.M, memLimbs, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, E, sE] at q ⊢
  unfold ev at q
  omega

end

/-! ## Leaf memory and value length -/

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}

theorem ev_lit3 (n : Nat) : ev tr 3 r pub (no_index (OfNat.ofNat n : Expr)) = n % P := ev_const n
theorem ev_sm3 (v : Nat) (e : Expr) : ev tr 3 r pub (sm v e) = (v % P) * ev tr 3 r pub e % P := by
  show ev tr 3 r pub (Expr.mul (.const v) e) = _
  rw [ev_mul, ev_const]
theorem ev_K3 (v : Nat) : ev tr 3 r pub (K v) = v % P := ev_const v

theorem pn_length : ∀ l : List Nat, (packNibbles l).length = l.length / 2
  | [] => rfl
  | [_] => by simp [packNibbles]
  | _ :: _ :: rest => by
    simp only [packNibbles, List.length_cons]
    rw [pn_length rest]; omega

/-- `|hexPrefix k b| = |k|/2 + 1`. -/
theorem hp_length (k : List Nat) (b : Bool) : (hexPrefix k b).length = k.length / 2 + 1 := by
  unfold hexPrefix
  dsimp only
  split
  next n rest hpar =>
    rw [List.length_cons, pn_length]
    simp only [List.length_cons] at hpar ⊢
    omega
  next nibs _ => rw [List.length_cons, pn_length]

theorem sub_ev {a b : Expr} {c : Nat} (h : ev tr 3 r pub (a - b) = c) (hc : c < P) :
    ev tr 3 r pub a = (ev tr 3 r pub b + c) % P := by
  rw [ev_sub] at h
  have ha := ev_lt (tr := tr) (t := 3) (r := r) (pub := pub) a
  have hb := ev_lt (tr := tr) (t := 3) (r := r) (pub := pub) b
  generalize ev tr 3 r pub a = A at *
  generalize ev tr 3 r pub b = B at *
  rcases Nat.eq_zero_or_pos B with h0 | h0
  · subst h0
    rw [Nat.sub_zero, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt ha] at h
    rw [Nat.zero_add, Nat.mod_eq_of_lt hc, h]
  · rw [Nat.mod_eq_of_lt (show P - B < P by omega)] at h
    by_cases hl : A < B
    · rw [Nat.mod_eq_of_lt (show A + (P - B) < P by omega)] at h
      rw [← h, show B + (A + (P - B)) = A + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt ha]
    · rw [show A + (P - B) = (A - B) + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
      rw [← h, show B + (A - B) = A by omega, Nat.mod_eq_of_lt ha]

theorem ev_vlenOf_lt (hnx : ∀ t, t < 3 → ev tr 3 r pub (Sn.c "nx" t) < 256) :
    ev tr 3 r pub (Sn.vlenOf fun t => Sn.c "nx" t) < 16777216 := by
  have h0 := hnx 0 (by decide); have h1 := hnx 1 (by decide); have h2 := hnx 2 (by decide)
  unfold Sn.vlenOf
  simp only [ev_hadd, ev_sm3, Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (show 256 * ev tr 3 r pub (Sn.c "nx" 1) < P by omega),
    Nat.mod_eq_of_lt (show 65536 * ev tr 3 r pub (Sn.c "nx" 2) < P by omega),
    Nat.mod_eq_of_lt (show ev tr 3 r pub (Sn.c "nx" 0) + 256 * ev tr 3 r pub (Sn.c "nx" 1) < P by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem snNMem_eq : snNMem tr pub r = ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 0) +
    65536 * ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 1) +
    4294967296 * ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 2) +
    281474976710656 * ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 3) := rfl

theorem ev_limb16_3 (b : Nat → Expr) (k : Nat) : ev tr 3 r pub (limb16 b k) =
    (ev tr 3 r pub (b (2 * k)) + 256 * ev tr 3 r pub (b (2 * k + 1)) % P) % P := by
  unfold limb16; rw [ev_hadd, ev_hmul, ev_K3]

set_option maxHeartbeats 8000000 in
/-- **The new leaf's memory** (`oLR` / `oLM`): `leafMem snKey vlen`, given `snNMem < P` (the AIR's
memory equation is one field equation over two 16-bit limbs). -/
theorem sn_leaf_nmem (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hA : ev tr 3 r pub (Sn.c "act") = 1) (hcont : ev tr 3 r pub (Sn.c "cont") = 0)
    (g : ev tr 3 r pub (Sn.c "oLR" + Sn.c "oLM") = 1)
    (hN : ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536) (hlt : snNMem tr pub r < P)
    (hnx : ∀ t, t < 3 → ev tr 3 r pub (Sn.c "nx" t) < 256) :
    snNMem tr pub r = leafMem (snKey tr pub r) (ev tr 3 r pub (Sn.vlenOf fun t => Sn.c "nx" t)) := by
  have hz : ∀ t, t < 4 → ev tr 3 r pub (Sn.c "nmem" (4 + t)) = 0 := fun t ht =>
    FieldVer.gate_zero (FieldRows2.sn_hold hc (sn_mem_nm0 t ht)) g
  have hm := eq_of_sub (FieldVer.gate_zero (FieldRows2.sn_hold hc sn_mem_lm) g)
  have hv := ev_vlenOf_lt hnx
  have hpl := FieldRows2.sn_hplen hc hA hcont
  have hkl := (FieldRows2.sn_flags hc hcont).1
  have l2 : ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 2) = 0 := by
    rw [ev_limb16_3]; have := hz 0 (by decide); have := hz 1 (by decide); simp_all
  have l3 : ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 3) = 0 := by
    rw [ev_limb16_3]; have := hz 2 (by decide); have := hz 3 (by decide); simp_all
  have n0 : ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 0) < 65536 := hN 0 (by decide)
  have n1 : ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 1) < 65536 := hN 1 (by decide)
  rw [snNMem_eq, l2, l3] at hlt ⊢
  have hH : ev tr 3 r pub (Sn.c "hplen") ≤ 33 := by omega
  have q1 := sub_ev hm (by omega)
  rw [ev_sm3] at q1; simp only [Nat.reduceMod] at q1
  rw [Nat.mod_eq_of_lt (show 2 * ev tr 3 r pub (Sn.c "hplen") < P by omega),
    Nat.mod_eq_of_lt (show 2 * ev tr 3 r pub (Sn.c "hplen") + ev tr 3 r pub (Sn.vlenOf fun t => Sn.c "nx" t) < P by omega)] at q1
  have q2 := sub_ev q1 (by omega)
  rw [ev_lit3] at q2; simp only [Nat.reduceMod] at q2
  rw [Nat.mod_eq_of_lt (by omega)] at q2
  rw [ev_hadd, ev_sm3] at q2; simp only [Nat.reduceMod] at q2
  rw [Nat.mod_eq_of_lt (show 65536 * ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 1) < P by omega),
    Nat.mod_eq_of_lt (by omega)] at q2
  unfold leafMem
  rw [hp_length, snKey_length]
  omega

end

/-! ## `oLR`, `oEU` -/

theorem sn_mem_gfr : Sn.c "gfr" - (Sn.c "oEB" + Sn.c "oEP" + Sn.c "oEM") ∈ Sn.constraints := by
  unfold Sn.constraints; simp

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}

theorem snNMem_lt (hN : ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536) :
    snNMem tr pub r < 18446744073709551616 := by
  have n0 : ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 0) < 65536 := hN 0 (by decide)
  have n1 : ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 1) < 65536 := hN 1 (by decide)
  have n2 : ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 2) < 65536 := hN 2 (by decide)
  have n3 : ev tr 3 r pub (limb16 (fun b => Sn.c "nmem" b) 3) < 65536 := hN 3 (by decide)
  rw [snNMem_eq]; omega

set_option maxHeartbeats 8000000 in
/-- **`SN.oLR`**: upsert at the leaf holding the key: the leaf's value is replaced. -/
theorem localOK_oLR {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hg : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1) (h1 : ev tr 3 r pub (Sn.c "oLR") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) (hd : ev tr 3 r pub (Sn.c "d") + 64 < P)
    (hnib : ∀ j < 64, (Sn.b j).eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d" + K j)]? = some (ev tr 3 r pub (Sn.k j)))
    (hklen : (Sn.c "isL" * (1 - Sn.c "gA")).eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid"))).length = ev tr 3 r pub (Sn.c "d" + Sn.c "klen"))
    (hold : OldOK σ (snIn tr pub r) (snOld tr pub r)) (hnew : NewOK σ (snOut tr pub r) (snNew tr pub r))
    (hN : ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536) (hlt : snNMem tr pub r < P)
    (hnx : ∀ t, t < 3 → ev tr 3 r pub (Sn.c "nx" t) < 256) :
    LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eLR : (Sn.c "oLR").eval tr 3 r pub = 1 := s1
  have eLM : (Sn.c "oLM").eval tr 3 r pub = 0 := s0
  have eU : (Sn.c "mU").eval tr 3 r pub = 1 := s1
  have eD : (Sn.c "mD").eval tr 3 r pub = 0 := s0
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 0 := s0
  have eIsL : (Sn.c "isL").eval tr 3 r pub = 1 := s1
  have eGA : (Sn.c "gA").eval tr 3 r pub = 0 := s0
  have eNu : gnu.eval tr 3 r pub = 1 := by
    have : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eS : Sn.gS.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oES").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eX : Sn.gX.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
    evsn; grind
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 1 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 1
    rw [show Sn.mode.eval tr 3 r pub = 1 by evsn; grind]; rfl
  have hA : ev tr 3 r pub (Sn.c "act") = 1 := by omega
  have g : ev tr 3 r pub (Sn.c "oLR" + Sn.c "oLM") = 1 := eval_one_ev (by simp only [eval_add, eLR, eLM]; grind)
  have hK := sn_key_prefix hc hcont (ev_of_eval eGA) hd hnib
  have hlen := hklen (by evsn; grind)
  rw [ev_hadd, Nat.mod_eq_of_lt (by
    have := (FieldRows2.sn_flags hc hcont).1; omega)] at hlen
  rw [List.drop_eq_nil_of_le (show (keyOf (ev tr 3 r pub (Sn.c "kid"))).length ≤
    ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") by omega), List.append_nil] at hK
  have hvl : ev tr 3 r pub (Sn.c "dvlen") = ev tr 3 r pub (Sn.vlenOf fun t => Sn.c "nx" t) :=
    FieldVer.eq_of_gate (FieldRows2.sn_hold hc sn_mem_vl) g
  have hvh : ((List.range 16).map fun i => Sn.c "dvh" i).map (E tr 3 r pub) =
      (pack2 fun b => Sn.c "nx" (4 + b)).map (E tr 3 r pub) := by
    simp only [pack2, List.map_map]
    apply List.map_congr_left; intro i hi
    have hi' := List.mem_range.1 hi
    have := FieldVer.eq_of_gate (FieldRows2.sn_hold hc (sn_mem_dvh i hi')) g
    simp only [Function.comp, E]
    rw [show 4 + (2 * i + 1) = 5 + 2 * i by omega]
    exact Fp.ext this
  have hmem := sn_leaf_nmem hc hA hcont g hN hlt hnx
  rw [snNew_leaf (by omega)] at hnew
  unfold snNVal at hnew
  rw [snOld_leaf (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_neg (show ¬ snW.gdn.eval tr 3 r pub = 1 from fun h => fp_zero_ne_one' (eGdn.symm.trans h))]
  dsimp only
  rw [sn_din, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid, snpay_vlen, snpay_vh]
  intro x hx1 hx2
  have e1 : ev tr 3 r pub (Sn.vlenOf fun t => Sn.c "nx" t) = x.length := by rw [← hvl]; exact hx1
  have e2 : bytesOf ((pack2 fun b => Sn.c "nx" (4 + b)).map (sE tr pub r)) = sha256 x := by
    rw [← hx2, hvh]
  rw [e1, e2, hmem, e1] at hnew
  refine step_leafRep hold hK ?_ ?_ ?_ ?_ ?_
  · dsimp only; rw [nu_ref eNu eS eX]; exact hnew
  · show le4 _ = le4 _
    rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]
  · dsimp only; rw [nu_nm eNu eX, hmem, e1]
  · have := ev_lt (tr := tr) (t := 3) (r := r) (pub := pub) (Sn.vlenOf fun t => Sn.c "nx" t); omega
  · dsimp only; rw [nu_nm eNu eX]; omega

set_option maxHeartbeats 8000000 in
/-- **`SN.oEU`**: upsert descend through an extension. -/
theorem localOK_oEU {σ : Store} {keyOf : Nat → List Nat}
    (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hg : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1) (h1 : ev tr 3 r pub (Sn.c "oEU") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) (hd : ev tr 3 r pub (Sn.c "d") + 64 < P)
    (hnib : ∀ j < 64, (Sn.b j).eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d" + K j)]? = some (ev tr 3 r pub (Sn.k j)))
    (hold : OldOK σ (snIn tr pub r) (snOld tr pub r)) (hnew : NewOK σ (snOut tr pub r) (snNew tr pub r))
    (hM : ∀ k, k < 4 → ev tr 3 r pub (Sn.M.getD k 0) < 65536)
    (hN : ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536)
    (hu : ∀ k, k < 4 → ev tr 3 r pub (Sn.c "unm" k) < 65536)
    (ho : ∀ k, k < 4 → ev tr 3 r pub (Sn.c "uom" k) < 65536) :
    LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  snfacts hc hg
  have eEU : (Sn.c "oEU").eval tr 3 r pub = 1 := s1
  have eEB : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
  have eES : (Sn.c "oES").eval tr 3 r pub = 0 := s0
  have eU : (Sn.c "mU").eval tr 3 r pub = 1 := s1
  have eD : (Sn.c "mD").eval tr 3 r pub = 0 := s0
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 1 := s1
  have eGA : (Sn.c "gA").eval tr 3 r pub = 0 := s0
  have eNu : gnu.eval tr 3 r pub = 1 := by
    have : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eS : Sn.gS.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
    evsn; grind
  have eX : Sn.gX.eval tr 3 r pub = 0 := by
    have : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
    have : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
    evsn; grind
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 1 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 1
    rw [show Sn.mode.eval tr 3 r pub = 1 by evsn; grind]; rfl
  have hF : ev tr 3 r pub (Sn.c "gfr") = 0 := by
    have a1 : ev tr 3 r pub (Sn.c "oEB") = 0 := by omega
    have a2 : ev tr 3 r pub (Sn.c "oEP") = 0 := by omega
    have a3 : ev tr 3 r pub (Sn.c "oEM") = 0 := by omega
    rw [eq_of_sub (FieldRows2.sn_hold hc sn_mem_gfr), ev_hadd, ev_hadd, a1, a2, a3]
  have eG : ev tr 3 r pub (Sn.c "oEU" + Sn.c "gfr") = 1 := by rw [ev_hadd, hF, h1]
  have hmem := sn_mem_eu hc eG hF hM hN hu ho
  have hK := sn_key_prefix hc hcont (ev_of_eval eGA) hd hnib
  have hkl : ev tr 3 r pub (Sn.c "d" + Sn.c "klen") = ev tr 3 r pub (Sn.c "d") + (snKey tr pub r).length := by
    rw [snKey_length, ev_hadd, Nat.mod_eq_of_lt (by have := (FieldRows2.sn_flags hc hcont).1; omega)]
  rw [← snKey_length] at hK
  rw [snOld_ext (by omega)] at hold
  rw [snNew_ext (by omega)] at hnew
  have cref : refOf (E tr 3 r pub ((Sn.c "oEU" + Sn.c "oEB") * Sn.c "nxf" + Sn.c "oES" * Sn.c "xf"))
        ((((pack2 (fun b => Sn.c "nx" b)).zip (pack2 fun b => Sn.c "x" b)).map
          (fun (p, q) => (Sn.c "oEU" + Sn.c "oEB") * p + Sn.c "oES" * q)).map (E tr 3 r pub)) =
      snNChild tr pub r := by
    rw [map_zip_left (Sn.c "oEU" + Sn.c "oEB") (Sn.c "oES") (fun p => p) _ (by evsn; grind) eES _
      (by simp [pack2])]
    unfold snNChild; congr 1; simp only [E, eval_add, eval_mul, eEU, eEB, eES]; grind
  have cnm : le4 (((List.range 4).map fun t => (Sn.c "oEU" + Sn.c "oEB") * Sn.c "unm" t).map (E tr 3 r pub)) =
      le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 r pub)) := by
    rw [map_gate (Sn.c "oEU" + Sn.c "oEB") (fun t => Sn.c "unm" t) (by evsn; grind), List.map_map]; rfl
  unfold LocalOK
  simp only [snRow]
  rw [if_pos (show snW.gdn.eval tr 3 r pub = 1 from eGdn)]
  dsimp only
  rw [sn_din, sn_dout, sn_uin, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid, hkl]
  intro hch x hx1 hx2
  refine step_extDesc hold hK ?_ ?_ ?_ ?_ (hch x hx1 hx2)
  · dsimp only; rw [nu_ref eNu eS eX, cref, cnm]
    have : snMem tr pub r + le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 r pub)) -
        le4 (((List.range 4).map fun t => Sn.c "uom" t).map (E tr 3 r pub)) = snNMem tr pub r := by omega
    rw [this]; exact hnew
  · show le4 _ = le4 _
    rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]
  · dsimp only; rw [nu_nm eNu eX, cnm]; omega
  · dsimp only; rw [nu_nm eNu eX]; exact snNMem_lt hN

end

end StateM5a.RowSnN
