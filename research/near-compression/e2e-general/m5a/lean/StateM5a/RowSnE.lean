import StateM5a.RowSnN

/-!
# StateM5a.RowSnE — `LocalOK` of the `SN` delete rows through an extension (`oES`, `oEB`, `oED`)

* `localOK_oES` (child `SAME`: the extension is `SAME`, `BusWalk.step_extSame`);
* `localOK_oEB` (child a kept branch `HB`: a new extension over the branch's new ref, memory
  `extOwnMem k + nm` from the `memChain (oEU + gfr)` with `gfr = 1`; `BusWalk.step_extBranch`);
* `localOK_oED` (child a leaf descriptor `LD`: the extension's key joins the leaf's; the key's
  nibbles are looked up against `kid2` too; `BusWalk.step_extLeaf`).
-/

namespace StateM5a.RowSnE

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnF
open StateM5a.RowSnM StateM5a.RowSnD StateM5a.RowSnN

local notation "P" => 2013265921

set_option maxRecDepth 100000

theorem sn_mem_rkB : Sn.c "oEB" * (Sn.c "rkc" - K RK_HB) ∈ Sn.constraints := by
  unfold Sn.constraints; simp
theorem sn_mem_rkD : Sn.c "oED" * (Sn.c "rkc" - K RK_LD) ∈ Sn.constraints := by
  unfold Sn.constraints; simp

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}

theorem ev_own (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hA : ev tr 3 r pub (Sn.c "act") = 1) (hcont : ev tr 3 r pub (Sn.c "cont") = 0) :
    ev tr 3 r pub Sn.own = extOwnMem (snKey tr pub r) ∧ ev tr 3 r pub Sn.own ≤ 116 := by
  have hpl := FieldRows2.sn_hplen hc hA hcont
  have hkl := (FieldRows2.sn_flags hc hcont).1
  unfold Sn.own extOwnMem
  rw [ev_hadd, ev_sm3, ev_lit3, hp_length, snKey_length, hpl]
  simp only [Nat.reduceMod]
  rw [Nat.mod_eq_of_lt (show 2 * (1 + ev tr 3 r pub (Sn.c "klen") / 2) < P by omega), Nat.mod_eq_of_lt (by omega)]
  omega

set_option maxHeartbeats 8000000 in
/-- **`oEB` memory**: `nmem = unm + extOwnMem k` (16-bit limbs). -/
theorem sn_mem_eb (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hA : ev tr 3 r pub (Sn.c "act") = 1) (hcont : ev tr 3 r pub (Sn.c "cont") = 0)
    (eG : ev tr 3 r pub (Sn.c "oEU" + Sn.c "gfr") = 1) (eF : ev tr 3 r pub (Sn.c "gfr") = 1)
    (hN : ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536)
    (hu : ∀ k, k < 4 → ev tr 3 r pub (Sn.c "unm" k) < 65536) :
    snNMem tr pub r = extOwnMem (snKey tr pub r) + le4 (((List.range 4).map fun t => Sn.c "unm" t).map (E tr 3 r pub)) := by
  obtain ⟨hown, hown'⟩ := ev_own hc hA hcont
  have e1 := FieldWsb.ev_one_sub1 (tr := tr) (t := 3) (r := r) (pub := pub) eF
  have em : ∀ k, k < 4 → ev tr 3 r pub (((List.range 4).map fun t => (1 - Sn.c "gfr") * Sn.M.getD t 0).getD k 0) = 0 :=
    fun k hk => by rw [getD_r4 _ hk, ev_gm0 e1]
  have eo : ∀ k, k < 4 → ev tr 3 r pub (((List.range 4).map fun t => (1 - Sn.c "gfr") * Sn.c "uom" t).getD k 0) = 0 :=
    fun k hk => by rw [getD_r4 _ hk, ev_gm0 e1]
  have ep0 : ev tr 3 r pub (((List.range 4).map fun t =>
      Sn.c "unm" t + (if t = 0 then Sn.c "gfr" * Sn.own else 0)).getD 0 0) =
      ev tr 3 r pub (Sn.c "unm" 0) + ev tr 3 r pub Sn.own := by
    rw [getD_r4 _ (by decide), ev_hadd, if_pos rfl, ev_gm eF]
    have := hu 0 (by decide); omega
  have ep : ∀ k, 0 < k → k < 4 → ev tr 3 r pub (((List.range 4).map fun t =>
      Sn.c "unm" t + (if t = 0 then Sn.c "gfr" * Sn.own else 0)).getD k 0) = ev tr 3 r pub (Sn.c "unm" k) := by
    intro k hk0 hk
    rw [getD_r4 _ hk, ev_hadd, if_neg (by omega), ev_lit3, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt (ev_lt _)]
  have q := memChain_sound _ _ _ _ _ _ (fun e he => FieldRows2.sn_hold hc (sn_mem_chainU he)) eG (by
    intro k hk
    rw [em k hk, eo k hk]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [ep0]; exact ⟨by have := hN 0 hk; omega, by omega, by have := hu 0 hk; omega, by omega⟩
    · rw [ep k hk0 hk]; exact ⟨by have := hN k hk; omega, by omega, by have := hu k hk; omega, by omega⟩)
  unfold V4 at q
  rw [em 0 (by decide), em 1 (by decide), em 2 (by decide), em 3 (by decide),
    ep0, ep 1 (by decide) (by decide), ep 2 (by decide) (by decide), ep 3 (by decide) (by decide),
    eo 0 (by decide), eo 1 (by decide), eo 2 (by decide), eo 3 (by decide)] at q
  rw [← hown]
  unfold snNMem le4
  simp only [Sn.NM, memLimbs, List.range, List.range.loop, List.map_cons, List.map_nil,
    List.getD_cons_zero, List.getD_cons_succ, List.getD_nil, E, sE] at q ⊢
  unfold ev at q hown'
  unfold ev
  omega

end

/-! ## Leaf descriptors -/

theorem limbBytes_length : ∀ l : List Nat, (Tape.limbBytes l).length = 2 * l.length
  | [] => rfl
  | _ :: l => by simp only [Tape.limbBytes, List.length_cons, limbBytes_length l]; omega

theorem bytesOf_length (l : List Fp) : (bytesOf l).length = 2 * l.length := by
  unfold bytesOf; rw [limbBytes_length, List.length_map]

/-- A leaf descriptor's leaf is well-formed (key nibbles `< 16`, length `≤ 2^21`). -/
theorem leaf_wf (k : List Nat) (len : Nat) (vh : Bytes) (hk : ∀ y ∈ k, y < 16) (hkl : k.length ≤ 2 ^ 21)
    (hlen : len < P) (hvh : vh.length = 32) : (PTrie.leaf k (.ref len vh) (leafMem k len)).wf = true := by
  simp only [PTrie.wf, nibblesOk, slotOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq]
  refine ⟨⟨⟨fun y hy => hk y hy, by omega, hvh⟩, ?_⟩, ?_⟩
  · unfold leafMem; rw [hp_length]; omega
  · rw [hp_length]; omega

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp}

/-- **The row's key is also `kid2`'s** (`g2 = 1`: every key nibble looked up against `kid2`). -/
theorem sn_key2_prefix {keyOf : Nat → List Nat} (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) (hg2 : ev tr 3 r pub (Sn.c "g2") = 1)
    (hd : ev tr 3 r pub (Sn.c "d") + 64 < P)
    (hnib2 : ∀ j < 64, (Sn.c "g2" * Sn.a j).eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid2")))[ev tr 3 r pub (Sn.c "d" + K j)]? = some (ev tr 3 r pub (Sn.k j))) :
    (keyOf (ev tr 3 r pub (Sn.c "kid2"))).drop (ev tr 3 r pub (Sn.c "d")) =
      snKey tr pub r ++ (keyOf (ev tr 3 r pub (Sn.c "kid2"))).drop
        (ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen")) := by
  obtain ⟨hL, hf⟩ := FieldRows2.sn_flags hc hcont
  apply drop_prefix
  intro j hj
  have hj64 : j < 64 := by omega
  have ha : ev tr 3 r pub (Sn.a j) = 1 := by
    rw [FieldRows2.sn_a_lt j hj64, hf j hj64, if_pos hj]
  have := hnib2 j hj64 (fp_of_ev1 (by rw [ev_gm hg2]; exact ha))
  rw [ev_dK j (by omega), FieldRows2.sn_k_lt j hj64] at this
  exact this

end

/-! ## The delete rows through an extension -/

/-- The ops of an active `SN` delete row through an extension (`oES`, `oEB` or `oED`): the find and
upsert ops are `0`, `mD = 1`, the delete ops sum to `1`.  (Stated on naturals: `omega` over the full
op bundle with every flag's bound is slow on these rows.) -/
theorem d_vals (lf ef la ea lr eu lx ex ld ed lz ez es eb mF mU mD : Nat) (_b1 : lf ≤ 1) (_b2 : ef ≤ 1)
    (_b3 : la ≤ 1) (_b4 : ea ≤ 1) (_b5 : lr ≤ 1) (_b6 : eu ≤ 1) (_b7 : lx ≤ 1) (_b8 : ex ≤ 1) (_b9 : ld ≤ 1)
    (_b10 : ed ≤ 1) (_b11 : lz ≤ 1) (_b12 : ez ≤ 1) (_b13 : es ≤ 1) (_b14 : eb ≤ 1)
    (hs : mF + mU + mD = 1) (hF : lf + ef + la + ea = mF) (hU : lr + eu + lx + ex = mU)
    (hD : ld + ed + lz + ez + es + eb = mD) (h : es = 1 ∨ eb = 1 ∨ ed = 1) :
    lf = 0 ∧ ef = 0 ∧ la = 0 ∧ ea = 0 ∧ lr = 0 ∧ eu = 0 ∧ lx = 0 ∧ ex = 0 ∧ mF = 0 ∧ mU = 0 ∧ mD = 1 ∧
      ld + ed + lz + ez + es + eb = 1 := by
  omega

/-- The op bundle of an `oES` / `oEB` / `oED` row, without the flags' bounds (see `d_vals`). -/
macro "dfacts" hc:term:max hg:term:max h:term:max : tactic => `(tactic| (
  obtain ⟨hb, _, _, _, _, _, hs, hF, hU, hD, _, _, _, _, _⟩ := sn_flags' $hc $hg
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _⟩ := d_vals _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hb "oLF" (by simp [snNames])) (hb "oEF" (by simp [snNames])) (hb "oLA" (by simp [snNames]))
    (hb "oEA" (by simp [snNames])) (hb "oLR" (by simp [snNames])) (hb "oEU" (by simp [snNames]))
    (hb "oLX" (by simp [snNames])) (hb "oEX" (by simp [snNames])) (hb "oLD" (by simp [snNames]))
    (hb "oED" (by simp [snNames])) (hb "oLZ" (by simp [snNames])) (hb "oEZ" (by simp [snNames]))
    (hb "oES" (by simp [snNames])) (hb "oEB" (by simp [snNames])) hs hF hU hD $h
  clear hb))

section
variable {tr : Trace Fp} {r : Nat} {pub : List Fp} {σ : Store} {keyOf : Nat → List Nat}
  (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
  (hg : ev tr 3 r pub (Sn.c "mF" + Sn.c "mU" + Sn.c "mD") = 1)
  (hcont : ev tr 3 r pub (Sn.c "cont") = 0) (hd : ev tr 3 r pub (Sn.c "d") + 64 < P)
  (hnib : ∀ j < 64, (Sn.b j).eval tr 3 r pub = 1 →
    (keyOf (ev tr 3 r pub (Sn.c "kid")))[ev tr 3 r pub (Sn.c "d" + K j)]? = some (ev tr 3 r pub (Sn.k j)))
  (hold : OldOK σ (snIn tr pub r) (snOld tr pub r))
include hc hg hcont hd hnib hold

set_option maxHeartbeats 8000000 in
/-- **`SN.oES`**: delete below an extension whose child is `SAME`: the extension is `SAME`. -/
theorem localOK_oES (h1 : ev tr 3 r pub (Sn.c "oES") = 1) : LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  dfacts hc hg (Or.inl h1)
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 1 := s1
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 1 := s1
  have eGA : (Sn.c "gA").eval tr 3 r pub = 0 := s0
  have a1 : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
  have a2 : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
  have a3 : (Sn.c "oED").eval tr 3 r pub = 0 := s0
  have a4 : (Sn.c "oLD").eval tr 3 r pub = 0 := s0
  have a5 : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
  have a6 : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
  have a7 : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
  have a8 : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
  have a9 : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
  have a10 : (Sn.c "oES").eval tr 3 r pub = 1 := s1
  have eNu : gnu.eval tr 3 r pub = 0 := by simp only [gnu, eval_add, a1, a2, a5]; grind
  have eS : Sn.gS.eval tr 3 r pub = 1 := by simp only [Sn.gS, eval_add, a8, a9, a10]; grind
  have eX : Sn.gX.eval tr 3 r pub = 0 := by simp only [Sn.gX, eval_add, a6, a7]; grind
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 2 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 2
    rw [show Sn.mode.eval tr 3 r pub = 2 by evsn; grind]; rfl
  have hrk : ev tr 3 r pub rkE = RK_SAME := by
    rw [ev_eq_of_eval (b := K RK_SAME) (by
      simp only [rkE, Sn.gS, Sn.gX, eval_add, eval_mul, eval_sm, eval_K, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
      grind)]
    simp [K, RK_SAME]
  have hrkc : ev tr 3 r pub (Sn.c "rkc") = RK_SAME := by
    rw [FieldVer.eq_of_gate (FieldRows2.sn_hold hc sn_mem_rkS) h1, ev_K3]; rfl
  have hK := sn_key_prefix hc hcont (ev_of_eval eGA) hd hnib
  have hkl : ev tr 3 r pub (Sn.c "d" + Sn.c "klen") = ev tr 3 r pub (Sn.c "d") + (snKey tr pub r).length := by
    rw [snKey_length, ev_hadd, Nat.mod_eq_of_lt (by have := (FieldRows2.sn_flags hc hcont).1; omega)]
  rw [← snKey_length] at hK
  rw [snOld_ext (by omega)] at hold
  unfold LocalOK
  simp only [snRow]
  rw [if_pos (show snW.gdn.eval tr 3 r pub = 1 from eGdn)]
  dsimp only
  rw [sn_din, sn_dout, sn_uin, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid, hkl]
  intro hch
  refine step_extSame hold hK hrkc hrk (same_ref eNu eS eX) ?_ hch
  show le4 _ = le4 _
  rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]

set_option maxHeartbeats 8000000 in
/-- **`SN.oEB`**: delete below an extension whose child is a kept branch (`HB`): a new extension
over the branch's new ref (`HE`), memory `extOwnMem k + nm`. -/
theorem localOK_oEB (h1 : ev tr 3 r pub (Sn.c "oEB") = 1)
    (hnew : NewOK σ (snOut tr pub r) (snNew tr pub r))
    (hN : ∀ k, k < 4 → ev tr 3 r pub (Sn.NM.getD k 0) < 65536)
    (hu : ∀ k, k < 4 → ev tr 3 r pub (Sn.c "unm" k) < 65536) :
    LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  have hA : ev tr 3 r pub (Sn.c "act") = 1 := (sn_flags' hc hg).2.1
  have b2 : ev tr 3 r pub (Sn.c "oEP") = 0 := (sn_flags' hc hg).2.2.2.2.1
  have b3 : ev tr 3 r pub (Sn.c "oEM") = 0 := (sn_flags' hc hg).2.2.2.2.2.1
  dfacts hc hg (Or.inr (Or.inl h1))
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 1 := s1
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 1 := s1
  have eGA : (Sn.c "gA").eval tr 3 r pub = 0 := s0
  have a1 : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
  have a2 : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
  have a3 : (Sn.c "oED").eval tr 3 r pub = 0 := s0
  have a4 : (Sn.c "oLD").eval tr 3 r pub = 0 := s0
  have a5 : (Sn.c "oEB").eval tr 3 r pub = 1 := s1
  have a6 : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
  have a7 : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
  have a8 : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
  have a9 : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
  have a10 : (Sn.c "oES").eval tr 3 r pub = 0 := s0
  have eNu : gnu.eval tr 3 r pub = 1 := by simp only [gnu, eval_add, a1, a2, a5]; grind
  have eS : Sn.gS.eval tr 3 r pub = 0 := by simp only [Sn.gS, eval_add, a8, a9, a10]; grind
  have eX : Sn.gX.eval tr 3 r pub = 0 := by simp only [Sn.gX, eval_add, a6, a7]; grind
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 2 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 2
    rw [show Sn.mode.eval tr 3 r pub = 2 by evsn; grind]; rfl
  have hrk : ev tr 3 r pub rkE = RK_HE := by
    rw [ev_eq_of_eval (b := K RK_HE) (by
      simp only [rkE, Sn.gS, Sn.gX, eval_add, eval_mul, eval_sm, eval_K, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
      grind)]
    simp [K, RK_HE]
  have hrkc : ev tr 3 r pub (Sn.c "rkc") = RK_HB := by
    rw [FieldVer.eq_of_gate (FieldRows2.sn_hold hc sn_mem_rkB) h1, ev_K3]; rfl
  have hF : ev tr 3 r pub (Sn.c "gfr") = 1 := by
    rw [eq_of_sub (FieldRows2.sn_hold hc sn_mem_gfr), ev_hadd, ev_hadd, h1, b2, b3]
  have eG : ev tr 3 r pub (Sn.c "oEU" + Sn.c "gfr") = 1 := by
    rw [ev_hadd, hF, ev_of_eval a2]
  have hmem := sn_mem_eb hc hA hcont eG hF hN hu
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
    rw [map_zip_left (Sn.c "oEU" + Sn.c "oEB") (Sn.c "oES") (fun p => p) _ (by evsn; grind) a10 _
      (by simp [pack2])]
    unfold snNChild; congr 1; simp only [E, eval_add, eval_mul, a2, a5, a10]; grind
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
  intro hch
  refine step_extBranch hold hK hrkc hrk ?_ ?_ ?_ ?_ hch
  · dsimp only; rw [nu_ref eNu eS eX, cref, cnm, ← hmem]; exact hnew
  · show le4 _ = le4 _
    rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]
  · dsimp only; rw [nu_nm eNu eX, cnm]; exact hmem
  · dsimp only; rw [nu_nm eNu eX]; exact snNMem_lt hN

set_option maxHeartbeats 8000000 in
/-- **`SN.oED`**: delete below an extension whose child is a leaf descriptor (`LD`): the
extension's key joins the leaf's (`extendChild`), result `LD` with start `d`. -/
theorem localOK_oED (h1 : ev tr 3 r pub (Sn.c "oED") = 1)
    (hnib2 : ∀ j < 64, (Sn.c "g2" * Sn.a j).eval tr 3 r pub = 1 →
      (keyOf (ev tr 3 r pub (Sn.c "kid2")))[ev tr 3 r pub (Sn.c "d" + K j)]? = some (ev tr 3 r pub (Sn.k j)))
    (hkey : ∀ K, (∀ y ∈ keyOf K, y < 16) ∧ (keyOf K).length ≤ 2 ^ 21) :
    LocalOK (Sem σ keyOf) (snRow tr pub r) := by
  have hg2' := (sn_flags' hc hg).2.2.2.2.2.2.2.2.2.2.2.2.2.2
  dfacts hc hg (Or.inr (Or.inr h1))
  have eU : (Sn.c "mU").eval tr 3 r pub = 0 := s0
  have eD : (Sn.c "mD").eval tr 3 r pub = 1 := s1
  have eGdn : (Sn.c "gdn").eval tr 3 r pub = 1 := s1
  have eGA : (Sn.c "gA").eval tr 3 r pub = 0 := s0
  have a0 : (Sn.c "oLF").eval tr 3 r pub = 0 := s0
  have a0' : (Sn.c "oEF").eval tr 3 r pub = 0 := s0
  have a1 : (Sn.c "oLR").eval tr 3 r pub = 0 := s0
  have a2 : (Sn.c "oEU").eval tr 3 r pub = 0 := s0
  have a3 : (Sn.c "oED").eval tr 3 r pub = 1 := s1
  have a4 : (Sn.c "oLD").eval tr 3 r pub = 0 := s0
  have a5 : (Sn.c "oEB").eval tr 3 r pub = 0 := s0
  have a6 : (Sn.c "oLX").eval tr 3 r pub = 0 := s0
  have a7 : (Sn.c "oEX").eval tr 3 r pub = 0 := s0
  have a8 : (Sn.c "oLZ").eval tr 3 r pub = 0 := s0
  have a9 : (Sn.c "oEZ").eval tr 3 r pub = 0 := s0
  have a10 : (Sn.c "oES").eval tr 3 r pub = 0 := s0
  have hmode : (payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))).mode = 2 := by
    rw [snpay_mode]; show (Sn.mode.eval tr 3 r pub).toNat = 2
    rw [show Sn.mode.eval tr 3 r pub = 2 by evsn; grind]; rfl
  have hrk : ev tr 3 r pub rkE = RK_LD := by
    rw [ev_eq_of_eval (b := K RK_LD) (by
      simp only [rkE, Sn.gS, Sn.gX, eval_add, eval_mul, eval_sm, eval_K, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]
      grind)]
    simp [K, RK_LD]
  have hrkc : ev tr 3 r pub (Sn.c "rkc") = RK_LD := by
    rw [FieldVer.eq_of_gate (FieldRows2.sn_hold hc sn_mem_rkD) h1, ev_K3]; rfl
  have hg2 : ev tr 3 r pub (Sn.c "g2") = 1 := by
    rw [hg2', h1, ev_of_eval a6, ev_of_eval a7]
  have hK := sn_key_prefix hc hcont (ev_of_eval eGA) hd hnib
  have hK2 := sn_key2_prefix hc hcont hg2 hd hnib2
  have hkl0 : ev tr 3 r pub (Sn.c "d" + Sn.c "klen") = ev tr 3 r pub (Sn.c "d") + ev tr 3 r pub (Sn.c "klen") := by
    rw [ev_hadd, Nat.mod_eq_of_lt (by have := (FieldRows2.sn_flags hc hcont).1; omega)]
  have hkl : ev tr 3 r pub (Sn.c "d" + Sn.c "klen") = ev tr 3 r pub (Sn.c "d") + (snKey tr pub r).length := by
    rw [snKey_length, hkl0]
  rw [← snKey_length] at hK hK2
  rw [snOld_ext (by omega)] at hold
  have eal : ev tr 3 r pub (Sn.c "oLF" * Sn.vlenOf (fun t => Sn.c "x" t) + (Sn.c "oEF" + Sn.c "oED") * Sn.c "alen") =
      ev tr 3 r pub ((Sn.c "oEF" + Sn.c "oED") * Sn.c "alen") := by
    apply ev_eq_of_eval; evsn; grind
  have eah : bytesOf (((pack2 fun b => Sn.c "x" (4 + b)).zip ((List.range 16).map fun i => Sn.c "avh" i)).map
        (fun (p, q) => Sn.c "oLF" * p + (Sn.c "oEF" + Sn.c "oED") * q) |>.map (E tr 3 r pub)) =
      bytesOf (((List.range 16).map fun i => (Sn.c "oEF" + Sn.c "oED") * Sn.c "avh" i).map (E tr 3 r pub)) := by
    rw [map_zip_right (Sn.c "oLF") (Sn.c "oEF" + Sn.c "oED") (fun p => p) _ a0 (by evsn; grind) _
      (by simp [pack2]), map_gate (Sn.c "oEF" + Sn.c "oED") (fun i => Sn.c "avh" i) (by evsn; grind),
      List.map_map]
    rfl
  unfold LocalOK
  simp only [snRow]
  rw [if_pos (show snW.gdn.eval tr 3 r pub = 1 from eGdn)]
  dsimp only
  rw [sn_din, sn_dout, sn_uin, sn_uout]
  simp only [Sem, hmode]
  rw [snpay_kid, hkl]
  intro hch
  refine step_extLeaf (hc := hch) hold hK hrkc hrk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rfl
  · dsimp only; exact ev_gm h1
  · dsimp only; exact eal
  · dsimp only; exact eah
  · dsimp only; rw [ev_gm h1, ev_gm h1, hkl]; exact hK2
  · show le4 _ = le4 _
    rw [map_gate' (Sn.c "mU" + Sn.c "mD") Sn.M (by evsn; grind)]
  · dsimp only
    refine leaf_wf _ _ _ (fun y hy => (hkey _).1 y (List.mem_of_mem_drop hy))
      (by rw [List.length_drop]; have := (hkey (ev tr 3 r pub (Sn.c "oED" * Sn.c "kid2"))).2; omega)
      (ev_lt _) ?_
    rw [bytesOf_length]; simp [pack2]

end

end StateM5a.RowSnE
