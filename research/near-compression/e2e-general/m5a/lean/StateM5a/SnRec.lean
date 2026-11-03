import StateM5a.SnHashed

/-!
# StateM5a.SnRec — a hashing `SN` head's record is `Hashed` to its digest (`cont = 0`)

* `gRecS x xf mb`: the leaf / extension record a row's columns spell (`RowSnMsg.snOld` and
  `RowSnN.snNew` are instances, `snOld_eq` / `snNew_eq`);
* **`grecS_hashed`**: when every `SnSer.snSerF` entry is a byte (and the key nibbles are `< 16`,
  a leaf's top length byte is `0`, an extension's child is a digest), the record is all-digest,
  well formed, `Shallow`, and `R.toP.hashOf = sha256 snSerF`;
* **`sn_old_node`** / **`sn_new_node`**: an `SN` head (`cont = 0`) hashing its old node (`gsha`)
  / its final new node (`gfin`) has byte-ranged columns (`SnBytes`) and its record `Hashed` to the
  digest it receives — from `Holds` alone (the SHA-256 table contract, no cryptographic assumption).
-/

namespace StateM5a.SnRec

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KcChain StateM5a.KeyDigest StateM5a.BrDigest StateM5a.BrSer StateM5a.SnSer
open StateM5a.KeyDecode StateM5a.SnDigest StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnN StateM5a.SnHashed

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable (tr : Trace Fp) (pub : List Fp) (r : Nat)

/-- The memory of a row's node from its byte columns `mb` (4 limbs of 16 bits). -/
def memS (mb : Nat → Expr) : Nat := le4 (((List.range 4).map fun k => limb16 mb k).map (nE tr pub r))

/-- **The record** an `SN` row's columns spell: a leaf `snKey ↦ (vlen x, x₄..₃₅)` or an
extension `snKey → (xf, x₀..₃₁)`, with memory `mb`. -/
def gRecS (x : Nat → Expr) (xf : Expr) (mb : Nat → Expr) : Rec :=
  if ev tr 3 r pub (Sn.c "isL") = 1 then
    .leaf (snKey tr pub r) (.ref (ev tr 3 r pub (Sn.vlenOf x)) (bytesOf ((pack2 fun b => x (4 + b)).map (nE tr pub r))))
      (memS tr pub r mb)
  else .ext (snKey tr pub r) (refOf (nE tr pub r xf) ((pack2 x).map (nE tr pub r))) (memS tr pub r mb)

/-- The byte facts of a row's node (every `snSerF` entry). -/
def SnBytes (x mb : Nat → Expr) : Prop := ∀ v ∈ snSerF tr pub r x mb, v.toNat < 256

end

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem snOld_eq : snOld tr pub r = gRecS tr pub r (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b) := rfl
theorem snNew_eq : snNew tr pub r = gRecS tr pub r (fun t => Sn.c "nx" t) (Sn.c "nxf") (fun b => Sn.c "nmem" b) := rfl

/-! ## Bytes at positions -/

variable {x mb : Nat → Expr}

theorem SnBytes.atHp (h : SnBytes tr pub r x mb) {m : Nat} (hm : m < ev tr 3 r pub (Sn.c "hplen")) :
    ev tr 3 r pub (Sn.c "hp" m) < 256 := h _ (List.mem_of_getElem? (snSerF_hp hm))
theorem SnBytes.atX (h : SnBytes tr pub r x mb) {t : Nat} (ht : t < payLen tr pub r) :
    ev tr 3 r pub (x t) < 256 := h _ (List.mem_of_getElem? (snSerF_x ht))
theorem SnBytes.atMb (h : SnBytes tr pub r x mb) {b : Nat} (hb : b < 8) :
    ev tr 3 r pub (mb b) < 256 := h _ (List.mem_of_getElem? (snSerF_mb hb))

theorem ev3_limb16 (v : Nat → Expr) (k : Nat) (ha : ev tr 3 r pub (v (2 * k)) < 256)
    (hb : ev tr 3 r pub (v (2 * k + 1)) < 256) :
    ev tr 3 r pub (limb16 v k) = ev tr 3 r pub (v (2 * k)) + 256 * ev tr 3 r pub (v (2 * k + 1)) := by
  unfold limb16
  rw [ev_hadd, ev_hmul, ev3_K]
  omega

theorem memS_val (hb : ∀ b, b < 8 → ev tr 3 r pub (mb b) < 256) :
    memS tr pub r mb = ev tr 3 r pub (mb 0) + 256 * ev tr 3 r pub (mb 1) + 65536 * ev tr 3 r pub (mb 2) +
      16777216 * ev tr 3 r pub (mb 3) + 4294967296 * ev tr 3 r pub (mb 4) +
      1099511627776 * ev tr 3 r pub (mb 5) + 281474976710656 * ev tr 3 r pub (mb 6) +
      72057594037927936 * ev tr 3 r pub (mb 7) := by
  show ev tr 3 r pub (limb16 mb 0) + 65536 * ev tr 3 r pub (limb16 mb 1) + 4294967296 * ev tr 3 r pub (limb16 mb 2) +
    281474976710656 * ev tr 3 r pub (limb16 mb 3) = _
  rw [ev3_limb16 mb 0 (hb _ (by omega)) (hb _ (by omega)), ev3_limb16 mb 1 (hb _ (by omega)) (hb _ (by omega)),
    ev3_limb16 mb 2 (hb _ (by omega)) (hb _ (by omega)), ev3_limb16 mb 3 (hb _ (by omega)) (hb _ (by omega))]
  simp only [Nat.reduceMul, Nat.reduceAdd]
  omega

theorem memS_u64 (hb : ∀ b, b < 8 → ev tr 3 r pub (mb b) < 256) :
    u64 (memS tr pub r mb) = (List.range 8).map fun b => UInt8.ofNat (ev tr 3 r pub (mb b)) := by
  rw [memS_val hb, u64, leN8 (fun b => ev tr 3 r pub (mb b)) hb]

theorem memS_lt (hb : ∀ b, b < 8 → ev tr 3 r pub (mb b) < 256) : memS tr pub r mb < 18446744073709551616 := by
  rw [memS_val hb]
  have := hb 0 (by omega); have := hb 1 (by omega); have := hb 2 (by omega); have := hb 3 (by omega)
  have := hb 4 (by omega); have := hb 5 (by omega); have := hb 6 (by omega); have := hb 7 (by omega)
  omega

theorem map_toNat_eq {l : Bytes} {L : List Nat} (h : l.map UInt8.toNat = L) : l = L.map UInt8.ofNat := by
  subst h
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨(UInt8.ofNat_toNat ..).symm, ih⟩

theorem u32_small {n : Nat} (h : n < 256) : u32 n = [UInt8.ofNat n, 0, 0, 0] := by
  simp only [u32, leN, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, Nat.zero_mod, Nat.zero_div]
  rfl

theorem range_split (f : Nat → UInt8) (a b : Nat) :
    (List.range (a + b)).map f = (List.range a).map f ++ (List.range b).map fun j => f (a + j) := by
  rw [List.range_add, List.map_append, List.map_map]
  rfl

/-! ## The record is hashed -/

set_option maxHeartbeats 8000000 in
/-- **A record whose serialization bytes are `snSerF` is `Hashed` to their SHA-256.** -/
theorem grecS_hashed (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hA : ev tr 3 r pub (Sn.c "act") = 1) (hcont : ev tr 3 r pub (Sn.c "cont") = 0)
    (hk : ∀ j, j < 64 → ev tr 3 r pub (Sn.c "k" j) < 16) {xf : Expr}
    (hB : SnBytes tr pub r x mb) (hx3 : ev tr 3 r pub (Sn.c "isL") = 1 → ev tr 3 r pub (x 3) = 0)
    (hxf : ev tr 3 r pub (Sn.c "isL") ≠ 1 → ev tr 3 r pub xf = 0) :
    Hashed (gRecS tr pub r x xf mb) (sha256 ((snSerF tr pub r x mb).map fun v => UInt8.ofNat v.toNat)) := by
  have hops := sn_ops hc
  have hL := FieldRows2.sn_bool hc "isL" (by simp)
  have hpl := FieldRows2.sn_hplen hc hA hcont
  have hkl := (FieldRows2.sn_flags hc hcont).1
  have hhp : (hexPrefix (snKey tr pub r) (decide (ev tr 3 r pub (Sn.c "isL") = 1))).map UInt8.toNat =
      (List.range (ev tr 3 r pub (Sn.c "hplen"))).map fun m => ev tr 3 r pub (Sn.c "hp" m) :=
    FieldRows2.sn_hexPrefix hc hA hcont hk
  have hlen : (hexPrefix (snKey tr pub r) (decide (ev tr 3 r pub (Sn.c "isL") = 1))).length =
      ev tr 3 r pub (Sn.c "hplen") := by
    have := congrArg List.length hhp; simpa using this
  have hhpE := map_toNat_eq hhp
  have hmb := fun b (h : b < 8) => hB.atMb (b := b) h
  have hnib : nibblesOk (snKey tr pub r) = true := by
    simp only [nibblesOk, snKey, FieldRows2.keyOf, List.all_map, List.all_eq_true, List.mem_range,
      Function.comp, decide_eq_true_eq]
    intro j hj; exact hk j (by omega)
  -- the common head: tag, `u32 |hp|`, `hp`
  have hisE : ev tr 3 r pub (Sn.c "isE") = 1 - ev tr 3 r pub (Sn.c "isL") := by
    obtain ⟨hfl, h1, h2, h3, h4, h5, h6, -, -⟩ := hops
    have := hfl "isE" (by simp [snNames]); omega
  have htag : ev tr 3 r pub (sm 3 (Sn.c "isE")) = 3 * (1 - ev tr 3 r pub (Sn.c "isL")) := by
    rw [ev3_sm, hisE]; omega
  have hhead : (snSerF tr pub r x mb).map (fun v => UInt8.ofNat v.toNat) =
      [UInt8.ofNat (3 * (1 - ev tr 3 r pub (Sn.c "isL")))] ++
        u32 (hexPrefix (snKey tr pub r) (decide (ev tr 3 r pub (Sn.c "isL") = 1))).length ++
        hexPrefix (snKey tr pub r) (decide (ev tr 3 r pub (Sn.c "isL") = 1)) ++
        (List.range (payLen tr pub r)).map (fun t => UInt8.ofNat (ev tr 3 r pub (x t))) ++
        u64 (memS tr pub r mb) := by
    rw [hlen, u32_small (by omega), hhpE, memS_u64 hmb]
    simp only [snSerF, List.map_append, List.map_cons, List.map_nil, List.map_map, List.cons_append,
      List.nil_append, List.append_assoc]
    show UInt8.ofNat (ev tr 3 r pub (sm 3 (Sn.c "isE"))) :: _ = _
    rw [htag]
    rfl
  have hpay : ∀ t, t < payLen tr pub r → ev tr 3 r pub (x t) < 256 := fun t ht => hB.atX ht
  by_cases h1 : ev tr 3 r pub (Sn.c "isL") = 1
  · -- a leaf
    have hpl36 : payLen tr pub r = 4 + 32 := by unfold payLen; omega
    have x3 := hx3 h1
    have hx : ∀ t, t < 36 → ev tr 3 r pub (x t) < 256 := fun t ht => hpay t (by omega)
    have hvl : ev tr 3 r pub (Sn.vlenOf x) = ev tr 3 r pub (x 0) + 256 * ev tr 3 r pub (x 1) +
        65536 * (ev tr 3 r pub (x 2) + 256 * ev tr 3 r pub (x 3)) := by
      unfold Sn.vlenOf
      rw [ev_hadd, ev_hadd, ev3_sm, ev3_sm, x3]
      have := hx 0 (by omega); have := hx 1 (by omega); have := hx 2 (by omega)
      omega
    have hvlt : ev tr 3 r pub (Sn.vlenOf x) < 4294967296 := by
      rw [hvl, x3]; have := hx 0 (by omega); have := hx 1 (by omega); have := hx 2 (by omega); omega
    have hh : bytesOf ((pack2 fun b => x (4 + b)).map (nE tr pub r)) =
        (List.range 32).map fun j => UInt8.ofNat (ev tr 3 r pub (x (4 + j))) :=
      bytesOf_pack3 (fun b => x (4 + b)) (fun j hj => hx _ (by omega))
    have hhl : (bytesOf ((pack2 fun b => x (4 + b)).map (nE tr pub r))).length = 32 := by rw [hh]; simp
    simp only [gRecS, h1, ↓reduceIte]
    refine ⟨trivial, ?_, ⟨_, _, rfl⟩, ?_⟩
    · simp only [Rec.toP, PTrie.wf, hnib, slotOk, hvlt, hhl, memS_lt hmb, Bool.true_and, decide_true,
        beq_self_eq_true, Bool.and_true]
      simp only [h1, decide_true] at hlen
      rw [hlen]; (try simp) <;> omega
    · simp only [Rec.toP, PTrie.hashOf]
      congr 1
      rw [hhead, hpl36, range_split, Slot.valueRef, hvl]
      simp only [u32]
      rw [leN4 (fun b => ev tr 3 r pub (x b))
        (fun b hb => hx b (by omega)), hh]
      simp only [h1, decide_true, Nat.sub_self, Nat.mul_zero, List.append_assoc]
      rfl
  · -- an extension
    have h0 : ev tr 3 r pub (Sn.c "isL") = 0 := by omega
    have hpl32 : payLen tr pub r = 32 := by unfold payLen; omega
    have hx : ∀ t, t < 32 → ev tr 3 r pub (x t) < 256 := fun t ht => hpay t (by omega)
    have hch : refOf (nE tr pub r xf) ((pack2 x).map (nE tr pub r)) =
        .dig (bytesOf ((pack2 x).map (nE tr pub r))) :=
      refOf_dig' _ _ (by simp [pack2]) (hxf h1)
    have hh : bytesOf ((pack2 x).map (nE tr pub r)) = (List.range 32).map fun j => UInt8.ofNat (ev tr 3 r pub (x j)) :=
      bytesOf_pack3 x hx
    have hhl : (bytesOf ((pack2 x).map (nE tr pub r))).length = 32 := by rw [hh]; simp
    simp only [gRecS, h1, ↓reduceIte, hch]
    refine ⟨trivial, ?_, ⟨_, rfl⟩, ?_⟩
    · simp only [Rec.toP, Ref.toP, PTrie.wf, hnib, hhl, memS_lt hmb, Bool.true_and, decide_true,
        beq_self_eq_true, Bool.and_true]
      simp only [h1, decide_false] at hlen
      rw [hlen]; (try simp) <;> omega
    · simp only [Rec.toP, Ref.toP, PTrie.hashOf]
      congr 1
      rw [hhead, hpl32, hh]
      simp only [h1, decide_false, h0, Nat.sub_zero, Nat.mul_one, List.append_assoc]
      rfl

end

/-! ## Hashing rows -/

theorem sn_mem_x3 : Sn.c "isL" * Sn.c "x" 3 ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem sn_mem_nx3 : (Sn.c "oLR" + Sn.c "oLM") * Sn.c "nx" 3 ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem sn_mem_gxf : Sn.c "gsha" * Sn.c "xf" ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem sn_mem_gnxf : Sn.gfin * Sn.c "nxf" ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp
theorem sn_mem_gsg : Sn.c "gsha" * (1 - Sn.c "gold") ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
  (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)

include hH in
theorem ev_idS {r : Nat} (hr : r < tr.height 3) :
    ev tr 3 r pub Sn.idO = ID_SN + 2 * r ∧ ev tr 3 r pub Sn.idN = ID_SN + 2 * r + 1 := by
  have hH3 : tr.height 3 ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right (by decide) (hH.logBound 3 (by rw [fullAir_len]; omega)).2
  have hrid := sn_rid hH r hr
  constructor
  · show ev tr 3 r pub (K ID_SN + sm 2 (Sn.c "rid")) = _
    rw [ev_id2 _ _ (by omega) (by decide), hrid]
  · show ev tr 3 r pub (K ID_SN + sm 2 (Sn.c "rid") + 1) = _
    rw [ev_id2' _ _ (by omega) (by decide), hrid]

include hH in
/-- A row with `gsha` or `gnew` is active. -/
theorem sn_act_of {r : Nat} (hr : r < tr.height 3)
    (h : ev tr 3 r pub (Sn.c "gsha") = 1 ∨ ev tr 3 r pub (Sn.c "gnew") = 1) : ev tr 3 r pub (Sn.c "act") = 1 := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  obtain ⟨hfl, h1, h2, h3, h4, -, -, -, h9⟩ := sn_ops hc
  have := hfl "act" (by simp [snNames])
  rcases h with h | h
  · have hg1 := FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_gsg) h
    have hg : ev tr 3 r pub (Sn.c "gold") = 1 := by
      rw [ev_sub] at hg1
      have := ev_lt (tr := tr) (t := 3) (r := r) (pub := pub) (Sn.c "gold")
      rw [ev_one] at hg1; omega
    rcases (by omega : ev tr 3 r pub (Sn.c "act") = 1 ∨ ev tr 3 r pub (Sn.c "act") = 0) with h0 | h0
    · exact h0
    exfalso
    have z1 : ev tr 3 r pub (Sn.c "oLM") = 0 := by omega
    have z2 : ev tr 3 r pub (Sn.c "oEP") = 0 := by omega
    have z3 : ev tr 3 r pub (Sn.c "oEM") = 0 := by omega
    have e := eq_of_sub (FieldRows.hold rfl hc sn_mem_gold)
    rw [ev_sub, ev_sub, ev_sub, h0, z1, z2, z3, hg] at e
    simp at e
  · omega

include hH hxB hxD hxK hN hxr in
/-- **A row hashing its old node** (`gsha`, `cont = 0`): its columns are bytes and its old record is
`Hashed` to its digest `ho`. -/
theorem sn_old_node {r : Nat} (hr : r < tr.height 3) (hs : ev tr 3 r pub (Sn.c "gsha") = 1)
    (hcont : ev tr 3 r pub (Sn.c "cont") = 0) :
    SnBytes tr pub r (fun t => Sn.c "x" t) (fun b => Sn.c "mem" b) ∧
      Hashed (snOld tr pub r) (bytesOf ((pack2 fun b => Sn.c "ho" b).map (nE tr pub r))) := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hA := sn_act_of hH hr (Or.inl hs)
  obtain ⟨hB, hd⟩ := sn_node hH hxB hxD hxK hr (par := 0) (Nat.zero_le _) (ev_idS hH hr).1 rfl sn_sd_old
    (fun i hi hb hs hh => mem_of_filter sn_sb_old hi (pred_true hb hs hh)) hs hA hcont
  refine ⟨hB, ?_⟩
  rw [hd, snOld_eq]
  exact grecS_hashed hc hA hcont (sn_k16 hH hN hxr hr) hB
    (fun h1 => FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_x3) h1)
    (fun _ => FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_gxf) hs)

include hH hxB hxD hxK hN hxr in
/-- **A row hashing its new node** (`gnew`, `nref = 0`, `cont = 0`). -/
theorem sn_new_node {r : Nat} (hr : r < tr.height 3) (hn : ev tr 3 r pub (Sn.c "gnew") = 1)
    (hn0 : ev tr 3 r pub (Sn.c "nref") = 0) (hcont : ev tr 3 r pub (Sn.c "cont") = 0) :
    SnBytes tr pub r (fun t => Sn.c "nx" t) (fun b => Sn.c "nmem" b) ∧
      Hashed (snNew tr pub r) (bytesOf ((pack2 fun b => Sn.c "hn" b).map (nE tr pub r))) := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hA := sn_act_of hH hr (Or.inr hn)
  have hf : ev tr 3 r pub Sn.gfin = 1 := by
    show ev tr 3 r pub (Sn.c "gnew" - Sn.c "nref") = 1
    rw [ev_sub, hn, hn0]
  obtain ⟨hB, hd⟩ := sn_node hH hxB hxD hxK hr (par := 1) (Nat.le_refl _) (ev_idS hH hr).2 rfl sn_sd_new
    (fun i hi hb hs hh => mem_of_filter sn_sb_new hi (pred_true hb hs hh)) hf hA hcont
  refine ⟨hB, ?_⟩
  rw [hd, snNew_eq]
  obtain ⟨hfl, h1, h2, h3, h4, h5, h6, -, h9⟩ := sn_ops hc
  have := hfl "oLR" (by simp [snNames]); have := hfl "oLM" (by simp [snNames])
  have := hfl "act" (by simp [snNames])
  exact grecS_hashed hc hA hcont (sn_k16 hH hN hxr hr) hB
    (fun hl => FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_nx3) (by rw [ev_hadd]; omega))
    (fun _ => FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_gnxf) hf)

end

end StateM5a.SnRec
