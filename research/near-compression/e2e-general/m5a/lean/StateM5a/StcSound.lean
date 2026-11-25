import StateM5a.StcRow
import StateM5a.StHalfC
import StateM5a.TmplSeg

/-!
# StateM5a.StcSound — B-T3: `StcOK` from `Holds` (the `STC` table opens and closes `stRoot`)

For an active `STC` row (`Stc.table D` at any index of any AIR whose `SRNG` sends are bytes, with the
SHA-512 chip contract on `IF384`):

* `sha_in` / `sha_out`: SHA-384 of the row's input / output message (139 bytes) is its digest bytes
  `ri` / `ro` (two compressions each, `two_comps`; FIPS padding, `StcBytes.sha384_stc`);
* `comI` (the opened commitment: tag `b₀`, `ws` = `b₁…₄₈`, `wsLen` = the public count, trie, index,
  rest) serializes to the input message (`ser_comI`), and its `close` with `R_out` and the engine's
  output meta to the output message (`ser_close`);
* **`stc_row_ok`**: `StcOK r_in r_out R_in R_out wsLen mi mo` with `r_in`, `mo` read from the row's
  `STMQ` message and `r_out`, `mi` from its `STMA` message (`decR`, `decM`: 14 limbs of 3 bytes), and
  **`wsLen ≤ 2^D`** — the B-T2 named premise of `WsBridge.ws_moves_seg`, now from the circuit;
* **`stc_holds`**: the same from `Holds` (any AIR, `STC` at index `t`), and **`stc_seg`** for the
  STATE template with the opening, `segAir D (stcTables D ++ extra)` (`m5tSegC` + lane F's rows).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace StateM5a.StcSound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.FieldRows StateM5a.WsDecode StateM5a.WsDecode3
open StateM5a.Sha512If StateM5a.StcBytes StateM5a.StcRow StateM5a.WsBridge StateM5a.StHalfC StateM5a.Bus
open StateM5a.StateView (StCommit wbytes)
open ArenaCore.Bytes NearSpecV3

local notation "P" => 2013265921

/-! ## Two chained compressions -/

theorem take6_map {x : List Nat} (hl : x.length = 8) (hw : W64 x) : (digest6 x).1 = x.take 6 :=
  digest6_take x hl hw

/-- **Two compressions chained through 8 limb triples.** -/
theorem two_comps {compress : List Nat → List Nat → List Nat} (hc : CompressOK compress)
    {chip : List IfMsg} (hC : Sha512IfContract compress chip) {cid1 cid2 : Nat} {B1 B2 : List Nat}
    {Hl Dl Xl : List (List Nat)} (h16 : B1.length = 16) (h16' : B2.length = 16) (hH : Hl.length = 8)
    (hD : Dl.length = 6) (hX : Xl.length = 2)
    (h1 : ∀ x ∈ compRecv cid1 (IV384.map wlimbs ++ B1.map wlimbs ++ Hl), x ∈ chip)
    (h2 : ∀ x ∈ compRecv cid2 (Hl ++ B2.map wlimbs ++ (Dl ++ Xl)), x ∈ chip) :
    Dl = enc (digest6 (compress (compress IV384 B1) B2)) := by
  obtain ⟨h, blk, hl8, hb16, -, -, e1⟩ := comp_sound hc hC (by simp [IV384, h16, hH]) h1
  rw [List.map_append, List.map_append] at e1
  obtain ⟨e1a, e1b⟩ := List.append_inj e1 (by simp [hl8, hb16, IV384, h16])
  obtain ⟨e1c, e1d⟩ := List.append_inj e1a (by simp [hl8, IV384])
  have hh : h = IV384 := map_wlimbs_inj e1c.symm
  have hb : blk = B1 := map_wlimbs_inj e1d.symm
  rw [hh, hb] at e1b
  obtain ⟨h', blk', hl8', hb16', -, -, e2⟩ := comp_sound hc hC (by simp [h16', hH, hD, hX]) h2
  rw [List.map_append, List.map_append] at e2
  obtain ⟨e2a, e2b⟩ := List.append_inj e2 (by simp [hl8', hb16', hH, h16'])
  obtain ⟨e2c, e2d⟩ := List.append_inj e2a (by simp [hl8', hH])
  have hh' : h' = compress IV384 B1 := map_wlimbs_inj (e2c.symm.trans e1b)
  have hb' : blk' = B2 := map_wlimbs_inj e2d.symm
  rw [hh', hb'] at e2b
  obtain ⟨o, ox, hs, ho, -⟩ := List.map_eq_append_iff.1 e2b.symm
  have hlo : o.length = 6 := by rw [← hD, ← ho, List.length_map]
  have hw := (hc (compress IV384 B1) B2).2
  have hw' : W64 o := by rw [hs] at hw; exact (w64_append.1 hw).1
  rw [enc, digest6_eq hs hlo hw', ho]


/-! ## The `STMQ` / `STMA` messages -/

/-- A 42-B digest from its 14 limbs (the first 14 entries of a message). -/
def decR (l : List Nat) : ArenaCore.Bytes := limbBytes (l.take 14)
/-- The tag (entry 14) and the `rest` digest (entries 15–28) of a message. -/
def decM (l : List Nat) : StMeta := ⟨l.getD 14 0, limbBytes ((l.drop 15).take 14)⟩

theorem msg29 {α : Type} [Inhabited α] (L1 L2 : List α) (x d : α) (h1 : L1.length = 14) :
    (L1 ++ [x] ++ L2).take 14 = L1 ∧ (L1 ++ [x] ++ L2).getD 14 d = x ∧ (L1 ++ [x] ++ L2).drop 15 = L2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.append_assoc, List.take_left' h1]
  · rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by omega), h1]; simp
  · rw [List.append_assoc, show (15 : Nat) = L1.length + 1 by omega, ← List.drop_drop, List.drop_left]; simp

/-! ## The row -/

section Row
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp} {D : Nat}
  (hc : ∀ e ∈ (Stc.table D).constraints, ev tr t r pub e = 0)
  (hA : ev tr t r pub (Stc.c "act") = 1)
  (hB : ∀ x ∈ Stc.byteCols, ev tr t r pub x < 256)
  (hHi : ∀ x ∈ Stc.hiCols, ev tr t r pub x < 256)
  (hLo : ∀ p ∈ Stc.loCols, ev tr t r pub p.1 < 256 ∧ ev tr t r pub (K (2 ^ (8 - p.2)) * p.1) < 256)
  {chip : List IfMsg} (hC : Sha512IfContract cW chip)

/-- The row's input / output messages (139 bytes). -/
def msgI (tr : Trace Fp) (t r : Nat) (pub : List Fp) : ArenaCore.Bytes :=
  (List.range 139).map fun p => UInt8.ofNat (FI tr t r pub p)
def msgO (tr : Trace Fp) (t r : Nat) (pub : List Fp) : ArenaCore.Bytes :=
  (List.range 139).map fun p => UInt8.ofNat (FO tr t r pub p)

theorem wordsF_len (f : Nat → Nat) (w0 n : Nat) : (wordsF f w0 n).length = n := by simp [wordsF]

theorem wordsF_w64 (f : Nat → Nat) (w0 n : Nat) : W64 (wordsF f w0 n) := by
  intro w hw; obtain ⟨k, -, rfl⟩ := List.mem_map.1 hw; exact wordOf_lt _ _

theorem toB_dig (f : Nat → Nat) (d : Dig) (h : d.1 = wordsF f 0 6) :
    toB d = (List.range 48).map fun p => UInt8.ofNat (f p) := by
  have : d = ⟨wordsF f 0 6, wordsF_len f 0 6, wordsF_w64 f 0 6⟩ := Subtype.ext h
  rw [this, toB_words]

include hc hA hB hHi hLo hC in
/-- **SHA-384 of the input message is the row's digest bytes `ri`.** -/
theorem sha_in
    (h1 : ∀ x ∈ compRecv (ev tr t r pub (Stc.c "ci1"))
      ((ivW ++ Stc.blockW Stc.mI "si" 0 ++ wordsOf (fun u => Stc.c "hi" u) 8).map (dec3 tr t r pub)), x ∈ chip)
    (h2 : ∀ x ∈ compRecv (ev tr t r pub (Stc.c "ci2"))
      ((wordsOf (fun u => Stc.c "hi" u) 8 ++ Stc.blockW Stc.mI "si" 1 ++ digW (fun u => Stc.c "di" u) ++
        wordsOf (fun u => Stc.c "xi" u) 2).map (dec3 tr t r pub)), x ∈ chip) :
    NearSpecV3.E2E.Bnd.sha384 (msgI tr t r pub) = (List.range 48).map fun j => UInt8.ofNat (RI tr t r pub j) := by
  have b0 := blockI hc hA hB hHi hLo (k := 0) (by decide)
  have b1 := blockI hc hA hB hHi hLo (k := 1) (by decide)
  simp only [Nat.mul_zero, Nat.mul_one] at b0 b1
  rw [List.map_append, List.map_append, ivW_dec, b0] at h1
  rw [List.map_append, List.map_append, List.map_append, b1, digI hc hA hB hHi hLo, List.append_assoc] at h2
  have e := two_comps cW_ok hC (wordsF_len _ _ _) (wordsF_len _ _ _) (by simp [wordsOf]) (by simp [wordsF])
    (by simp [wordsOf]) h1 h2
  have e' : digest6 (cW (cW IV384 (wordsF (FI tr t r pub) 0 16)) (wordsF (FI tr t r pub) 16 16)) =
      ⟨wordsF (RI tr t r pub) 0 6, wordsF_len _ _ _, wordsF_w64 _ _ _⟩ := enc_inj e.symm
  unfold msgI
  have hp : ∀ p, 139 ≤ p → p < 256 → FI tr t r pub p = Stc.padByte p := fun p hp _ => by
    show ev tr t r pub (Stc.mI p) = _
    rw [mI_pad hp, ev_K _ (by have := padByte_lt p; omega)]
  rw [sha384_stc (FI tr t r pub) (fun p => bI hB p) hp, e', toB_words]

include hc hA hB hHi hLo hC in
theorem sha_out
    (h1 : ∀ x ∈ compRecv (ev tr t r pub (Stc.c "co1"))
      ((ivW ++ Stc.blockW Stc.mO "so" 0 ++ wordsOf (fun u => Stc.c "ho" u) 8).map (dec3 tr t r pub)), x ∈ chip)
    (h2 : ∀ x ∈ compRecv (ev tr t r pub (Stc.c "co2"))
      ((wordsOf (fun u => Stc.c "ho" u) 8 ++ Stc.blockW Stc.mO "so" 1 ++ digW (fun u => Stc.c "do" u) ++
        wordsOf (fun u => Stc.c "xo" u) 2).map (dec3 tr t r pub)), x ∈ chip) :
    NearSpecV3.E2E.Bnd.sha384 (msgO tr t r pub) = (List.range 48).map fun j => UInt8.ofNat (RO tr t r pub j) := by
  have b0 := blockO hc hA hB hHi hLo (k := 0) (by decide)
  have b1 := blockO hc hA hB hHi hLo (k := 1) (by decide)
  simp only [Nat.mul_zero, Nat.mul_one] at b0 b1
  rw [List.map_append, List.map_append, ivW_dec, b0] at h1
  rw [List.map_append, List.map_append, List.map_append, b1, digO hc hA hB hHi hLo, List.append_assoc] at h2
  have e := two_comps cW_ok hC (wordsF_len _ _ _) (wordsF_len _ _ _) (by simp [wordsOf]) (by simp [wordsF])
    (by simp [wordsOf]) h1 h2
  have e' : digest6 (cW (cW IV384 (wordsF (FO tr t r pub) 0 16)) (wordsF (FO tr t r pub) 16 16)) =
      ⟨wordsF (RO tr t r pub) 0 6, wordsF_len _ _ _, wordsF_w64 _ _ _⟩ := enc_inj e.symm
  unfold msgO
  have hp : ∀ p, 139 ≤ p → p < 256 → FO tr t r pub p = Stc.padByte p := fun p hp _ => by
    show ev tr t r pub (Stc.mO p) = _
    rw [mO_pad hp, ev_K _ (by have := padByte_lt p; omega)]
  rw [sha384_stc (FO tr t r pub) (fun p => bO hB p) hp, e', toB_words]

/-! ## The opened commitment -/

theorem range_cut {α : Type} (g : Nat → α) (a b : Nat) :
    (List.range (a + b)).map g = (List.range a).map g ++ (List.range b).map (fun i => g (a + i)) := by
  rw [List.range_add, List.map_append, List.map_map]; rfl

/-- The 139 bytes of a byte function, cut at the commitment's fields. -/
theorem range139 {α : Type} (g : Nat → α) :
    (List.range 139).map g = [g 0] ++ (List.range 48).map (fun i => g (1 + i)) ++
      (List.range 8).map (fun i => g (49 + i)) ++ (List.range 32).map (fun i => g (57 + i)) ++
      (List.range 8).map (fun i => g (89 + i)) ++ (List.range 42).map (fun i => g (97 + i)) := by
  rw [show (139 : Nat) = 97 + 42 from rfl, range_cut, show (97 : Nat) = 89 + 8 from rfl, range_cut,
    show (89 : Nat) = 57 + 32 from rfl, range_cut, show (57 : Nat) = 49 + 8 from rfl, range_cut,
    show (49 : Nat) = 1 + 48 from rfl, range_cut]
  rfl

/-- **The opened commitment** of an `STC` row. -/
def comI (tr : Trace Fp) (t r : Nat) (pub : List Fp) : StCommit :=
  { tag := FI tr t r pub 0
    ws := (List.range 48).map fun j => UInt8.ofNat (FI tr t r pub (1 + j))
    wsLen := WsLen.wsLen pub
    trie := (List.range 32).map fun j => UInt8.ofNat (FI tr t r pub (57 + j))
    idx := NearSpec.leNat ((List.range 8).map fun k => UInt8.ofNat (FI tr t r pub (89 + k)))
    rest := (List.range 42).map fun j => UInt8.ofNat (FI tr t r pub (97 + j)) }

include hc hA hB in
theorem u64_len (hD : D ≤ 20) : NearSpec.u64 (WsLen.wsLen pub) =
    (List.range 8).map fun i => UInt8.ofNat (FI tr t r pub (49 + i)) := by
  obtain ⟨hW, h0, -⟩ := lenI hc hA hB hD
  rw [hW, u64_bytes (FI tr t r pub 49) (FI tr t r pub 50) (FI tr t r pub 51) (bI hB 49) (bI hB 50) (bI hB 51),
    range8_map]
  simp only [List.map_cons, List.map_nil, Nat.add_zero, show 49 + 1 = 50 from rfl, show 49 + 2 = 51 from rfl,
    show 49 + 3 = 52 + 0 from rfl, show 49 + 4 = 52 + 1 from rfl, show 49 + 5 = 52 + 2 from rfl,
    show 49 + 6 = 52 + 3 from rfl, show 49 + 7 = 52 + 4 from rfl, h0 0 (by decide), h0 1 (by decide),
    h0 2 (by decide), h0 3 (by decide), h0 4 (by decide)]

theorem u64_idx (l : ArenaCore.Bytes) (hl : l.length = 8) : NearSpec.u64 (NearSpec.leNat l) = l := by
  have := leN_leNat l; rw [hl] at this; exact this

include hc hA hB in
theorem ser_comI (hD : D ≤ 20) : (comI tr t r pub).ser = msgI tr t r pub := by
  unfold msgI
  rw [range139, StCommit.ser, comI]
  simp only
  rw [u64_len hc hA hB hD, u64_idx _ (by simp)]

include hc hA hB in
theorem comI_wf (hD : D ≤ 20) : (comI tr t r pub).WF := by
  obtain ⟨hW, -, -⟩ := lenI hc hA hB hD
  refine ⟨bI hB 0, by simp [comI], ?_, by simp [comI], ?_, by simp [comI, NearSpecV3.E2E.Bnd.digestLen]⟩
  · show WsLen.wsLen pub < 2 ^ 64
    have := bI hB 49; have := bI hB 50; have := bI hB 51
    unfold FI at hW; omega
  · have := leNat_lt ((List.range 8).map fun k => UInt8.ofNat (FI tr t r pub (89 + k)))
    simpa [comI] using this

theorem FO_mid {p : Nat} (h1 : 49 ≤ p) (h2 : p < 97) : FO tr t r pub p = FI tr t r pub p := by
  unfold FO FI Stc.mO Stc.mI Stc.NB
  rw [if_neg (by omega), if_neg (by omega), if_pos h2, if_pos (by omega)]

include hc hA hB in
/-- **The closed commitment serializes to the output message.** -/
theorem ser_close (hD : D ≤ 20) (R : ArenaCore.Bytes) (m : StMeta)
    (hR : R = (List.range 48).map fun j => UInt8.ofNat (FO tr t r pub (1 + j)))
    (ht : m.tag = FO tr t r pub 0)
    (hr : m.rest = (List.range 42).map fun j => UInt8.ofNat (FO tr t r pub (97 + j))) :
    (close (comI tr t r pub) R m).ser = msgO tr t r pub := by
  unfold msgO
  rw [range139, StCommit.ser, close, comI]
  simp only
  rw [u64_len hc hA hB hD, u64_idx _ (by simp), hR, ht, hr]
  have e1 : ((List.range 8).map fun i => UInt8.ofNat (FI tr t r pub (49 + i))) =
      (List.range 8).map fun i => UInt8.ofNat (FO tr t r pub (49 + i)) := by
    apply List.map_congr_left; intro i hi; have := List.mem_range.1 hi; rw [FO_mid (by omega) (by omega)]
  have e2 : ((List.range 32).map fun i => UInt8.ofNat (FI tr t r pub (57 + i))) =
      (List.range 32).map fun i => UInt8.ofNat (FO tr t r pub (57 + i)) := by
    apply List.map_congr_left; intro i hi; have := List.mem_range.1 hi; rw [FO_mid (by omega) (by omega)]
  have e3 : ((List.range 8).map fun i => UInt8.ofNat (FI tr t r pub (89 + i))) =
      (List.range 8).map fun i => UInt8.ofNat (FO tr t r pub (89 + i)) := by
    apply List.map_congr_left; intro i hi; have := List.mem_range.1 hi; rw [FO_mid (by omega) (by omega)]
  rw [e1, e2, e3]

theorem ev_limb3 (byte : Nat → Expr) (i : Nat) (h0 : ev tr t r pub (byte (3 * i)) < 256)
    (h1 : ev tr t r pub (byte (3 * i + 1)) < 256) (h2 : ev tr t r pub (byte (3 * i + 2)) < 256) :
    ev tr t r pub (Stc.limb3 byte i) =
      65536 * ev tr t r pub (byte (3 * i)) + 256 * ev tr t r pub (byte (3 * i + 1)) + ev tr t r pub (byte (3 * i + 2)) := by
  unfold Stc.limb3
  have hX := ev_kmul_nw (tr := tr) (t := t) (r := r) (pub := pub) 65536 (byte (3 * i)) (by omega) (by decide)
  have hY := ev_kmul_nw (tr := tr) (t := t) (r := r) (pub := pub) 256 (byte (3 * i + 1)) (by omega) (by decide)
  have hXY : ev tr t r pub (K 65536 * byte (3 * i) + K 256 * byte (3 * i + 1)) =
      65536 * ev tr t r pub (byte (3 * i)) + 256 * ev tr t r pub (byte (3 * i + 1)) := by
    rw [ev_add_nw (by rw [hX, hY]; omega), hX, hY]
  rw [ev_add_nw (by rw [hXY]; omega), hXY]

theorem limbs14_dec (byte : Nat → Expr) (hb : ∀ j, j < 42 → ev tr t r pub (byte j) < 256) :
    limbBytes ((Stc.limbs14 byte).map (ev tr t r pub)) = (List.range 42).map fun j => UInt8.ofNat (ev tr t r pub (byte j)) := by
  rw [Stc.limbs14, List.map_map]
  rw [show ((List.range 14).map (ev tr t r pub ∘ Stc.limb3 byte)) = (List.range 14).map fun i =>
      65536 * ev tr t r pub (byte (3 * i)) + 256 * ev tr t r pub (byte (3 * i + 1)) + ev tr t r pub (byte (3 * i + 2)) by
    apply List.map_congr_left; intro i hi; have := List.mem_range.1 hi
    exact ev_limb3 byte i (hb _ (by omega)) (hb _ (by omega)) (hb _ (by omega))]
  exact limbBytes_limbs (fun j => ev tr t r pub (byte j)) hb

/-- The row's `STMQ` / `STMA` message values. -/
def qv (tr : Trace Fp) (t r : Nat) (pub : List Fp) : List Nat := Stc.stmqMsg.map (ev tr t r pub)
def av (tr : Trace Fp) (t r : Nat) (pub : List Fp) : List Nat := Stc.stmaMsg.map (ev tr t r pub)

theorem limbs14_len (byte : Nat → Expr) : ((Stc.limbs14 byte).map (ev tr t r pub)).length = 14 := by
  simp [Stc.limbs14]

include hB in
theorem qv_dec : decR (qv tr t r pub) = (List.range 42).map (fun j => UInt8.ofNat (RI tr t r pub j)) ∧
    (decM (qv tr t r pub)).tag = FO tr t r pub 0 ∧
    (decM (qv tr t r pub)).rest = (List.range 42).map fun j => UInt8.ofNat (FO tr t r pub (97 + j)) := by
  obtain ⟨m1, m2, m3⟩ := msg29 ((Stc.limbs14 fun j => Stc.c "ri" j).map (ev tr t r pub))
    ((Stc.limbs14 fun j => Stc.c "or" j).map (ev tr t r pub)) (ev tr t r pub (Stc.c "ot")) 0 (limbs14_len _)
  have hq : qv tr t r pub = (Stc.limbs14 fun j => Stc.c "ri" j).map (ev tr t r pub) ++ [ev tr t r pub (Stc.c "ot")] ++
      (Stc.limbs14 fun j => Stc.c "or" j).map (ev tr t r pub) := by
    unfold qv Stc.stmqMsg; rw [List.map_append, List.map_append]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [decR, hq, m1, limbs14_dec _ (fun j hj => hB _ (mem_ri (by omega)))]; rfl
  · show (qv tr t r pub).getD 14 0 = _
    rw [hq, m2]; rfl
  · show limbBytes (((qv tr t r pub).drop 15).take 14) = _
    rw [hq, m3, List.take_of_length_le (by rw [limbs14_len]; exact Nat.le_refl _),
      limbs14_dec _ (fun j hj => hB _ (mem_or (by omega)))]
    apply List.map_congr_left; intro j hj; have := List.mem_range.1 hj
    show UInt8.ofNat (ev tr t r pub (Stc.c "or" j)) = UInt8.ofNat (ev tr t r pub (Stc.mO (97 + j)))
    unfold Stc.mO Stc.NB; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    congr 3; omega

include hB in
theorem av_dec : decR (av tr t r pub) = (List.range 42).map (fun j => UInt8.ofNat (RO tr t r pub j)) ∧
    (decM (av tr t r pub)).tag = FI tr t r pub 0 ∧
    (decM (av tr t r pub)).rest = (List.range 42).map fun j => UInt8.ofNat (FI tr t r pub (97 + j)) := by
  obtain ⟨m1, m2, m3⟩ := msg29 ((Stc.limbs14 fun j => Stc.c "ro" j).map (ev tr t r pub))
    ((Stc.limbs14 fun j => Stc.c "b" (97 + j)).map (ev tr t r pub)) (ev tr t r pub (Stc.c "b" 0)) 0 (limbs14_len _)
  have hq : av tr t r pub = (Stc.limbs14 fun j => Stc.c "ro" j).map (ev tr t r pub) ++ [ev tr t r pub (Stc.c "b" 0)] ++
      (Stc.limbs14 fun j => Stc.c "b" (97 + j)).map (ev tr t r pub) := by
    unfold av Stc.stmaMsg; rw [List.map_append, List.map_append]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [decR, hq, m1, limbs14_dec _ (fun j hj => hB _ (mem_ro (by omega)))]; rfl
  · show (av tr t r pub).getD 14 0 = _
    rw [hq, m2]; rfl
  · show limbBytes (((av tr t r pub).drop 15).take 14) = _
    rw [hq, m3, List.take_of_length_le (by rw [limbs14_len]; exact Nat.le_refl _),
      limbs14_dec _ (fun j hj => hB _ (mem_b (by omega)))]
    apply List.map_congr_left; intro j hj; have := List.mem_range.1 hj
    show UInt8.ofNat (ev tr t r pub (Stc.c "b" (97 + j))) = UInt8.ofNat (ev tr t r pub (Stc.mI (97 + j)))
    unfold Stc.mI Stc.NB; rw [if_pos (by omega)]

theorem take42 (f : Nat → Nat) :
    ((List.range 48).map fun j => UInt8.ofNat (f j)).take 42 = (List.range 42).map fun j => UInt8.ofNat (f j) := by
  rw [← List.map_take, List.take_range]; rfl

include hc hA hB hHi hLo hC in
/-- **`StcOK` for an active `STC` row** (and `wsLen ≤ 2^D`). -/
theorem stc_row_ok (hD : D ≤ 20)
    (h1 : ∀ x ∈ compRecv (ev tr t r pub (Stc.c "ci1"))
      ((ivW ++ Stc.blockW Stc.mI "si" 0 ++ wordsOf (fun u => Stc.c "hi" u) 8).map (dec3 tr t r pub)), x ∈ chip)
    (h2 : ∀ x ∈ compRecv (ev tr t r pub (Stc.c "ci2"))
      ((wordsOf (fun u => Stc.c "hi" u) 8 ++ Stc.blockW Stc.mI "si" 1 ++ digW (fun u => Stc.c "di" u) ++
        wordsOf (fun u => Stc.c "xi" u) 2).map (dec3 tr t r pub)), x ∈ chip)
    (h3 : ∀ x ∈ compRecv (ev tr t r pub (Stc.c "co1"))
      ((ivW ++ Stc.blockW Stc.mO "so" 0 ++ wordsOf (fun u => Stc.c "ho" u) 8).map (dec3 tr t r pub)), x ∈ chip)
    (h4 : ∀ x ∈ compRecv (ev tr t r pub (Stc.c "co2"))
      ((wordsOf (fun u => Stc.c "ho" u) 8 ++ Stc.blockW Stc.mO "so" 1 ++ digW (fun u => Stc.c "do" u) ++
        wordsOf (fun u => Stc.c "xo" u) 2).map (dec3 tr t r pub)), x ∈ chip) :
    StcOK (decR (qv tr t r pub)) (decR (av tr t r pub)) (toB (TmplWsx.pubDig pub PUB_WSA))
      (toB (TmplWsx.pubDig pub PUB_WSB)) (WsLen.wsLen pub) (decM (av tr t r pub)) (decM (qv tr t r pub)) ∧
      WsLen.wsLen pub ≤ 2 ^ D := by
  obtain ⟨q1, q2, q3⟩ := qv_dec (tr := tr) (t := t) (r := r) (pub := pub) hB
  obtain ⟨a1, a2, a3⟩ := av_dec (tr := tr) (t := t) (r := r) (pub := pub) hB
  have hin : toB (TmplWsx.pubDig pub PUB_WSA) = (List.range 48).map fun j => UInt8.ofNat (FI tr t r pub (1 + j)) :=
    toB_dig _ _ (wsI hc hA hB hHi hLo)
  have hout : toB (TmplWsx.pubDig pub PUB_WSB) = (List.range 48).map fun j => UInt8.ofNat (FO tr t r pub (1 + j)) :=
    toB_dig _ _ (wsO hc hA hB hHi hLo)
  refine ⟨⟨comI tr t r pub, comI_wf hc hA hB hD, ?_, hin.symm, rfl, a2.symm, a3.symm, ?_⟩,
    (lenI hc hA hB hD).2.2⟩
  · rw [ser_comI hc hA hB hD, NearSpecV3.E2E.Bnd.bdigest, sha_in hc hA hB hHi hLo hC h1 h2, q1]
    exact take42 _
  · rw [ser_close hc hA hB hD _ _ hout q2 q3, NearSpecV3.E2E.Bnd.bdigest, sha_out hc hA hB hHi hLo hC h3 h4, a1]
    exact (take42 _).symm

end Row

/-! ## From `Holds` -/

section Holds
variable {A : Air} {tr : Trace Fp} {pub : List Fp} {D t : Nat}
  (hH : Holds A pub tr) (ht : t < A.tables.length) (hT : A.tables[t]! = Stc.table D)
  (hR : ∀ m ∈ busList A tr pub B_SRNG true, tn (m.getD 0 0) < 256)
  (hC : Sha512IfContract cW ((busList A tr pub B_IF384 true).map decIf))

include hH ht hT hR in
theorem srng_rcv {r : Nat} (hr : r < tr.height t) (hA : ev tr t r pub (Stc.c "act") = 1) {x : Expr}
    (hi : rcv B_SRNG (Stc.c "act") [x] ∈ (Stc.table D).interactions) : ev tr t r pub x < 256 := by
  have h1 := mem_busList A ht (by rw [hT]; exact hi) hr (mult_one (DecodeM5a.ev_one_eval hA))
  have h2 := (holds_perm hH B_SRNG).mem_iff.2 h1
  exact hR _ h2

theorem rng_mem {i : Interaction} (h : i ∈ Stc.ranges) : i ∈ (Stc.table D).interactions :=
  List.mem_append_right _ h

theorem comps_mem {i : Interaction} (h : i ∈ Stc.comps) : i ∈ (Stc.table D).interactions :=
  List.mem_append_left _ (List.mem_append_right _ h)

include hH ht hT hR hC in
/-- **`StcOK` from `Holds`**, for every active `STC` row. -/
theorem stc_holds (hD : D ≤ 20) {r : Nat} (hr : r < tr.height t) (hA : ev tr t r pub (Stc.c "act") = 1) :
    StcOK (decR (qv tr t r pub)) (decR (av tr t r pub)) (toB (TmplWsx.pubDig pub PUB_WSA))
      (toB (TmplWsx.pubDig pub PUB_WSB)) (WsLen.wsLen pub) (decM (av tr t r pub)) (decM (qv tr t r pub)) ∧
      WsLen.wsLen pub ≤ 2 ^ D := by
  have hc : ∀ e ∈ (Stc.table D).constraints, ev tr t r pub e = 0 := by
    intro e he
    have h := hH.constr t ht r hr e
    rw [← getElem!_pos _ t ht, hT] at h
    exact ev_of_eval (h he)
  have hB : ∀ x ∈ Stc.byteCols, ev tr t r pub x < 256 := fun x hx =>
    srng_rcv hH ht hT hR hr hA (rng_mem (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨x, hx, rfl⟩))))
  have hHi : ∀ x ∈ Stc.hiCols, ev tr t r pub x < 256 := fun x hx =>
    srng_rcv hH ht hT hR hr hA (rng_mem (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨x, hx, rfl⟩))))
  have hLo : ∀ p ∈ Stc.loCols, ev tr t r pub p.1 < 256 ∧ ev tr t r pub (K (2 ^ (8 - p.2)) * p.1) < 256 := by
    intro p hp
    refine ⟨srng_rcv hH ht hT hR hr hA (rng_mem (List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp, ?_⟩))),
      srng_rcv hH ht hT hR hr hA (rng_mem (List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp, ?_⟩)))⟩ <;> simp
  have hperm := holds_perm hH B_IF384
  have hA' : (Stc.c "act").eval tr t r pub = 1 := DecodeM5a.ev_one_eval hA
  have sub : ∀ L : List Interaction, (∀ i ∈ L, i ∈ Stc.comps) → ∀ i ∈ L, i ∈ (A.tables[t]!).interactions :=
    fun L hL i hi => by rw [hT]; exact comps_mem (hL i hi)
  refine stc_row_ok hc hA hB hHi hLo hC hD
    (comp_mem hperm ht (sub _ fun i hi => ?_) hr hA') (comp_mem hperm ht (sub _ fun i hi => ?_) hr hA')
    (comp_mem hperm ht (sub _ fun i hi => ?_) hr hA') (comp_mem hperm ht (sub _ fun i hi => ?_) hr hA')
  · unfold Stc.comps
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hi))
  · unfold Stc.comps
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hi))
  · unfold Stc.comps
    exact List.mem_append_left _ (List.mem_append_right _ hi)
  · unfold Stc.comps
    exact List.mem_append_right _ hi

end Holds

/-! ## The STATE template with the opening: `segAir D (stcTables D ++ extra)` -/

section Seg
open StateM5a.TmplSeg
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}

theorem segc_len : (segAir D (stcTables D ++ extra) nb np).tables.length = 10 + extra.length := by
  simp [segAir, m5tSeg, stcTables]; omega

theorem segc_stc : (segAir D (stcTables D ++ extra) nb np).tables[8]! = Stc.table D := by
  simp [segAir, m5tSeg, stcTables]

theorem segc_srng : (segAir D (stcTables D ++ extra) nb np).tables[9]! = Srng.table := by
  simp [segAir, m5tSeg, stcTables]

theorem segc_extra (k : Nat) (hk : 10 ≤ k) (hk' : k < 10 + extra.length) :
    (segAir D (stcTables D ++ extra) nb np).tables[k]! ∈ extra := by
  simp only [segAir]
  rw [getElem!_pos _ k (by simp [m5tSeg, stcTables]; omega)]
  rw [List.getElem_append_right (by simp [m5tSeg]; omega)]
  rw [List.getElem_append_right (by simp [m5tSeg, stcTables]; omega)]
  exact List.getElem_mem _

theorem segc_low (k : Nat) (hk : k < 8) :
    (segAir D (stcTables D ++ extra) nb np).tables[k]! = (m5tSeg D).tables[k]! := by
  simp only [segAir]
  rw [getElem!_pos _ k (by simp [m5tSeg, stcTables]; omega), getElem!_pos _ k (by simp [m5tSeg]; omega)]
  exact List.getElem_append_left (by simp [m5tSeg]; omega)

theorem ns_low (k : Nat) (hk : k < 8) : noSnd ((m5tSeg D).tables[k]!).interactions B_SRNG = true := by
  have e : ((m5tSeg D).tables[k]!).interactions = ((m5tSeg 0).tables[k]!).interactions := by
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | rfl | omega
  rw [e]
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;> first | decide | omega

set_option maxRecDepth 100000 in
theorem ns_stc : noSnd (Stc.table D).interactions B_SRNG = true := by
  show noSnd Stc.interactions B_SRNG = true
  decide

/-- **Every `SRNG` value is a byte** (the template with the opening; `extra` does not send on it). -/
theorem srng_send_lt (hH : Holds (segAir D (stcTables D ++ extra) nb np) pub tr)
    (hxs : ∀ T ∈ extra, ∀ i ∈ T.interactions, ¬ (i.bus = B_SRNG ∧ i.send = true)) {m : List Fp}
    (hm : m ∈ busList (segAir D (stcTables D ++ extra) nb np) tr pub B_SRNG true) : tn (m.getD 0 0) < 256 := by
  obtain ⟨k, hk, r, hr, i, hi, hb, hs, rfl⟩ := busList_inv _ hm
  rw [segc_len] at hk
  by_cases h8 : k < 8
  · rw [segc_low k h8] at hi
    exact absurd (noSnd_spec (ns_low k h8) hi hb hs) id
  · by_cases h88 : k = 8
    · subst h88; rw [segc_stc] at hi
      exact absurd (noSnd_spec ns_stc hi hb hs) id
    · by_cases h9 : k = 9
      · subst h9
        rw [segc_srng] at hi
        have hc : ∀ r, r < tr.height 9 → ∀ e ∈ Rng.table.constraints, e.eval tr 9 r pub = 0 := by
          intro r hr e he
          have h := hH.constr 9 (by rw [segc_len]; omega) r hr e
          rw [← getElem!_pos _ 9 (by rw [segc_len]; omega), segc_srng] at h
          exact h he
        have hl : tr.log 9 ≤ 8 := by
          have h := (hH.logBound 9 (by rw [segc_len]; omega)).2
          rw [← getElem!_pos _ 9 (by rw [segc_len]; omega), segc_srng] at h
          exact h
        have hv := rng_v hc hl r hr
        have hH8 : tr.height 9 ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) hl
        simp only [Srng.table, Srng.interactions, List.mem_singleton] at hi
        subst hi
        show ev tr 9 r pub (Srng.c "v") < 256
        have : ev tr 9 r pub (Srng.c "v") = r := hv
        omega
      · exact absurd ⟨hb, hs⟩ (hxs _ (segc_extra k (by omega) hk) i hi)

/-- **`StcOK` on the STATE template with the opening.** -/
theorem stc_seg (hH : Holds (segAir D (stcTables D ++ extra) nb np) pub tr)
    (hxs : ∀ T ∈ extra, ∀ i ∈ T.interactions, ¬ (i.bus = B_SRNG ∧ i.send = true))
    (hC : Sha512IfContract cW ((busList (segAir D (stcTables D ++ extra) nb np) tr pub B_IF384 true).map decIf))
    (hD : D ≤ 20) {r : Nat} (hr : r < tr.height 8) (hA : ev tr 8 r pub (Stc.c "act") = 1) :
    StcOK (decR (qv tr 8 r pub)) (decR (av tr 8 r pub)) (toB (TmplWsx.pubDig pub PUB_WSA))
      (toB (TmplWsx.pubDig pub PUB_WSB)) (WsLen.wsLen pub) (decM (av tr 8 r pub)) (decM (qv tr 8 r pub)) ∧
      WsLen.wsLen pub ≤ 2 ^ D :=
  stc_holds hH (by rw [segc_len]; omega) segc_stc (fun m hm => srng_send_lt hH hxs hm) hC hD hr hA

set_option maxRecDepth 100000 in
theorem stc_buses (D : Nat) : ∀ T ∈ stcTables D, ∀ i ∈ T.interactions,
    i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG := by
  intro T hT
  simp only [stcTables, List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl
  · show ∀ i ∈ Stc.interactions, _
    decide
  · show ∀ i ∈ Srng.interactions, _
    decide

/-- **Lane B's state half of a STATE leaf, from `Holds`** (B-T3): for an active `STC` row, every
`fits` state committed by the row's input `stRoot` (`STMQ`) and related by the requests to `v'`
(`StepRel` with the engine's output meta, `STMQ`) is committed by the output `stRoot` (`STMA`) and
has the input meta (`STMA`) — or a SHA-384 collision. Premises: the chip contract, `NodeCR`, lane
E's depth, and the named leaf content `SegLeaves` (`wsLen ≤ 2^D` is now the circuit's). -/
theorem stHalf_seg (Pv : StateView.StViewParams) (hH : Holds (segAir D (stcTables D ++ extra) nb np) pub tr)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG)
    (hxs : ∀ T ∈ extra, ∀ i ∈ T.interactions, ¬ (i.bus = B_SRNG ∧ i.send = true))
    (hC : Sha512IfContract cW ((busList (segAir D (stcTables D ++ extra) nb np) tr pub B_IF384 true).map decIf))
    (hD1 : 1 ≤ D) (hD : D ≤ 20) (hCR : NodeCR cW) (hdep : Pv.depth = 24)
    (hz : toB (TmplWsx.zD D) = Merkle.zd StateView.nodeH StateView.zero48 D)
    {upd : List StateView.Entry → List StateView.Entry} (hupd : ∀ es, (upd es).length = es.length)
    (hSL : SegLeaves Pv D tr pub upd) {r : Nat} (hr : r < tr.height 8) (hA : ev tr 8 r pub (Stc.c "act") = 1)
    (v v' : NearSpecV3.E2E.Bnd.StV) (hv : StateView.stD Pv v = decR (qv tr 8 r pub))
    (hrel : StepRel Pv upd (decM (qv tr 8 r pub)) v v') :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨ (StateView.stD Pv v' = decR (av tr 8 r pub) ∧ metaOf Pv v = decM (av tr 8 r pub)) := by
  obtain ⟨hS, hn⟩ := stc_seg hH (fun T hT i hi => hxs T hT i hi) hC hD hr hA
  have hx' : ∀ T ∈ stcTables D ++ extra, ∀ i ∈ T.interactions,
      i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG := by
    intro T hT
    rcases List.mem_append.1 hT with h | h
    · exact stc_buses D T h
    · exact hx T h
  have hW := ws_moves_seg Pv hH hx' hC hD1 hD hCR hdep hz hn hupd hSL
  exact st_step Pv hS hW hupd v v' hv hrel

end Seg

#print axioms stc_holds
#print axioms stc_seg
#print axioms stHalf_seg

end StateM5a.StcSound
