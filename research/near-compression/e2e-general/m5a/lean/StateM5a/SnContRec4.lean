import StateM5a.SnContRec3
import StateM5a.SnStore2

/-!
# StateM5a.SnContRec4 — the decoded records of a continued head, `OldOK` / `NewOK`

For a row with `cont = 1` the head-only records `snOld` / `snNew` (key `snKey`, read from the
head's 64 key cells) are not its node.  The **continued records** `snOldC` / `snNewC` are
`gRecK` over the node's full key `ckey …`: a key whose record is `Hashed` to the head's digest
(`ho` / `hn`), with `2·(hplen − 1) + odd` nibbles (chosen by `Classical.epsilon`; one exists by
`SnContRec3.grecK_hashed`, the decoded `hexPrefix` of the SHA-256 message).

* **`cont_old_hashed`** / **`cont_new_hashed`**: the continued records are `Hashed` to the
  digests the head receives;
* **`cont_oldOK`** / **`cont_newOK`**: `OldOK σ (snIn r) (snOldC r)` and `NewOK σ (snOut r) (snNewC r)`
  for any store `σ` (a continued node is always hashed, never on `VER`).

No cryptographic assumption.  Premises: `SnRange`'s `hxB hxD hxK hN hxr`, plus `hxR`, `hxRr`.
-/

namespace StateM5a.SnContRec4

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KcChain StateM5a.KeyDigest StateM5a.BrDigest StateM5a.BrSer StateM5a.SnSer
open StateM5a.KeyDecode StateM5a.SnDigest StateM5a.SnContHead StateM5a.SnContMem StateM5a.SnRec
open StateM5a.SnContRec1 StateM5a.SnContRec2 StateM5a.SnContRec3 StateM5a.RowSnMsg StateM5a.RowSnN
open StateM5a.SnHashed StateM5a.SnStore2

set_option maxRecDepth 100000

section
variable (tr : Trace Fp) (pub : List Fp) (r : Nat)

/-- The key-correctness predicate: a full key whose record is hashed to the digest `hb`. -/
def KeyOK (x : Nat → Expr) (xf : Expr) (mb hb : Nat → Expr) (K : List Nat) : Prop :=
  K.length = 2 * (ev tr 3 r pub (Sn.c "hplen") - 1) + ev tr 3 r pub (Sn.c "odd") ∧ nibblesOk K = true ∧
    Hashed (gRecK tr pub r K x xf mb) (bytesOf ((pack2 hb).map (nE tr pub r)))

/-- **The full key** of a continued head's node (old: `x, xf, mem, ho`; new: `nx, nxf, nmem, hn`). -/
noncomputable def ckey (x : Nat → Expr) (xf : Expr) (mb hb : Nat → Expr) : List Nat :=
  Classical.epsilon (KeyOK tr pub r x xf mb hb)

/-- **The old record of a continued head** (over its full key). -/
noncomputable def snOldC : Rec :=
  gRecK tr pub r (ckey tr pub r (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b) (fun b => Sn.c "ho" b))
    (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b)

/-- **The new record of a continued head** (over its full key). -/
noncomputable def snNewC : Rec :=
  gRecK tr pub r (ckey tr pub r (fun t => Sn.c "nx" t) (Sn.c "nxf") (fun b => Sn.c "nmem" b) (fun b => Sn.c "hn" b))
    (fun t => Sn.c "nx" t) (Sn.c "nxf") (fun b => Sn.c "nmem" b)

end

theorem ckey_spec {tr : Trace Fp} {pub : List Fp} {r : Nat} {x : Nat → Expr} {xf : Expr} {mb hb : Nat → Expr}
    (h : ∃ K, KeyOK tr pub r x xf mb hb K) : KeyOK tr pub r x xf mb hb (ckey tr pub r x xf mb hb) :=
  Classical.epsilon_spec h

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
variable (hH : Holds (fullAir D extra nb np) pub tr)
  (hxB : XSbHi D extra nb np tr pub)
  (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
  (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
  (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
  (hxRr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_KCR)
  (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hxr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_RNG)

include hH hxB hxD hxK hxR hxRr hN hxr in
/-- **A continued head's old node**: its full key is `KeyOK` (`gold`). -/
theorem cont_old_key {r : Nat} (hr : r < tr.height 3) (hcont : ev tr 3 r pub (Sn.c "cont") = 1)
    (hg : ev tr 3 r pub (Sn.c "gold") = 1) :
    KeyOK tr pub r (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b) (fun b => Sn.c "ho" b)
      (ckey tr pub r (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b) (fun b => Sn.c "ho" b)) := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hs := ch_gsha hc hcont hg
  have hA := SnRec.sn_act_of hH hr (Or.inl hs)
  obtain ⟨M, hML, hMb, hH32, hH256, hby, hdg⟩ := cont_node hH hxB hxD hxK hxR hxRr hr (par := 0)
    (Nat.zero_le _) (SnRec.ev_idS hH hr).1 rfl sn_sd_old
    (fun i hi hb hs hh => mem_of_filter sn_sb_old hi (pred_true hb hs hh)) hs hA hcont
  obtain ⟨hl, hn, hR⟩ := grecK_hashed hc hA (sn_k16 hH hN hxr hr 0 (by decide)) hML hMb hH32 hH256 hby
    (fun h1 => FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_x3) h1)
    (fun _ => FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_gxf) hs) (xf := Sn.c "xf")
  exact ckey_spec ⟨_, hl, hn, by rw [hdg]; exact hR⟩

include hH hxB hxD hxK hxR hxRr hN hxr in
/-- **A continued head's new node**: its full key is `KeyOK` (`gnew`). -/
theorem cont_new_key {r : Nat} (hr : r < tr.height 3) (hcont : ev tr 3 r pub (Sn.c "cont") = 1)
    (hg : ev tr 3 r pub (Sn.c "gnew") = 1) :
    KeyOK tr pub r (fun t => Sn.c "nx" t) (Sn.c "nxf") (fun b => Sn.c "nmem" b) (fun b => Sn.c "hn" b)
      (ckey tr pub r (fun t => Sn.c "nx" t) (Sn.c "nxf") (fun b => Sn.c "nmem" b) (fun b => Sn.c "hn" b)) := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hf := ch_gfin hc hcont hg
  have hA := SnRec.sn_act_of hH hr (Or.inr hg)
  obtain ⟨M, hML, hMb, hH32, hH256, hby, hdg⟩ := cont_node hH hxB hxD hxK hxR hxRr hr (par := 1)
    (Nat.le_refl _) (SnRec.ev_idS hH hr).2 rfl sn_sd_new
    (fun i hi hb hs hh => mem_of_filter sn_sb_new hi (pred_true hb hs hh)) hf hA hcont
  obtain ⟨hfl, h1, h2, h3, h4, h5, h6, -, h9⟩ := sn_ops hc
  have := hfl "oLR" (by simp [RowSn.snNames]); have := hfl "oLM" (by simp [RowSn.snNames])
  have := hfl "act" (by simp [RowSn.snNames])
  obtain ⟨hl, hn, hR⟩ := grecK_hashed hc hA (sn_k16 hH hN hxr hr 0 (by decide)) hML hMb hH32 hH256 hby
    (fun hl => FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_nx3) (by rw [ev_hadd]; omega))
    (fun _ => FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_gnxf) hf) (xf := Sn.c "nxf")
  exact ckey_spec ⟨_, hl, hn, by rw [hdg]; exact hR⟩

include hH hxB hxD hxK hxR hxRr hN hxr in
/-- **`OldOK` of a continued head's old record** (any store). -/
theorem cont_oldOK (σ : Store) {r : Nat} (hr : r < tr.height 3) (hcont : ev tr 3 r pub (Sn.c "cont") = 1)
    (hg : ev tr 3 r pub (Sn.c "gold") = 1) : OldOK σ (snIn tr pub r) (snOldC tr pub r) := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hs := ch_gsha hc hcont hg
  have ho : ev tr 3 r pub (Sn.c "oref") = 0 := FieldVer.gate_zero (FieldRows.hold rfl hc sn_mem_gor) hs
  unfold snIn
  rw [VerStore.refOf_dig _ _ (VerStore.pack2_len fun b => Sn.c "ho" b) ho]
  exact VerStore.oldOK_dig (cont_old_key hH hxB hxD hxK hxR hxRr hN hxr hr hcont hg).2.2

include hH hxB hxD hxK hxR hxRr hN hxr in
/-- **`NewOK` of a continued head's new record** (any store). -/
theorem cont_newOK (σ : Store) {r : Nat} (hr : r < tr.height 3) (hcont : ev tr 3 r pub (Sn.c "cont") = 1)
    (hg : ev tr 3 r pub (Sn.c "gnew") = 1) : NewOK σ (snOut tr pub r) (snNewC tr pub r) := by
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have hR := (cont_new_key hH hxB hxD hxK hxR hxRr hN hxr hr hcont hg).2.2
  right
  refine ⟨_, ?_, hR.1, hR.2.2.2⟩
  unfold snOut; exact VerStore.refOf_dig _ _ (VerStore.pack2_len fun b => Sn.c "hn" b) (ch_nref hc hcont)

end

end StateM5a.SnContRec4
