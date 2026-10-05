import ZkFormal.Near.Render.Proof.RcptBytes1
import ZkFormal.Near.Link.Claim

/-!
# ZkFormal.Near.Render.Proof.RcptBytes2 — `RcptBytesStmt`

The rcpt view sends `RC` and `RF` in pieces (the claim prefix bytes, then one
receipt / refund encoding per segment at offsets `rcOffs` / `rfOffs`) and
`PEO`, `LEAF`, `RID` whole; reassembled (`emitAt_append`, `emitAt_flatMap`)
these are exactly the bytes of `rcptMsgs` (`rcptBytes : RcptBytesStmt`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-! ## `emitAt` -/

theorem emitAt_cons (id off x : Nat) (a : List Nat) :
    emitAt id off (x :: a) = [id, off, x] :: emitAt id (off + 1) a := by
  simp only [emitAt, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.succ_eq_add_one, List.getD_cons_succ]
  congr 2; omega

theorem emitAt_append (id : Nat) : ∀ (a b : List Nat) (off : Nat),
    emitAt id off (a ++ b) = emitAt id off a ++ emitAt id (off + a.length) b
  | [], b, off => by simp [emitAt]
  | x :: a, b, off => by
    rw [List.cons_append, emitAt_cons, emitAt_cons, emitAt_append id a b (off + 1)]
    simp only [List.cons_append, List.length_cons]
    rw [show off + 1 + a.length = off + (a.length + 1) by omega]

/-- Running offsets of the chunks `g 0, g 1, …`. -/
def offs (g : Nat → List Nat) (off r : Nat) : Nat := off + ((List.range r).map fun r' => (g r').length).sum

theorem emitAt_flatMap (id off : Nat) (g : Nat → List Nat) : ∀ n,
    emitAt id off ((List.range n).flatMap g) = (List.range n).flatMap fun r => emitAt id (offs g off r) (g r)
  | 0 => by simp [emitAt]
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, emitAt_append, emitAt_flatMap id off g n]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, offs]
    congr 2
    rw [List.length_flatMap]

theorem toNats_concatAll (L : List Bytes) : toNats (concatAll L) = L.flatMap toNats := by
  induction L with
  | nil => rfl
  | cons b L ih => simp [concatAll, toNats_append, ih]

/-! ## The rcpt views as a function of `r` -/

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e)

def xv (c : Claim) (e : Ext) (r : Nat) : RcptV := rcptViewOf (rdOf (mkInfo c e) r)

theorem views_eq : rcptViewsOf (mkInfo c.1 e) = (List.range e.rs.length).map (xv c.1 e) := by
  simp only [rcptViewsOf, rcptData, List.map_map]; rfl

theorem views_getD {r : Nat} (hr : r < e.rs.length) : (rcptViewsOf (mkInfo c.1 e)).getD r default = xv c.1 e r := by
  rw [views_eq]; simp [List.getD_eq_getElem?_getD, hr]

theorem rcOffs_eq : ∀ r, r ≤ e.rs.length →
    rcOffs (rcptViewsOf (mkInfo c.1 e)) r = offs (fun r => (xv c.1 e r).enc) 12 r
  | 0, _ => by simp [rcOffs, offs]
  | r + 1, h => by
    rw [rcOffs, rcOffs_eq r (by omega), views_getD (by omega)]
    simp [offs, List.range_succ, List.sum_append]; omega

theorem rfOffs_eq : ∀ r, r ≤ e.rs.length →
    rfOffs (rcptViewsOf (mkInfo c.1 e)) r =
      offs (fun r => if (xv c.1 e r).hr then (xv c.1 e r).encRefund else []) 4 r
  | 0, _ => by simp [rfOffs, offs]
  | r + 1, h => by
    rw [rfOffs, rfOffs_eq r (by omega), views_getD (by omega)]
    simp only [offs, List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    split <;> simp <;> omega

include hg

theorem hdr : Link.Hdr c := ⟨hg.pv, hg.chain⟩

omit hg in
theorem rs_eq : e.rs = (List.range e.rs.length).map e.rc := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [Ext.rc, List.getD_eq_getElem?_getD, h1]

/-- `RC` bytes: the claim's shard id and count, then the receipt encodings. -/
theorem rc_split : rcBytes (mkInfo c.1 e) =
    (pubBytes (pubOf c.1) PV_SHARD 8 ++ pubBytes (pubOf c.1) PV_N 4) ++
      (List.range e.rs.length).flatMap fun r => (xv c.1 e r).enc := by
  have h1 := Link.pub_shard (hdr hg)
  have h2 := Link.pub_n (hdr hg)
  have hp : pubOf c.1 = publicOf c := rfl
  rw [hp, h1, h2, ← hg.len]
  simp only [rcBytes, mkInfo_e, mkInfo_c, encodeReceipts, toNats_append]
  conv => lhs; rw [rs_eq]
  simp only [List.length_map, List.length_range, List.append_assoc, toNats_concatAll, List.map_map,
    List.flatMap_map]
  congr 2
  apply flatMap_congr'
  intro r hr
  exact (enc_eq hg (List.mem_range.1 hr)).symm

/-- `RF` bytes: the claim's refund count, then the refund encodings. -/
theorem rf_split : rfBytes (mkInfo c.1 e) =
    pubBytes (pubOf c.1) PV_NREF 4 ++
      (List.range e.rs.length).flatMap fun r => if (xv c.1 e r).hr then (xv c.1 e r).encRefund else [] := by
  have h1 := Link.pub_nref (hdr hg)
  have hp : pubOf c.1 = publicOf c := rfl
  rw [hp, h1, ← hg.refundCount]
  simp only [rfBytes, mkInfo_e, mkInfo_c, encodeReceipts, toNats_append, toNats_concatAll, List.flatMap_map]
  congr 1
  simp only [Ext.refunds, List.flatMap_assoc]
  apply flatMap_congr'
  intro r hr
  have hr' := List.mem_range.1 hr
  show (e.refundOf c.1 r).flatMap (fun x => toNats x.encode) =
    if hasRefund (mkInfo c.1 e) r then (xv c.1 e r).encRefund else []
  by_cases hs : surplusOf c.1.blockGasPrice (e.rc r) = 0
  · have hrf : e.refundOf c.1 r = [] := by simp [Ext.refundOf, hs]
    have hh : hasRefund (mkInfo c.1 e) r = false := by simp [hasRefund, mkInfo_e, mkInfo_c, hrf]
    simp [hrf, hh]
  · have hrf : e.refundOf c.1 r =
        [gasRefundReceipt (e.rc r) c.1.blockHeight (surplusOf c.1.blockGasPrice (e.rc r))] := by
      simp [Ext.refundOf, hs]
    have hh : hasRefund (mkInfo c.1 e) r = true := by simp [hasRefund, mkInfo_e, mkInfo_c, hrf]
    simp only [hrf, hh, ite_true, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact (encRefund_eq hg hr' hh).symm

theorem rid_eq (r : Nat) :
    (xv c.1 e r).rid ++ pubBytes (pubOf c.1) PV_HEIGHT 8 ++ List.replicate 8 0 = ridBytes (mkInfo c.1 e) r := by
  have h1 := Link.pub_height (hdr hg)
  have hp : pubOf c.1 = publicOf c := rfl
  have h8 : List.replicate 8 0 = leBytes 8 0 := by decide
  rw [hp, h1, h8]
  rfl

end

def encF (c : Claim) (e : Ext) (r : Nat) : List Nat := (xv c e r).enc
def refF (c : Claim) (e : Ext) (r : Nat) : List Nat :=
  if (xv c e r).hr then (xv c e r).encRefund else []
def rA (c : Claim) (e : Ext) (r : Nat) : List ZkFormal.Near.Msg := emitAt K_RC (offs (encF c e) 12 r) (encF c e r)
def rB (c : Claim) (e : Ext) (r : Nat) : List ZkFormal.Near.Msg := emitAt K_RF (offs (refF c e) 4 r) (refF c e r)
def rQ (c : Claim) (e : Ext) (r : Nat) : List ZkFormal.Near.Msg :=
  emitAt (msgId K_PEO r) 0 (peoBytes (mkInfo c e) r) ++ emitAt (msgId K_LEAF r) 0 (leafBytes (mkInfo c e) r) ++
    (if hasRefund (mkInfo c e) r then emitAt (msgId K_RID r) 0 (ridBytes (mkInfo c e) r) else [])

theorem encF_def (c : Claim) (e : Ext) : encF c e = fun r => (xv c e r).enc := rfl
theorem refF_def (c : Claim) (e : Ext) :
    refF c e = fun r => if (xv c e r).hr then (xv c e r).encRefund else [] := rfl

theorem sends_eq {c : WfClaim} {e : Ext} (hg : Good c.1 e) :
    rcptSends (pubOf c.1) (rcptViewsOf (mkInfo c.1 e)) B_BYTES =
      emitAt K_RC 0 (pubBytes (pubOf c.1) PV_SHARD 8 ++ pubBytes (pubOf c.1) PV_N 4) ++
        emitAt K_RF 0 (pubBytes (pubOf c.1) PV_NREF 4) ++
        (List.range e.rs.length).flatMap fun r => rA c.1 e r ++ rB c.1 e r ++ rQ c.1 e r := by
  have hL : (rcptViewsOf (mkInfo c.1 e)).zip (List.range (rcptViewsOf (mkInfo c.1 e)).length) =
      (List.range e.rs.length).map fun r => (xv c.1 e r, r) := by
    rw [views_eq, List.length_map, List.length_range, zip_range_map]
  simp only [rcptSends, ↓reduceIte]
  rw [hL, List.flatMap_map]
  apply congrArg
  apply flatMap_congr'
  intro r hr
  have hr' : r < e.rs.length := List.mem_range.1 hr
  have h1 := rcOffs_eq (c := c) (e := e) r (Nat.le_of_lt hr')
  have h2 := rfOffs_eq (c := c) (e := e) r (Nat.le_of_lt hr')
  simp only [rA, rB, rQ, encF_def, refF_def, h1, h2]
  rw [show (xv c.1 e r).peo = peoBytes (mkInfo c.1 e) r from peo_eq hg hr',
    show (xv c.1 e r).leaf = leafBytes (mkInfo c.1 e) r from leaf_eq,
    show (xv c.1 e r).hr = hasRefund (mkInfo c.1 e) r from rfl, rid_eq hg r]
  cases hasRefund (mkInfo c.1 e) r <;> simp [emitAt, List.append_assoc]

theorem msgs_bytes_eq {c : WfClaim} {e : Ext} (hg : Good c.1 e) :
    emitAll (rcptMsgs (mkInfo c.1 e)) =
      (emitAt K_RC 0 (pubBytes (pubOf c.1) PV_SHARD 8 ++ pubBytes (pubOf c.1) PV_N 4) ++
        (List.range e.rs.length).flatMap (rA c.1 e)) ++
      (emitAt K_RF 0 (pubBytes (pubOf c.1) PV_NREF 4) ++ (List.range e.rs.length).flatMap (rB c.1 e)) ++
      (List.range e.rs.length).flatMap (rQ c.1 e) := by
  simp only [emitAll, rcptMsgs, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [rc_split hg, rf_split hg,
    emitAt_append _ (pubBytes (pubOf c.1) PV_SHARD 8 ++ pubBytes (pubOf c.1) PV_N 4),
    emitAt_append _ (pubBytes (pubOf c.1) PV_NREF 4), emitAt_flatMap, emitAt_flatMap]
  have e12 : 0 + (pubBytes (pubOf c.1) PV_SHARD 8 ++ pubBytes (pubOf c.1) PV_N 4).length = 12 := by
    simp [pubBytes]
  have e4 : 0 + (pubBytes (pubOf c.1) PV_NREF 4).length = 4 := by simp [pubBytes]
  have hm : ∀ k, msgId k 0 = k := fun k => by simp [msgId]
  rw [e12, e4, hm, hm]
  have hQ : ((List.range (mkInfo c.1 e).nRcpt).flatMap fun r =>
      [({ id := msgId K_PEO r, bytes := peoBytes (mkInfo c.1 e) r } : Render.Msg),
        { id := msgId K_LEAF r, bytes := leafBytes (mkInfo c.1 e) r }] ++
      if hasRefund (mkInfo c.1 e) r = true then
        [({ id := msgId K_RID r, bytes := ridBytes (mkInfo c.1 e) r } : Render.Msg)] else []).flatMap
        (fun m => emitAt m.id 0 m.bytes) = (List.range e.rs.length).flatMap (rQ c.1 e) := by
    rw [List.flatMap_assoc]
    apply flatMap_congr'
    intro r _
    simp only [rQ]
    cases hasRefund (mkInfo c.1 e) r <;> simp
  rw [hQ]
  simp only [List.append_assoc]
  rfl

/-- **`RcptBytesStmt`.** -/
theorem rcptBytes : RcptBytesStmt := by
  intro c e hg _
  rw [sends_eq hg, msgs_bytes_eq hg]
  have h1 := perm_flatMap_append (List.range e.rs.length) (fun r => rA c.1 e r ++ rB c.1 e r) (rQ c.1 e)
  have h2 := perm_flatMap_append (List.range e.rs.length) (rA c.1 e) (rB c.1 e)
  rw [List.perm_iff_count]
  intro a
  have c1 := h1.count_eq a
  have c2 := h2.count_eq a
  simp only [List.count_append] at c1 c2 ⊢
  omega

end ZkFormal.Near.Render