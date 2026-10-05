import ZkFormal.Near.Link.Run

/-!
# ZkFormal.Near.Link.Refunds — `refunds_ok : RefundsStmt`
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace Link

theorem systemN_eq : toBytes ([6, 0, 0, 0] ++ systemN) = borshBytes AccountId.system := by decide
theorem zeros16_eq : toBytes (List.replicate 16 0) = u128 0 := by decide
theorem zeros8_eq : toBytes (List.replicate 8 0) = u64 0 := by decide

theorem toBytes_encRefund {x : RcptV} {r a b c : Nat} (w : x.Wf r a b c) (height refund : Nat)
    (hrfid : toBytes x.rfid = receiptIdFrom (toBytes x.rid) height 0)
    (hramt : leN' x.ramt = refund) :
    toBytes x.encRefund = (gasRefundReceipt x.toReceipt height refund).encode := by
  obtain ⟨hp, hv, hs⟩ := idLens w
  obtain ⟨-, -, h3, -, -, -, -, -, -, -, h11, -⟩ := w.lens
  have hkt : x.kt < 256 := by omega
  simp only [RcptV.encRefund, toBytes_append, gasRefundReceipt, RcptV.toReceipt, Receipt.encode,
    PublicKey.encode]
  have hr16 : u128 (leN' x.ramt) = toBytes x.ramt := leN_leN' h11
  rw [← toBytes_append, systemN_eq, toBytes_borshN (by omega), hrfid, zeros16_eq, tailN_eq,
    ← hramt, hr16]
  have : u8 x.kt = toBytes [x.kt] := by
    simp only [u8, leN, toBytes, List.map_cons, List.map_nil, Nat.mod_eq_of_lt hkt]
  rw [this]
  simp only [List.append_assoc]; rfl

theorem concatAll_append (a b : List Bytes) : concatAll (a ++ b) = concatAll a ++ concatAll b := by
  induction a with
  | nil => rfl
  | cons x a ih => simp only [List.cons_append, concatAll, ih, List.append_assoc]

theorem concatAll_flatMap {α : Type} (g : α → List Receipt) :
    ∀ l : List α, concatAll ((l.flatMap g).map Receipt.encode) =
      concatAll (l.map fun x => concatAll ((g x).map Receipt.encode))
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, List.map_append, concatAll_append, concatAll_flatMap g l]; rfl

theorem map_range_getD {α : Type} (l : List α) (d : α) :
    (List.range l.length).map (fun r => l.getD r d) = l :=
  List.ext_getElem (by simp) (fun i h1 h2 => by simp [List.getD_eq_getElem?_getD, h2])

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (by simp),
      flatMap_congr' l (fun y hy => h y (by simp [hy]))]

theorem range_flatMap_getD {α β : Type} (g : α → List β) (d : α) :
    ∀ (l : List α), (List.range l.length).flatMap (fun r => g (l.getD r d)) = l.flatMap g
  | [] => rfl
  | x :: l => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [range_flatMap_getD g d l, List.flatMap_cons]

def refundG (bh : Nat) (x : RcptV) : List Receipt :=
  if x.hr then [gasRefundReceipt x.toReceipt bh (leN' x.ramt)] else []

theorem length_flatMap_refundG (bh : Nat) :
    ∀ (rs : RcptVs), (rs.flatMap (refundG bh)).length = (rs.filter (·.hr)).length
  | [] => rfl
  | x :: rs => by
    rw [List.flatMap_cons, List.length_append, length_flatMap_refundG bh rs, List.filter_cons]
    unfold refundG; cases x.hr <;> simp <;> omega

theorem refunds_ok : RefundsStmt := by
  intro c vs ws rs as mv ids shaS shaR h
  obtain ⟨toks, -, h0, hw, -⟩ := toks_spec h
  have hh := hdr_of c h.rcpt
  -- per receipt: refund list ↔ `hr`
  have href : ∀ r (hr : r < rs.length), (linkExt vs as rs).refundOf c.1 r =
      if rs[r].hr then [gasRefundReceipt rs[r].toReceipt c.1.blockHeight (leN' rs[r].ramt)] else [] := by
    intro r hr
    have ar := arith_ok h hr (hw r hr)
    obtain ⟨-, -, -, -, -, -, a7, a8, -⟩ := ar
    simp only [Ext.refundOf, surplusOf, burnPrice, rc_eq hr, RcptV.toReceipt]
    by_cases hhr : rs[r].hr = true
    · rw [if_neg (a7.mp hhr), if_pos hhr, a8 hhr]
    · have : Params.G * (leN' rs[r].gp - min (leN' rs[r].gp) c.1.blockGasPrice) = 0 := by
        exact Classical.byContradiction fun hc => hhr (a7.mpr hc)
      rw [if_pos this, if_neg hhr]
  have hlen : (linkExt vs as rs).rs.length = rs.length := by simp [linkExt]
  have hrefs : (linkExt vs as rs).refunds c.1 = rs.flatMap (refundG c.1.blockHeight) := by
    simp only [Ext.refunds, hlen]
    rw [← range_flatMap_getD (refundG c.1.blockHeight) default rs]
    apply flatMap_congr'; intro r hr
    have hr' := List.mem_range.mp hr
    rw [href r hr', List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr']; rfl
  obtain ⟨-, -, -, -, -, bnr, -, -⟩ := wf_bounds c
  have hcount : (rs.filter (·.hr)).length = c.1.refundCount := by
    rw [h.rcpt.refunds (fun _ _ => pubNat_lt c _), leN'_pub_field (pub_nref hh) bnr]
  have hcnt : ((linkExt vs as rs).refunds c.1).length = c.1.refundCount := by
    rw [hrefs, length_flatMap_refundG, hcount]
  refine ⟨hcnt, ?_⟩
  obtain ⟨hb, hd⟩ := rf_digest h
  rw [hd, refundsCommitment, encodeReceipts, hcnt, rfMsg_eq, toBytes_append,
    toBytes_pubBytes (pub_nref hh), toBytes_flatMap, hrefs, concatAll_flatMap]
  congr 1
  apply congrArg (u32 c.1.refundCount ++ ·)
  apply congrArg concatAll
  apply List.map_congr_left
  intro x hx
  obtain ⟨r, hr', rfl⟩ := List.mem_iff_getElem.mp hx
  simp only [rfPart, refundG]
  split
  · next hhr =>
    obtain ⟨_, _, _, w⟩ := rcpt_wf_at h hr'
    obtain ⟨hrb, hrd⟩ := rid_digest h hr' hhr
    have hrfid : toBytes rs[r].rfid = receiptIdFrom (toBytes rs[r].rid) c.1.blockHeight 0 := by
      rw [hrd, toBytes_map_toNat, receiptIdFrom, ridMsg, toBytes_append, toBytes_append,
        toBytes_pubBytes (pub_height hh), zeros8_eq]
    rw [toBytes_encRefund w _ _ hrfid rfl]
    simp [concatAll]
  · rfl

end Link

end ZkFormal.Near
