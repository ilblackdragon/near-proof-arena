import ZkFormal.Near.Render.Proof.BusRids
import ZkFormal.Near.Render.Proof.MrkTraffic3
import ZkFormal.Near.Render.Proof.ShaTab
import ZkFormal.Near.Spec.SoundAccount

/-!
# ZkFormal.Near.Render.Proof.BusBytes — the `BYTES` bus balances

The `sha` table receives `(Id, i, bytes[i])` for every byte of every message
of the bundle (`emitAll (bundle c e).msgs`, `expectedBytes_eq`); the node,
rcpt, acct and mrk views send exactly those of their own messages:

* acct (`acct_bytes`): `VPRE k`, and `VPOST k` as `post[0..16) ‖ pre[16..)`
  (only the amount changes: `encode_decode`);
* mrk (`mrk_bytes`): `MRK(q)`, `q = hashedBefore` = the generator's index;
* node (`NodeSerStmt`): the views serialize as `mkInfo`'s `pre`/`post`
  (the node lane's `nodeSer` of the views);
* rcpt (`RcptBytesStmt`): `RC`, `RF` in pieces, `PEO`, `LEAF`, `RID`.

`bytesBus_of : NodeSerStmt → RcptBytesStmt → BytesBusStmt`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

/-- All `BYTES` messages of a message list. -/
def emitAll (ms : List Render.Msg) : List ZkFormal.Near.Msg := ms.flatMap fun m => emitAt m.id 0 m.bytes

theorem emitAll_append (a b : List Render.Msg) : emitAll (a ++ b) = emitAll a ++ emitAll b := by
  simp [emitAll]

theorem expectedBytes_eq (ms : List Render.Msg) :
    Sha.Gen.expectedBytes (ms.map fun m => ⟨m.id, m.bytes, true⟩) = emitAll ms := by
  simp [Sha.Gen.expectedBytes, emitAll, emitAt, List.flatMap_map]

theorem cnt_append (a b : List ZkFormal.Near.Msg) (m : List Fp) : cnt (a ++ b) m = cnt a m + cnt b m := by
  simp [cnt, List.count_append]

/-- The node views serialize as the generator's `pre`/`post` (node lane). -/
def NodeSerStmt : Prop :=
  ∀ (c : WfClaim) (e : Ext), Good c.1 e → Small e → ∀ n, n < e.ns.length →
    (nodeViewOf (mkInfo c.1 e) (edgeUses (bundle c.1 e).walks) n).v.ser false = (mkInfo c.1 e).pre.getD n [] ∧
    (nodeViewOf (mkInfo c.1 e) (edgeUses (bundle c.1 e).walks) n).v.ser true = (mkInfo c.1 e).post.getD n []

/-- The rcpt view sends exactly the bytes of the rcpt messages. -/
def RcptBytesStmt : Prop :=
  ∀ (c : WfClaim) (e : Ext), Good c.1 e → Small e →
    (rcptSends (pubOf c.1) (rcptViewsOf (mkInfo c.1 e)) B_BYTES).Perm (emitAll (rcptMsgs (mkInfo c.1 e)))

section
variable {c : Claim} {e : Ext}

/-! ## node -/

theorem node_bytes (uses : Std.HashMap Edge Nat)
    (h : ∀ n, n < e.ns.length →
      (nodeViewOf (mkInfo c e) uses n).v.ser false = (mkInfo c e).pre.getD n [] ∧
      (nodeViewOf (mkInfo c e) uses n).v.ser true = (mkInfo c e).post.getD n []) :
    nodeSends (nodeViewsOf (mkInfo c e) uses) B_BYTES = emitAll (nodeMsgs (mkInfo c e)) := by
  simp only [nodeSends, ↓reduceIte, nodeViewsOf, List.length_map, List.length_range, zip_range_map,
    List.flatMap_map, emitAll, nodeMsgs, List.flatMap_assoc]
  apply flatMap_congr'
  intro n hn
  have hns : (mkInfo c e).ns = e.ns.toArray := rfl
  have hn' : n < e.ns.length := by simpa [hns] using hn
  obtain ⟨h1, h2⟩ := h n hn'
  simp [h1, h2]

/-! ## acct -/

theorem acct_post_split (hg : Good c e) {k : Nat} (hk : k ∈ (mkInfo c e).touched) :
    ((mkInfo c e).vpost.getD k []).take 16 ++ ((mkInfo c e).vpre.getD k []).drop 16 =
      (mkInfo c e).vpost.getD k [] := by
  obtain ⟨nr, h1, h2⟩ := mem_touched.1 hk
  rw [vpre_eq hk, vpost_eq hk]
  have hv := hg.vals_v1 k nr h1 h2
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hv
  have he : e.vals0 k = Account.encode a := (Sound.encode_decode ha).symm
  have hacc : e.acc0 k = a := by simp [Ext.acc0, ha]
  simp only [Ext.valsAt, hacc, he, Account.encode, toNats, List.map_append, u128]
  have l1 : ((leN 16 (e.amtAt k e.rs.length)).map UInt8.toNat).length = 16 := by simp [leN_length]
  have l2 : ((leN 16 a.amount).map UInt8.toNat).length = 16 := by simp [leN_length]
  simp only [List.append_assoc]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]

theorem acct_bytes (hg : Good c e) :
    acctSends (acctViewsOf (mkInfo c e)) B_BYTES = emitAll (acctMsgs (mkInfo c e)) := by
  simp only [acctSends, ↓reduceIte, acctViewsOf, List.flatMap_map, emitAll, acctMsgs, List.flatMap_assoc]
  apply flatMap_congr'
  intro k hk
  rw [acct_post_split hg hk]
  simp

end

/-! ## mrk -/

theorem filterMap_flatMap {α β γ : Type} (F : α → Option β) (H : β → List γ) :
    ∀ l : List α, (l.filterMap F).flatMap H = l.flatMap fun x => ((F x).map H).getD []
  | [] => rfl
  | x :: l => by
    rw [List.filterMap_cons, List.flatMap_cons, ← filterMap_flatMap F H l]
    cases F x <;> simp

theorem flatMap_range_getD {α γ : Type} (d : α) (G : α → List γ) (l : List α) :
    (List.range l.length).flatMap (fun q => G (l.getD q d)) = l.flatMap G := by
  have : (List.range l.length).map (fun q => l.getD q d) = l := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getD_eq_getElem?_getD, h2]
  conv => rhs; rw [← this]
  rw [List.flatMap_map]

open MrkTraffic MrkGen in
theorem mrk_bytes (I : Info) (hn : 1 ≤ I.nRcpt) :
    mrkSends (pubOf I.c) (mrkViewOf I) B_BYTES = emitAll (mrkMsgs I) := by
  have hv : (mrkViewOf I).nodes = (mrkShape I.nRcpt).map (gNode ((List.range (I.nRcpt + 2)).map (levels I))) := by
    simp only [mrkViewOf]; rfl
  simp only [mrkSends, ↓reduceIte, hv, emitAll, mrkMsgs]
  rw [zip_range_getD default, List.flatMap_map, filterMap_flatMap, List.length_map,
    ← flatMap_range_getD (0, 0, false)]
  apply flatMap_congr'
  intro q hq
  have hq' : q < (mrkShape I.nRcpt).length := List.mem_range.1 hq
  have hx : (mrkShape I.nRcpt).getD q (0, 0, false) = (mrkShape I.nRcpt)[q] := by
    simp [List.getD_eq_getElem?_getD, hq']
  have hg : ((mrkShape I.nRcpt).map (gNode ((List.range (I.nRcpt + 2)).map (levels I)))).getD q default =
      gNode ((List.range (I.nRcpt + 2)).map (levels I)) (mrkShape I.nRcpt)[q] := by
    simp [List.getD_eq_getElem?_getD, hq']
  rw [hx, hg]
  generalize hy : (mrkShape I.nRcpt)[q] = y at *
  obtain ⟨j, i, h⟩ := y
  cases h with
  | false => rfl
  | true =>
    have := hashedBefore_eq hn ((List.range (I.nRcpt + 2)).map (levels I)) hq' (by rw [hy])
    rw [hy] at this
    simp only [gNode, ↓reduceIte, Option.map_some, Option.getD_some, this]
    rfl

/-- **`BytesBusStmt`** from the node and rcpt byte facts. -/
theorem bytesBus_of (hN : NodeSerStmt) (hR : RcptBytesStmt) : BytesBusStmt := by
  intro c e hg hs m
  rw [hcount_eq, hcount_eq]
  have h1 := node_bytes (c := c.1) (e := e) (edgeUses (bundle c.1 e).walks) (hN c e hg hs)
  have h2 := acct_bytes hg
  have h3 : mrkSends (pubOf c.1) (mrkViewOf (mkInfo c.1 e)) B_BYTES = emitAll (mrkMsgs (mkInfo c.1 e)) :=
    mrk_bytes (mkInfo c.1 e) (by show 1 ≤ e.rs.length; rw [hg.len]; exact hg.n_pos)
  have h4 := cnt_perm (hR c e hg hs) m
  have hm : (bundle c.1 e).msgs = nodeMsgs (mkInfo c.1 e) ++ acctMsgs (mkInfo c.1 e) ++
      mrkMsgs (mkInfo c.1 e) ++ rcptMsgs (mkInfo c.1 e) := rfl
  simp only [sel, ↓reduceIte, Bool.false_eq_true, nodeTraffic, rcptTraffic, acctTraffic, mrkTraffic,
    bundle_info]
  rw [h1, h2, h3, h4]
  simp only [shaTraffic, nodeRecvs, walkTraffic, walkSends, walkRecvs, rcptRecvs, acctRecvs, mrkRecvs,
    sortTraffic, B_VSLOT, B_DIGEST, B_BYTES, B_PARENT, B_EDGE, B_KEYNIB, B_FINAL, B_MEM, B_RIDS, B_MPOS,
    Nat.reduceEqDiff, ↓reduceIte, cnt_nil, Nat.zero_add, Nat.add_zero]
  rw [show (List.map (fun m => ({ id := m.id, bytes := m.bytes, dmult := true } : Sha.Gen.Msg)) (bundle c.1 e).msgs) =
      shaMsgs (bundle c.1 e).msgs from rfl]
  rw [shaMsgs, expectedBytes_eq, hm, emitAll_append, emitAll_append, emitAll_append, cnt_append, cnt_append,
    cnt_append]
  omega

end ZkFormal.Near.Render
