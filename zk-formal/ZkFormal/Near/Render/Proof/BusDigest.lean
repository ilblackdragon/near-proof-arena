import ZkFormal.Near.Render.Proof.DigMrk2
import ZkFormal.Near.Render.Proof.BusBytes

/-!
# ZkFormal.Near.Render.Proof.BusDigest — `DigestBusStmt`

The SHA table provides the digest `[id, len, sha256 bytes]` of every message
of the bundle once (`Sha.Gen.expectedDigests`, every `dmult` set).  Every
message id (`kind + 16·idx`) is received exactly once:

* node (`node_digest`): `NPRE/NPOST` of the root (against the claim's state
  roots) and of every revealed child (each non-root node has one parent),
  `VPRE/VPOST` of every touched slot — the `node` and `acct` messages;
* mrk (`mrk_digest`): the `LEAF` and `MRK` messages (root against the claim's
  outcome root);
* rcpt (`rcpt_digest`): `RC`, `RF` (against the claim's commitments), `PEO(r)`
  and, for refunds, `RID(r)`.

So no per-message `dmult` is needed: identical contents under different ids
are different messages.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

namespace BusDigest

/-- The rcpt messages whose digests `rcpt` receives (all but `LEAF`). -/
def rcptOwn (I : Info) : List Render.Msg :=
  [⟨msgId K_RC 0, rcBytes I⟩, ⟨msgId K_RF 0, rfBytes I⟩] ++
  (List.range I.nRcpt).flatMap fun r =>
    (if hasRefund I r then [⟨msgId K_RID r, ridBytes I r⟩] else []) ++ [⟨msgId K_PEO r, peoBytes I r⟩]

theorem perm_flatMap_congr {α β : Type} {F G : α → List β} (h : ∀ x, (F x).Perm (G x)) :
    ∀ l : List α, (l.flatMap F).Perm (l.flatMap G)
  | [] => List.Perm.refl _
  | x :: l => by
    simp only [List.flatMap_cons]
    exact (h x).append (perm_flatMap_congr h l)

theorem rcptMsgs_perm (I : Info) : (rcptMsgs I).Perm (rcptOwn I ++ leafMsgs I) := by
  simp only [rcptMsgs, rcptOwn, leafMsgs, List.append_assoc]
  refine List.Perm.append_left _ ?_
  rw [List.map_eq_flatMap]
  refine List.Perm.trans ?_ (perm_flatMap_append _ _ _)
  apply perm_flatMap_congr
  intro r
  cases hasRefund I r
  · exact List.perm_append_comm
  · simp only [↓reduceIte]
    exact List.perm_append_comm

section
variable {c : WfClaim} {e : Ext} (hg : Good c.1 e)
include hg

theorem rid_len (r : Nat) (hr : r < e.rs.length) : (ridBytes (mkInfo c.1 e) r).length = 48 := by
  have h := RcptP.d_id hg (r := r) hr
  rw [RcptP.Df_eq hr] at h
  simp only [rdOf] at h
  simp only [ridBytes, List.length_append, NodeInfo.leBytes_len, h]

/-- **The rcpt receives on `DIGEST`.** -/
theorem rcpt_digest :
    rcptRecvs (pubOf c.1) (rcptViewsOf (mkInfo c.1 e)) B_DIGEST = (rcptOwn (mkInfo c.1 e)).map digestMsg := by
  have hh : Link.Hdr c := ⟨hg.pv, hg.chain⟩
  have hp : pubOf c.1 = publicOf c := rfl
  have hN : (rcptViewsOf (mkInfo c.1 e)).length = e.rs.length := by rw [views_eq]; simp
  have hRC : digMsg K_RC (rcOffs (rcptViewsOf (mkInfo c.1 e)) (rcptViewsOf (mkInfo c.1 e)).length)
      (pubBytes (pubOf c.1) PV_RC 32) = digestMsg ⟨msgId K_RC 0, rcBytes (mkInfo c.1 e)⟩ := by
    have h1 : rcOffs (rcptViewsOf (mkInfo c.1 e)) (rcptViewsOf (mkInfo c.1 e)).length = (rcBytes (mkInfo c.1 e)).length := by
      rw [hN, rcOffs_eq _ (Nat.le_refl _), rc_split hg]
      simp [offs, pubBytes, List.length_flatMap]
      omega
    have h2 : pubBytes (pubOf c.1) PV_RC 32 = shaN (rcBytes (mkInfo c.1 e)) := by
      rw [hp, Link.pub_rc hh]
      show (c.1.receiptsCommitment).map UInt8.toNat = toNats (sha256 (ofNats (toNats _)))
      rw [NodeInfo.ofNats_toNats, ← hg.rcCommit]
      rfl
    rw [h1, h2]; rfl
  have hRF : digMsg K_RF (rfOffs (rcptViewsOf (mkInfo c.1 e)) (rcptViewsOf (mkInfo c.1 e)).length)
      (pubBytes (pubOf c.1) PV_RFC 32) = digestMsg ⟨msgId K_RF 0, rfBytes (mkInfo c.1 e)⟩ := by
    have h1 : rfOffs (rcptViewsOf (mkInfo c.1 e)) (rcptViewsOf (mkInfo c.1 e)).length = (rfBytes (mkInfo c.1 e)).length := by
      rw [hN, rfOffs_eq _ (Nat.le_refl _), rf_split hg]
      simp only [offs, pubBytes, List.length_append, List.length_map, List.length_range, List.length_flatMap]
    have h2 : pubBytes (pubOf c.1) PV_RFC 32 = shaN (rfBytes (mkInfo c.1 e)) := by
      rw [hp, Link.pub_rfc hh]
      show (c.1.refundsCommitment).map UInt8.toNat = toNats (sha256 (ofNats (toNats _)))
      rw [NodeInfo.ofNats_toNats, ← hg.rfCommit]
      rfl
    rw [h1, h2]; rfl
  simp only [rcptRecvs, B_DIGEST, ↓reduceIte]
  rw [hRC, hRF]
  simp only [rcptOwn, List.map_cons, List.cons_append, List.nil_append,
    List.cons.injEq, true_and]
  rw [views_eq]
  simp only [List.length_map, List.length_range, zip_range_map, List.flatMap_map, List.map_flatMap]
  apply flatMap_congr'
  intro r hr
  have hr' : r < e.rs.length := List.mem_range.1 hr
  have hpeo := peo_eq hg hr'
  simp only [xv] at hpeo ⊢
  rw [hpeo]
  cases hrf : hasRefund (mkInfo c.1 e) r
  · simp only [rcptViewOf, rdOf, hrf, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.map_cons,
      List.map_nil, digMsg, digestMsg]
  · simp only [rcptViewOf, rdOf, hrf, ↓reduceIte, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, digMsg, digestMsg, rid_len hg r hr']

end

theorem expectedDigests_eq (ms : List Render.Msg) :
    Sha.Gen.expectedDigests (ms.map fun m => ⟨m.id, m.bytes, true⟩) = ms.map digestMsg := by
  unfold Sha.Gen.expectedDigests
  rw [List.filter_map, List.filter_eq_self.2 (by simp), List.map_map]
  rfl

end BusDigest

open BusDigest in
/-- **`DigestBusStmt`.** -/
theorem digestBus : DigestBusStmt := by
  intro c e hg hs m
  rw [hcount_eq, hcount_eq]
  have hN := node_digest hg hs.keys (edgeUses (bundle c.1 e).walks)
  have hM := mrk_digest hg
  have hR := rcpt_digest hg
  have hm : (bundle c.1 e).msgs = nodeMsgs (mkInfo c.1 e) ++ acctMsgs (mkInfo c.1 e) ++
      mrkMsgs (mkInfo c.1 e) ++ rcptMsgs (mkInfo c.1 e) := rfl
  simp only [sel, ↓reduceIte, Bool.false_eq_true, nodeTraffic, rcptTraffic, mrkTraffic, bundle_info]
  rw [cnt_perm hN, cnt_perm hM, hR]
  simp only [shaTraffic, nodeSends, walkTraffic, walkSends, walkRecvs, rcptSends, acctTraffic, acctSends,
    acctRecvs, mrkSends, sortTraffic, B_VSLOT, B_DIGEST, B_BYTES, B_PARENT, B_EDGE, B_KEYNIB, B_FINAL, B_MEM,
    B_RIDS, B_MPOS, Nat.reduceEqDiff, ↓reduceIte, cnt_nil, Nat.zero_add, Nat.add_zero]
  rw [expectedDigests_eq, hm]
  simp only [List.map_append, cnt_append]
  rw [cnt_perm ((rcptMsgs_perm _).map digestMsg)]
  simp only [List.map_append, cnt_append]
  omega

end ZkFormal.Near.Render
