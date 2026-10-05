import ZkFormal.Near.Render.Proof.MemChain
import ZkFormal.Near.Render.Proof.BusRids

/-!
# ZkFormal.Near.Render.Proof.BusMem — `MemBusStmt`

Every `MEM` message is `msgW k t i` (slot `k`, time `t`, lane `i`, amount
`amtAt k t`, the slot's locked/storage bytes); writes are at the pairs
`pairsW`, reads at `pairsR`, a permutation (`MemChain.pairs_perm`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra MemChain

namespace BusMem
variable (e : Ext)

def msgW (k t i : Nat) : ZkFormal.Near.Msg :=
  [k, t, i, (leBytes 16 (e.amtAt k t)).getD i 0, (leBytes 16 (e.acc0 k).locked).getD i 0,
    (leBytes 8 (e.acc0 k).storageUsage ++ List.replicate 8 0).getD i 0]

def msgsAt (p : Nat × Nat) : List ZkFormal.Near.Msg := (List.range 16).map (msgW e p.1 p.2)

variable {c : Claim}

theorem rcpt_sends (pub : List Fp) :
    rcptSends pub (rcptViewsOf (mkInfo c e)) B_MEM =
      ((List.range e.rs.length).map (fun r => (e.slot r, r + 1))).flatMap (msgsAt e) := by
  simp only [rcptSends, B_MEM, B_BYTES, B_KEYNIB, Nat.reduceEqDiff, if_false, if_true, rcptViewsOf, rcptData,
    List.map_map, List.length_map, List.length_range, zip_range_map, List.flatMap_map]
  apply flatMap_congr'; intro r _
  simp only [msgsAt, Function.comp_apply]
  apply List.map_congr_left; intro i _
  simp [rcptViewOf, rdOf, msgW, mkInfo_e, Ext.amtAt, Info.nRcpt]

theorem rcpt_recvs (pub : List Fp) :
    rcptRecvs pub (rcptViewsOf (mkInfo c e)) B_MEM =
      ((List.range e.rs.length).map (fun r => (e.slot r, lb e (e.slot r) r))).flatMap (msgsAt e) := by
  simp only [rcptRecvs, B_MEM, B_DIGEST, B_FINAL, Nat.reduceEqDiff, if_false, if_true, rcptViewsOf, rcptData,
    List.map_map, List.length_map, List.length_range, zip_range_map, List.flatMap_map]
  apply flatMap_congr'; intro r _
  simp only [msgsAt, Function.comp_apply]
  apply List.map_congr_left; intro i _
  simp [rcptViewOf, rdOf, msgW, mkInfo_e, Info.nRcpt, tprev_eq, ← amt_lb]

theorem leBytes_leNat (l : Bytes) {w : Nat} (h : l.length = w) : leBytes w (leNat l) = toNats l := by
  subst h; simp only [leBytes, Sound.leN_leNat]

/-- The decoded pre-state account of a touched slot, bytewise. -/
theorem acc0_bytes (hg : Good c e) {k : Nat} (hk : k ∈ (mkInfo c e).touched) (i : Nat) (hi : i < 16) :
    (leBytes 16 (e.acc0 k).amount).getD i 0 = (toNats (e.vals0 k)).getD i 0 ∧
    (leBytes 16 (e.acc0 k).locked).getD i 0 = (toNats (e.vals0 k)).getD (16 + i) 0 ∧
    (leBytes 8 (e.acc0 k).storageUsage ++ List.replicate 8 0).getD i 0 =
      (if i < 8 then (toNats (e.vals0 k)).getD (64 + i) 0 else 0) := by
  obtain ⟨nr, h1, h2⟩ := mem_touched.1 hk
  have hl := hg.vals_len k nr h1 h2
  have hv := hg.vals_v1 k nr h1 h2
  rcases hd : Account.decode (e.vals0 k) with _ | a
  · simp [hd] at hv
  · have ha : e.acc0 k = a := by simp [Ext.acc0, hd]
    simp only [Account.decode, hl, if_true] at hd
    split at hd
    · simp at hd
    · simp only [Option.some.injEq] at hd
      rw [ha, ← hd]
      have l1 : ((e.vals0 k).take 16).length = 16 := by simp [hl]
      have l2 : (((e.vals0 k).drop 16).take 16).length = 16 := by simp [hl]
      have l3 : ((e.vals0 k).drop 64).length = 8 := by simp [hl]
      simp only
      rw [leBytes_leNat _ l1, leBytes_leNat _ l2, leBytes_leNat _ l3]
      refine ⟨?_, ?_, ?_⟩
      · simp [toNats, List.getD_eq_getElem?_getD, List.getElem?_take, hi]
      · simp [toNats, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, hi, Nat.add_comm]
      · by_cases h8 : i < 8
        · simp only [h8, if_true]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [leBytes, toNats, leN_length]; omega)]
          simp [toNats, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]
        · simp only [h8, if_false]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [leBytes, toNats, leN_length]; omega)]
          rw [List.getElem?_replicate]; split <;> rfl

theorem acct_sends (hg : Good c e) :
    acctSends (acctViewsOf (mkInfo c e)) B_MEM =
      ((mkInfo c e).touched.map (fun k => (k, 0))).flatMap (msgsAt e) := by
  simp only [acctSends, B_MEM, B_BYTES, Nat.reduceEqDiff, if_false, if_true, acctViewsOf, List.flatMap_map]
  apply flatMap_congr'; intro k hk
  simp only [msgsAt]
  apply List.map_congr_left; intro i hi
  have hi' := List.mem_range.1 hi
  obtain ⟨h1, h2, h3⟩ := acc0_bytes e hg hk i hi'
  simp only [acctLane, vpre_eq hk, msgW, Ext.amtAt, List.cons_append, List.nil_append, h1, h2, h3]

theorem acct_recvs (hg : Good c e) :
    acctRecvs (acctViewsOf (mkInfo c e)) B_MEM =
      ((mkInfo c e).touched.map (fun k => (k, lb e k e.rs.length))).flatMap (msgsAt e) := by
  simp only [acctRecvs, B_MEM, if_true, acctViewsOf, List.flatMap_map]
  apply flatMap_congr'; intro k hk
  simp only [msgsAt]
  apply List.map_congr_left; intro i hi
  have hi' := List.mem_range.1 hi
  obtain ⟨_, h2, h3⟩ := acc0_bytes e hg hk i hi'
  simp only [acctLane, vpre_eq hk, vpost_eq hk, msgW, List.cons_append, List.nil_append, h2, h3, mkInfo_e,
    tlast_eq, ← amt_lb]
  simp only [Ext.valsAt, Account.encode, u128, toNats, leBytes, List.getD_eq_getElem?_getD, List.getElem?_take, hi',
    if_true, List.map_append, List.append_assoc]
  rw [List.getElem?_append_left (by simp [leN_length]; exact hi')]

end BusMem

open BusMem in
/-- **`MemBusStmt`.** -/
theorem memBus : MemBusStmt := by
  intro c e hg _ m
  rw [hcount_eq, hcount_eq]
  simp only [sel, if_true, Bool.false_eq_true, if_false, shaTraffic, nodeTraffic, nodeSends, nodeRecvs,
    walkTraffic, walkSends, walkRecvs, mrkTraffic, mrkSends, mrkRecvs, sortTraffic, B_VSLOT, B_DIGEST,
    B_BYTES, B_PARENT, B_EDGE, B_KEYNIB, B_FINAL, B_MEM, B_RIDS, B_MPOS, Nat.reduceEqDiff, cnt_nil,
    Nat.zero_add, Nat.add_zero, bundle_info, rcptTraffic, acctTraffic]
  rw [show (7 : Nat) = B_MEM from rfl, rcpt_sends, rcpt_recvs, acct_sends e hg, acct_recvs e hg]
  simp only [cnt, ← List.count_append, ← List.map_append, ← List.flatMap_append]
  exact ((pairs_perm e touched_nodup (fun r hr => slot_mem hg hr)).flatMap_right _ |>.map Msg.toFp).count_eq m

end ZkFormal.Near.Render
