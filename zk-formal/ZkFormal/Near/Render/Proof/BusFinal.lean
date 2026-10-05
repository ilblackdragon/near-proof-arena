import ZkFormal.Near.Render.Proof.WalkTraffic
import ZkFormal.Near.Render.Proof.BusRids

/-!
# ZkFormal.Near.Render.Proof.BusFinal — `FinalBusStmt`, `KeynibBusStmt`

`walk` sends `FINAL (r, slot)` at the end of walk `r` and receives the key
symbols `KEYNIB (r, t, sym, last)`; `rcpt` receives `FINAL (r, kslot)` and
sends the symbols of `0 ‖ receiver` and `END`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

theorem getD_last_cons {α : Type} (d a : α) (rest : List α) (h : rest ≠ []) :
    (a :: rest).getD ((a :: rest).length - 1) d = (rest.getLast?).getD d := by
  rw [List.getLast?_eq_getElem?]
  cases rest with
  | nil => exact absurd rfl h
  | cons b l => simp [List.getD_eq_getElem?_getD]

section
variable {c : Claim} {e : Ext} (hg : Good c e)
include hg

theorem final_step {r : Nat} (hr : r < e.rs.length) :
    (((walksOf (mkInfo c e)).getD r []).getD (((walksOf (mkInfo c e)).getD r []).length - 1) default).edge.getD 3 0
      = e.slot r := by
  obtain ⟨rest, h1, _, h3⟩ := walk_of_index hg hr
  rw [h1]
  have hne : rest ≠ [] := by rintro rfl; simp at h3
  rw [getD_last_cons _ _ _ hne]
  cases h : rest.getLast? with
  | none => rw [h] at h3; cases h3
  | some s => rw [h] at h3; simp at h3; simpa using h3

end

/-- **`FinalBusStmt`.** -/
theorem finalBus : FinalBusStmt := by
  intro c e hg _ m
  rw [hcount_eq, hcount_eq]
  have hw : (bundle c.1 e).walks = walksOf (mkInfo c.1 e) := rfl
  simp only [sel, if_true, Bool.false_eq_true, if_false, shaTraffic, nodeTraffic, nodeSends, nodeRecvs,
    walkTraffic, walkRecvs, walkSends, rcptTraffic, rcptSends, rcptRecvs, acctTraffic, acctSends, acctRecvs,
    mrkTraffic, mrkSends, mrkRecvs, sortTraffic, B_VSLOT, B_DIGEST, B_BYTES, B_PARENT, B_EDGE, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_FINAL, Nat.reduceEqDiff, cnt_nil, Nat.zero_add, Nat.add_zero, bundle_info, hw]
  congr 1
  simp only [walkViewsOf, List.map_map, rcptViewsOf, rcptData, List.length_map, List.length_range,
    zip_range_map, walksOf_len hg, Info.nRcpt, mkInfo_e]
  apply List.map_congr_left; intro r hr
  have hr' := List.mem_range.1 hr
  simp only [Function.comp_apply, WalkV.edge, List.length_map, List.length_range]
  have hL : 2 ≤ ((walksOf (mkInfo c.1 e)).getD r []).length := (walkIdx hg hr').len
  rw [steps_getD (by omega)]
  simp only [final_step hg hr', rcptViewOf, rdOf, mkInfo_e]

end ZkFormal.Near.Render

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

theorem nibbles_eq : ∀ (b : Bytes), nibbles b = (toNats b).flatMap fun ch => [ch / 16, ch % 16]
  | [] => rfl
  | x :: b => by simp [nibbles, toNats, nibbles_eq b]

theorem rcpt_keySyms (I : Info) (r : Nat) : (rcptViewOf (rdOf I r)).keySyms = keySyms (I.e.rc r) := by
  simp [RcptV.keySyms, rcptViewOf, rdOf, keySyms, accountKeyPath, nibbles, nibbles_eq]

/-- **`KeynibBusStmt`.** -/
theorem keynibBus : KeynibBusStmt := by
  intro c e hg _ m
  rw [hcount_eq, hcount_eq]
  have hw : (bundle c.1 e).walks = walksOf (mkInfo c.1 e) := rfl
  simp only [sel, if_true, Bool.false_eq_true, if_false, shaTraffic, nodeTraffic, nodeSends, nodeRecvs,
    walkTraffic, walkRecvs, walkSends, rcptTraffic, rcptSends, rcptRecvs, acctTraffic, acctSends, acctRecvs,
    mrkTraffic, mrkSends, mrkRecvs, sortTraffic, B_VSLOT, B_DIGEST, B_BYTES, B_PARENT, B_EDGE, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_FINAL, Nat.reduceEqDiff, cnt_nil, Nat.zero_add, Nat.add_zero, bundle_info, hw]
  congr 1
  simp only [walkViewsOf, List.flatMap_map, rcptViewsOf, rcptData, List.length_map, List.length_range,
    zip_range_map, walksOf_len hg, Info.nRcpt, mkInfo_e, List.map_map]
  apply flatMap_congr'; intro r hr
  have hr' := List.mem_range.1 hr
  obtain ⟨rest, h1, h2, _⟩ := walk_of_index hg hr'
  obtain ⟨kd, _⟩ := keySyms_facts hg (e.rc r)
  obtain ⟨l1, _, _, _, _, l6⟩ := walkFrom_shape _ _ _ _ h2 kd
  have hidx := walkIdx hg hr'
  simp only [Function.comp_apply, WalkV.edge, List.length_map, List.length_range, rcpt_keySyms, mkInfo_e]
  rw [h1] at hidx ⊢
  simp only [List.length_cons, l1, Nat.add_sub_cancel]
  apply List.map_congr_left; intro t ht
  have ht' := List.mem_range.1 ht
  rw [steps_getD (by simp [l1]; omega)]
  have hok := hidx.ok (t + 1) (by simp [l1]; omega)
  simp only [List.getD_cons_succ] at hok ⊢
  rw [WalkTraffic.edge2 hok]
  have : rest.getD t default = rest[t]'(by omega) := by simp [List.getD_eq_getElem?_getD, l1, ht']
  rw [this, (l6 t (by omega)).2.1]
  simp only [List.cons.injEq, true_and, and_true]
  split <;> split <;> first | rfl | omega

end ZkFormal.Near.Render
