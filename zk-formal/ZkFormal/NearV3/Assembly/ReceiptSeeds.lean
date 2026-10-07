import ZkFormal.NearV3.Assembly.Witness
import ZkFormal.Near.Link.EncLemmas

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Near

/-- Exact receipt payload, with execution/refund/routing metadata left as seeds.
This definition asserts neither receipt-table validity nor receipt execution. -/
def receiptSeed (r : Receipt) : RcptE :=
  { (default : RcptE) with
    p := r.predecessorId.map UInt8.toNat,
    v := r.receiverId.map UInt8.toNat, s := r.signerId.map UInt8.toNat,
    rid := r.receiptId.map UInt8.toNat, kt := r.signerPk.tag,
    pk := r.signerPk.data.map UInt8.toNat,
    gp := (u128 r.gasPrice).map UInt8.toNat,
    dep := (u128 r.deposit).map UInt8.toNat }

theorem receiptSeed_toReceipt (r : Receipt)
    (hg : r.gasPrice < 256^16) (hd : r.deposit < 256^16) :
    (receiptSeed r).toRcptV.toReceipt = r := by
  have hbytes (b : Bytes) : toBytes (b.map UInt8.toNat) = b := by
    simp [toBytes, List.map_map, Function.comp_def]
  have hnum (n : Nat) (h : n < 256^16) : leN' ((u128 n).map UInt8.toNat) = n := by
    rw [Link.leN'_eq, hbytes]
    exact leNat_leN 16 n h
  cases r
  simp only [receiptSeed, RcptV.toReceipt, hbytes, hnum _ hg, hnum _ hd]

theorem receiptSeed_toReceipt_of_wf {r : Receipt} (h : r.wf = true) :
    (receiptSeed r).toRcptV.toReceipt = r := by
  simp only [Receipt.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  apply receiptSeed_toReceipt
  · exact h.1.2
  · exact h.2

/-- One semantic list; table header width/count bounds remain separate. -/
def receiptListSeed (rs : List Receipt) : ListV3 :=
  {n0 := rs.length % 256, n1 := rs.length / 256, rs := rs.map receiptSeed}

theorem receiptListSeed_receipts {rs : List Receipt}
    (h : ∀ r ∈ rs, r.wf = true) :
    (receiptListSeed rs).rs.map (fun r => r.toRcptV.toReceipt) = rs := by
  simp only [receiptListSeed, List.map_map]
  conv => rhs; rw [← List.map_id rs]
  apply List.map_congr_left
  intro r hr
  exact receiptSeed_toReceipt_of_wf (h r hr)

end ZkFormal.NearV3.Assembly
