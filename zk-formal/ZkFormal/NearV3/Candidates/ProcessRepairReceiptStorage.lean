import ZkFormal.NearV3.Candidates.ProcessRepairMemoryLanes
namespace ZkFormal.NearV3.Candidates.ProcessRepairReceiptStorage
set_option maxRecDepth 32768
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Link NearSpec

theorem storage_bound {pub:List Fp} {rs:RcptVs} {as:List AcctV}
    (h:ProcessRepairReceiptMemoryOrder.Context pub rs as)
    (initial:∀a∈as,Bytes8 a.pre)
    (after:∀r,(hr:r<rs.length)→Bytes8 rs[r].aft)
    {r:Nat} (hr:r<rs.length) (hlen:rs[r].st.length=16):
    Bytes8 rs[r].st ∧ leN' rs[r].st<2^64 ∧
      Params.storageAmountPerByte*leN' rs[r].st<Params.two128:=by
  obtain ⟨a,ha,hk⟩:=ProcessRepairMemoryLanes.slot_acct h r hr
  have lanes:=ProcessRepairMemoryLanes.lanes h initial after r hr a ha hk
  have hb:Bytes8 rs[r].st:=by
    apply bytes8_of_getD hlen
    intro i hi
    rw [(lanes i hi).2.1]
    split
    · exact getD_lt_of_bytes8 (initial a ha) _
    · decide
  have hu:leN' rs[r].st<2^64:=by
    apply leN'_lt64 hlen hb
    intro i hi hi'
    rw [(lanes i hi').2.1,if_neg (by omega)]
  refine ⟨hb,hu,?_⟩
  have hh:=Nat.mul_lt_mul_of_pos_left hu (show 0<Params.storageAmountPerByte by decide)
  have hn:Params.storageAmountPerByte*2^64≤Params.two128:=by decide +kernel
  exact Nat.lt_of_lt_of_le hh hn

theorem native_check {pub:List Fp} {rs:RcptVs} {as:List AcctV}
    (h:ProcessRepairReceiptMemoryOrder.Context pub rs as)
    (initial:∀a∈as,Bytes8 a.pre)
    (after:∀r,(hr:r<rs.length)→Bytes8 rs[r].aft)
    {r:Nat} (hr:r<rs.length) (hlen:rs[r].st.length=16)
    (hc:(Params.storageAmountPerByte*leN' rs[r].st)%Params.two128≤leN' rs[r].aft+leN' rs[r].lk ∨
      leN' rs[r].st≤Params.zeroBalanceStorageLimit):
    Params.storageAmountPerByte*leN' rs[r].st≤leN' rs[r].aft+leN' rs[r].lk ∨
      leN' rs[r].st≤Params.zeroBalanceStorageLimit:=by
  have hb:=(storage_bound h initial after hr hlen).2.2
  rwa [Nat.mod_eq_of_lt hb] at hc
end ZkFormal.NearV3.Candidates.ProcessRepairReceiptStorage
