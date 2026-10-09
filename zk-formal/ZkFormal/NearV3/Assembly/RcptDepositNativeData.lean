import ZkFormal.NearV3.Assembly.RcptNativeBalances
import ZkFormal.Near.Render.Proof.RcptDepF

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Algebra ZkFormal.Near.Render RcptGen

/-- Numeric deposit data has no receipt-index restriction. Version ownership is
tracked separately from these byte arithmetic facts. -/
structure DepositArithmeticOk (d : RD) : Prop where
  aft_lt : d.bef+d.dep+1<256^16
  tot_lt : d.bef+d.dep+d.locked<256^16
  stor_lt : d.stor<256^8
  big : d.big=decide (10000000000000000000*d.stor≤d.bef+d.dep+d.locked)
  stake : d.big=false→d.stor≤770

/-- A scalar arithmetic record only; zero-filled unrelated fields do not claim
to be a physical receipt or its authenticated version metadata. -/
def nativeDepositData (a : Account) (r : Receipt) : RD :=
  { (default : RD) with
    bef := a.amount
    dep := r.deposit
    locked := a.locked
    stor := a.storageUsage
    big := decide (Params.storageAmountPerByte*a.storageUsage≤a.amount+r.deposit+a.locked) }

theorem deposit_leNat_bound : ∀bs : Bytes,leNat bs<256^bs.length
  | [] => by simp [leNat]
  | b::bs => by
    have hh := deposit_leNat_bound bs
    have hb := b.toNat_lt
    simp only [leNat,List.length_cons,Nat.pow_succ]
    omega

theorem decoded_account_storage_bound (bs : Bytes) (a : Account)
    (h : Account.decode bs=some a) : a.storageUsage<256^8 := by
  unfold Account.decode at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst a
      have hh := deposit_leNat_bound (bs.drop 64)
      simp only [List.length_drop,show bs.length=72 from by assumption] at hh
      exact hh
  · cases h

theorem nativeBalanceData_arithmetic {st : NearSpec.TransferV1.Acc} {r : Receipt} {a : Account}
    (h : NativeBalanceData st r a) : DepositArithmeticOk (nativeDepositData a r) := by
  have hb := nativeBalanceData_byte_bounds h
  obtain ⟨bs,_,hd⟩ := h.raw
  refine ⟨hb.1,hb.2,decoded_account_storage_bound bs a hd,rfl,?_⟩
  intro hg
  change decide (Params.storageAmountPerByte*a.storageUsage≤a.amount+r.deposit+a.locked)=false at hg
  have hn := of_decide_eq_false hg
  have hs := h.stake
  rcases hs with hs|hs
  · contradiction
  · exact hs

end ZkFormal.NearV3.Assembly.RcptSkeleton
