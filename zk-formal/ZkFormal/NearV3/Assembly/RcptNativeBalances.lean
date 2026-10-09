import ZkFormal.NearV3.Assembly.RcptAccountRead

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 NearSpec.TransferV1

/-- Native account facts needed by the bytewise deposit renderer, independently
of the still-open global account version/provider allocation. -/
structure NativeBalanceData (st : Acc) (r : Receipt) (a : Account) : Prop where
  raw : ∃bs,st.trie.get (accountKeyPath r.receiverId)=some bs ∧ Account.decode bs=some a
  amount : a.amount+r.deposit<Params.u128Max
  total : a.amount+r.deposit+a.locked<Params.two128
  stake : Params.storageAmountPerByte*a.storageUsage≤a.amount+r.deposit+a.locked ∨
    a.storageUsage≤Params.zeroBalanceStorageLimit

private theorem stake_bool {A B : Prop} [Decidable A] [Decidable B]
    (h : ¬(!(decide A || decide B))=true) : A∨B := by
  by_cases ha : A
  · exact Or.inl ha
  · by_cases hb : B
    · exact Or.inr hb
    · simp only [ha,hb,decide_false,Bool.false_or,Bool.not_false,not_true_eq_false] at h

theorem applySystemReceipt_balance_data (st out : Acc) (r : Receipt)
    (h : applySystemReceipt st r=.ok out) : ∃a,NativeBalanceData st r a := by
  unfold applySystemReceipt at h
  repeat (any_goals first
    | contradiction
    | ((try dsimp only at h);(try simp only [bind,Except.bind,pure,Except.pure] at h);split at h))
  all_goals
    refine ⟨_,⟨⟨_,?_,by assumption⟩,?_,?_,?_⟩⟩
    · rw [native_get_find,show st.trie.find (accountKeyPath r.receiverId)=some (some _) from by assumption]
      rfl
    · omega
    · omega
    · exact stake_bool (by assumption)


theorem applyReceipt_balance_data (ctx : Ctx) (st out : Acc) (r : Receipt)
    (h : applyReceipt ctx st r=some out) : ∃a,NativeBalanceData st r a := by
  unfold applyReceipt at h
  repeat (any_goals first
    | contradiction
    | ((try dsimp only at h);split at h))
  all_goals
    refine ⟨_,⟨⟨_,?_,by assumption⟩,?_,?_,?_⟩⟩
    · assumption
    · omega
    · omega
    · exact stake_bool (by assumption)

/-- Executable deposit input: the account read at the actual incoming state. -/
def nativeBalanceAccount (st : Acc) (r : Receipt) : Option Account :=
  (st.trie.get (accountKeyPath r.receiverId)).bind Account.decode

theorem nativeBalanceAccount_of_data {st : Acc} {r : Receipt} {a : Account}
    (h : NativeBalanceData st r a) : nativeBalanceAccount st r=some a := by
  obtain ⟨bs,hread,hdecode⟩ := h.raw
  simp only [nativeBalanceAccount,hread,Option.bind_some,hdecode]

theorem nativeBalanceData_byte_bounds {st : Acc} {r : Receipt} {a : Account}
    (h : NativeBalanceData st r a) :
    a.amount+r.deposit+1<256^16 ∧ a.amount+r.deposit+a.locked<256^16 := by
  have hm := h.amount
  have ht := h.total
  simp only [Params.u128Max,Params.two128] at hm ht
  constructor <;> omega

end ZkFormal.NearV3.Assembly.RcptSkeleton
