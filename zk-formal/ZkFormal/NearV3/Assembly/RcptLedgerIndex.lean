import ZkFormal.NearV3.Assembly.RcptHeaderTokens

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3

/-- Native prefix sum used by global receipt and list-header indices. -/
def prefixBurn (ctx : ApplyCtx) (rs : List Receipt) (before i : Nat) : Nat :=
  before+((rs.take i).map (nativeBurn ctx)).sum

theorem tokenLedger_get (ctx : ApplyCtx) (rs : List Receipt) (before i : Nat)
    (r : Receipt) (hr : rs[i]?=some r) :
    (tokenLedger ctx before rs)[i]?=
      some ⟨prefixBurn ctx rs before i,nativeBurn ctx r⟩ := by
  induction rs generalizing before i with
  | nil => simp at hr
  | cons r' rs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hr
      subst r'
      simp [tokenLedger,prefixBurn]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hr
      simpa [tokenLedger,prefixBurn,List.take_succ_cons,Nat.add_assoc] using
        ih (before+nativeBurn ctx r') i hr

theorem prefixBurn_succ (ctx : ApplyCtx) (rs : List Receipt) (before i : Nat)
    (r : Receipt) (hr : rs[i]?=some r) :
    prefixBurn ctx rs before (i+1)=prefixBurn ctx rs before i+nativeBurn ctx r := by
  induction rs generalizing before i with
  | nil => simp at hr
  | cons r' rs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hr
      subst r'
      simp [prefixBurn]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hr
      simpa [prefixBurn,List.take_succ_cons,Nat.add_assoc] using
        ih (before+nativeBurn ctx r') i hr

/-- Adjacent entries of the actual executable ledger have equal boundary bytes. -/
theorem tokenLedger_adjacent (ctx : ApplyCtx) (rs : List Receipt) (before i : Nat)
    (r s : Receipt) (hr : rs[i]?=some r) (hs : rs[i+1]?=some s) :
    ∃ x y, (tokenLedger ctx before rs)[i]?=some x ∧
      (tokenLedger ctx before rs)[i+1]?=some y ∧ x.newBytes=y.oldBytes := by
  refine ⟨_,_,tokenLedger_get ctx rs before i r hr,tokenLedger_get ctx rs before (i+1) s hs,?_⟩
  simp only [TokenInput.newBytes,TokenInput.oldBytes]
  rw [prefixBurn_succ ctx rs before i r hr]

/-- Generated receipt indices identify the actual input, not just a range with
an unrelated ordering. -/
theorem planReceipts_index_input (xs : List Input) (j nj r cj o o2 : Nat) (ll : Bool)
    (p : ReceiptPlan) (hp : p∈planReceipts j nj r cj o o2 ll xs) :
    ∃ i, xs[i]?=some p.input ∧ p.receiptIndex=r+i := by
  induction xs generalizing r cj o o2 with
  | nil => simp [planReceipts] at hp
  | cons x xs ih =>
    simp only [planReceipts,List.mem_cons] at hp
    rcases hp with he|hp
    · subst p
      exact ⟨0,rfl,by simp⟩
    · obtain ⟨i,hi,he⟩ := ih (r+1) (cj+1) (o+rcLength x) (o2+refundLength x) hp
      exact ⟨i+1,by simpa using hi,by omega⟩

end ZkFormal.NearV3.Assembly.RcptSkeleton
