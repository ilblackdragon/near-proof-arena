import ZkFormal.NearV3.Assembly.RcptGasEffectivePhysical

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem gasEffective_commute (F : (ReceiptPlan→Coord→Nat→Fp)→ReceiptPlan→Coord→Nat→Fp)
    (hlocal : ∀a b p row col,a p row col=b p row col→F a p row col=F b p row col)
    (hfree : ∀a p row,row.state=sGP→F a p row pc=a p row pc)
    (ctx : ApplyCtx) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasEffectiveAux ctx (F fallback)=F (gasEffectiveAux ctx fallback) := by
  funext p row col
  by_cases hc : row.state=sGP ∧ col=pc
  · obtain ⟨hs,rfl⟩ := hc
    rw [hfree _ p row hs]
    simp only [gasEffectiveAux,hs,and_self,ite_true]
  · have he (a : ReceiptPlan→Coord→Nat→Fp) : gasEffectiveAux ctx a p row col=a p row col := by simp only [gasEffectiveAux,if_neg hc]
    rw [he]
    exact (hlocal _ _ p row col (he fallback)).symm

theorem gasEffective_digest_commute (ctx : ApplyCtx)  (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasEffectiveAux ctx (digestMetadata fallback)=digestMetadata (gasEffectiveAux ctx fallback) := by
  apply gasEffective_commute (digestMetadata)
  · intro a b p row col he
    simp only [digestMetadata,he]
  · intro a p row hs
    cases row with
    | mk state i len => dsimp only at hs;subst state;rfl

theorem gasEffective_character_commute (ctx : ApplyCtx)  (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasEffectiveAux ctx (characterAux fallback)=characterAux (gasEffectiveAux ctx fallback) := by
  apply gasEffective_commute (characterAux)
  · intro a b p row col he
    simp only [characterAux,he]
  · intro a p row hs
    cases row with
    | mk state i len => dsimp only at hs;subst state;rfl

theorem gasEffective_length_commute (ctx : ApplyCtx)  (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasEffectiveAux ctx (characterLengthAux fallback)=characterLengthAux (gasEffectiveAux ctx fallback) := by
  apply gasEffective_commute (characterLengthAux)
  · intro a b p row col he
    simp only [characterLengthAux,he]
  · intro a p row hs
    cases row with
    | mk state i len => dsimp only at hs;subst state;rfl

theorem gasEffective_predecessor_commute (ctx : ApplyCtx)  (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasEffectiveAux ctx (predecessorAux fallback)=predecessorAux (gasEffectiveAux ctx fallback) := by
  apply gasEffective_commute (predecessorAux)
  · intro a b p row col he
    simp only [predecessorAux,he]
  · intro a p row hs
    cases row with
    | mk state i len => dsimp only at hs;subst state;rfl

theorem gasEffective_named_commute (ctx : ApplyCtx)  (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasEffectiveAux ctx (namedAux fallback)=namedAux (gasEffectiveAux ctx fallback) := by
  apply gasEffective_commute (namedAux)
  · intro a b p row col he
    simp only [namedAux,he]
  · intro a p row hs
    cases row with
    | mk state i len => dsimp only at hs;subst state;rfl

theorem gasEffective_system_commute (ctx : ApplyCtx)  (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasEffectiveAux ctx (systemAux fallback)=systemAux (gasEffectiveAux ctx fallback) := by
  apply gasEffective_commute (systemAux)
  · intro a b p row col he
    simp only [systemAux,he]
  · intro a p row hs
    cases row with
    | mk state i len => dsimp only at hs;subst state;rfl

theorem gasEffective_routing_commute (ctx : ApplyCtx) (interval : ReceiptPlan→Option Bytes×Option Bytes) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasEffectiveAux ctx (routingAux interval fallback)=routingAux interval (gasEffectiveAux ctx fallback) := by
  apply gasEffective_commute (routingAux interval)
  · intro a b p row col he
    simp only [routingAux,he]
  · intro a p row hs
    cases row with
    | mk state i len => dsimp only at hs;subst state;rfl

theorem gasEffective_key_commute (ctx : ApplyCtx) (accountId : ReceiptPlan→Nat) (accessId : ReceiptPlan→Option Nat) (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasEffectiveAux ctx (keyAux accountId accessId fallback)=keyAux accountId accessId (gasEffectiveAux ctx fallback) := by
  apply gasEffective_commute (keyAux accountId accessId)
  · intro a b p row col he
    simp only [keyAux,he]
  · intro a p row hs
    cases row with
    | mk state i len => dsimp only at hs;subst state;rfl

theorem gasEffective_borrow_commute (ctx : ApplyCtx)  (fallback : ReceiptPlan→Coord→Nat→Fp) :
    gasEffectiveAux ctx (gasBorrowAux ctx fallback)=gasBorrowAux ctx (gasEffectiveAux ctx fallback) := by
  apply gasEffective_commute (gasBorrowAux ctx)
  · intro a b p row col he
    simp only [gasBorrowAux,he]
  · intro a p row hs
    cases row with
    | mk state i len => dsimp only at hs;subst state;rfl

theorem gasEffective_constants_identity (ctx : ApplyCtx)  (fallback : ReceiptPlan→Nat→Fp) :
    gasEffectiveConstants ctx (systemIdentityConstants fallback)=systemIdentityConstants (gasEffectiveConstants ctx fallback) := by
  funext p col
  by_cases hc : col=gq
  · subst col;rfl
  · simp only [gasEffectiveConstants,systemIdentityConstants,if_neg hc]

theorem gasEffective_constants_key (ctx : ApplyCtx) (accountId : ReceiptPlan→Nat) (fallback : ReceiptPlan→Nat→Fp) :
    gasEffectiveConstants ctx (keyConstants accountId fallback)=keyConstants accountId (gasEffectiveConstants ctx fallback) := by
  funext p col
  by_cases hc : col=gq
  · subst col;rfl
  · simp only [gasEffectiveConstants,keyConstants,if_neg hc]

theorem gasEffective_constants_routing (ctx : ApplyCtx) (k : WalkD0) (fallback : ReceiptPlan→Nat→Fp) :
    gasEffectiveConstants ctx (nativeRoutingConstants k fallback)=nativeRoutingConstants k (gasEffectiveConstants ctx fallback) := by
  funext p col
  by_cases hc : col=gq
  · subst col;rfl
  · simp only [gasEffectiveConstants,nativeRoutingConstants,if_neg hc]

end ZkFormal.NearV3.Assembly.RcptSkeleton
