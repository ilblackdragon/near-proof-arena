import ZkFormal.NearV3.Assembly.RcptTokenLedger

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 NearSpec.TransferV1

private theorem except_bind_ok {α β : Type} {a : Except String α}
    {f : α → Except String β} {b : β} (h : a.bind f = .ok b) :
    ∃ x, a = .ok x ∧ f x = .ok b := by
  cases a <;> simp_all [Except.bind]

/-- Successful native main execution starts its receipt ledger at zero; no
initial-token or intermediate-overflow premise is added to the accepted domain. -/
theorem applyNewChunk_token_ledger (prims : Prims) (ctx : ApplyCtx) (t : PTrie)
    (rs : List Receipt) (out : MainOut) (h : applyNewChunk prims ctx t rs = .ok out) :
    out.tokensBurnt = (rs.map (nativeBurn ctx)).sum ∧
    out.tokensBurnt < Params.two128 ∧
    ∀ x ∈ tokenLedger ctx 0 rs,
      x.before < Params.two128 ∧ x.before+x.burnt < Params.two128 := by
  unfold applyNewChunk at h
  obtain ⟨_,_,h⟩ := except_bind_ok h
  obtain ⟨_,_,h⟩ := except_bind_ok h
  obtain ⟨⟨mid,so⟩,_,h⟩ := except_bind_ok h
  dsimp only at h
  obtain ⟨_,_,h⟩ := except_bind_ok h
  obtain ⟨_,_,h⟩ := except_bind_ok h
  obtain ⟨_,_,h⟩ := except_bind_ok h
  obtain ⟨⟨acc,ls⟩,ha,h⟩ := except_bind_ok h
  dsimp only at h
  obtain ⟨_,_,h⟩ := except_bind_ok h
  obtain ⟨_,_,h⟩ := except_bind_ok h
  simp only [pure,Except.pure,Except.ok.injEq] at h
  subst out
  have hh := applyReceipts_token_ledger ctx rs 0 _ (acc,ls) (by change 0 < Params.two128; decide) ha
  simpa using hh

end ZkFormal.NearV3.Assembly.RcptSkeleton
