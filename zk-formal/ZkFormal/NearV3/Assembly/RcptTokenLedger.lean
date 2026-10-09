import ZkFormal.NearV3.Assembly.RcptNativeTokens

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 NearSpec.TransferV1

/-- System refunds preserve the running native burn total. -/
theorem applySystemReceipt_tokens (st out : Acc) (r : Receipt)
    (h : applySystemReceipt st r = .ok out) : out.tokensBurnt = st.tokensBurnt := by
  unfold applySystemReceipt at h
  repeat (any_goals first
    | contradiction
    | ((try dsimp only at h); (try simp only [bind,Except.bind,pure,Except.pure] at h); split at h)
    | (simp only [Except.ok.injEq] at h; subst out; rfl))

/-- Burn amount in the two actual incoming-receipt branches. -/
def nativeBurn (ctx : ApplyCtx) (r : Receipt) : Nat :=
  if r.predecessorId == AccountId.system then 0
  else Params.G * min r.gasPrice ctx.gasPrice

/-- Executable ordered token windows, one per receipt (including system receipts). -/
def tokenLedger (ctx : ApplyCtx) : Nat → List Receipt → List TokenInput
  | _, [] => []
  | before, r :: rs =>
      ⟨before,nativeBurn ctx r⟩ :: tokenLedger ctx (before+nativeBurn ctx r) rs

private theorem except_bind_ok {α β : Type} {a : Except String α}
    {f : α → Except String β} {b : β} (h : a.bind f = .ok b) :
    ∃ x, a = .ok x ∧ f x = .ok b := by
  cases a <;> simp_all [Except.bind]

/-- Actual native execution determines the complete ordered token ledger,
with every intermediate endpoint below the native u128 bound. -/
theorem applyReceipts_token_ledger (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (i : Nat) (st out : Acc × List Limit),
      st.1.tokensBurnt < Params.two128 →
      applyReceipts ctx i st rs = .ok out →
      out.1.tokensBurnt = st.1.tokensBurnt + (rs.map (nativeBurn ctx)).sum ∧
      out.1.tokensBurnt < Params.two128 ∧
      ∀ x ∈ tokenLedger ctx st.1.tokensBurnt rs,
        x.before < Params.two128 ∧ x.before+x.burnt < Params.two128
  | [], _, st, out, hb, h => by
    cases h
    simpa [tokenLedger] using hb
  | r::rs, i, (acc,ls), out, hb, h => by
    simp only [applyReceipts] at h
    split at h
    · cases h
    · split at h
      · rename_i hr
        obtain ⟨acc',ha,h⟩ := except_bind_ok h
        have he := applySystemReceipt_tokens acc acc' r ha
        have hn : nativeBurn ctx r = 0 := by simp [nativeBurn,hr]
        obtain ⟨ho,hob,hl⟩ := applyReceipts_token_ledger ctx rs (i+1) (acc',ls) out (by simpa [he] using hb) h
        simp only [he] at ho
        refine ⟨by simpa [hn,he] using ho,hob,?_⟩
        simpa [tokenLedger,hn,he] using And.intro (And.intro hb hb) hl
      · rename_i hr
        split at h
        · split at h <;> cases h
        · rename_i acc' ha
          obtain ⟨ls',_,h⟩ := except_bind_ok h
          obtain ⟨he,hb',_⟩ := applyReceipt_tokens ⟨ctx.height,ctx.gasPrice⟩ acc acc' r ha
          have hn : nativeBurn ctx r = Params.G * min r.gasPrice ctx.gasPrice := by simp [nativeBurn,hr]
          obtain ⟨ho,hob,hl⟩ := applyReceipts_token_ledger ctx rs (i+1) (acc',ls') out hb' h
          refine ⟨?_,hob,?_⟩
          · simpa [List.map_cons,List.sum_cons,hn,he,Nat.add_assoc] using ho
          · simpa [tokenLedger,hn,he] using And.intro (And.intro hb hb') hl

theorem tokenLedger_length (ctx : ApplyCtx) (rs : List Receipt) (before : Nat) :
    (tokenLedger ctx before rs).length = rs.length := by
  induction rs generalizing before with
  | nil => rfl
  | cons r rs ih => simp [tokenLedger,ih]

/-- Serialization at every receipt boundary uses the same bytes on both sides. -/
theorem tokenLedger_boundary (ctx : ApplyCtx) (r s : Receipt) (rs : List Receipt)
    (before : Nat) :
    let a : TokenInput := ⟨before,nativeBurn ctx r⟩
    let b : TokenInput := ⟨before+nativeBurn ctx r,nativeBurn ctx s⟩
    tokenLedger ctx before (r::s::rs) = a::b::tokenLedger ctx (b.before+b.burnt) rs ∧
    a.newBytes = b.oldBytes := by
  exact ⟨rfl,rfl⟩

/-- Concatenating native receipt lists preserves the ledger order and carries
its exact accumulated total into the next list, including empty lists. -/
theorem tokenLedger_append (ctx : ApplyCtx) (xs ys : List Receipt) (before : Nat) :
    tokenLedger ctx before (xs++ys) = tokenLedger ctx before xs ++
      tokenLedger ctx (before+(xs.map (nativeBurn ctx)).sum) ys := by
  induction xs generalizing before with
  | nil => simp [tokenLedger]
  | cons x xs ih => simp [tokenLedger,ih,Nat.add_assoc]

end ZkFormal.NearV3.Assembly.RcptSkeleton
