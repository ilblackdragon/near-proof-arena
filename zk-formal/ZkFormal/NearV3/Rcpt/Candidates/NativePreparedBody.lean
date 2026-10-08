import ZkFormal.NearV3.Assembly.RcptNativeBodyLength
import ZkFormal.NearV3.Assembly.PrepBodyComplete
import ZkFormal.NearV3.Assembly.NativeWitnessFields

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Assembly Assembly.RcptSkeleton ZkFormal.NearV3.Sched

/-- Native refunds are charged by the actual incoming receipts, without an AIR body-length premise. -/
theorem native_body_length_bound (ctx : ApplyCtx) (rs : List Receipt)
    (hw : ∀r∈rs,r.wf=true) {t : PTrie} {out : MainOut}
    (h : applyNewChunk prims ctx t rs=.ok out) :
    (u32 0++encodeReceipts out.outgoing).length≤8+289*rs.length := by
  let xs : List Input:=rs.map (fun r=>⟨r,nativeRefund ctx r⟩)
  have he : xs.map Input.receipt=rs:=by simp [xs,Function.comp_def]
  have hwell : ∀x∈xs,x.receipt.wf=true := by
    intro x hx
    obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hx
    exact hw r hr
  have hh:=applyNewChunk_planned_body_length ctx [xs]
    (by intro ys hy; simp only [List.mem_singleton] at hy;subst ys;exact hwell)
    (by intro ys hy; simp only [List.mem_singleton] at hy;subst ys
        intro x hx;obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hx;rfl)
    (by simpa only [List.flatten_cons,List.flatten_nil,List.append_nil,he] using h)
  have hb : ∀ys : List Input,(∀x∈ys,x.receipt.wf=true)→
      (ys.map refundLength).sum≤289*ys.length := by
    intro ys hy
    induction ys with
    | nil=>simp
    | cons y ys ih=>
      have h1:=refundLength_bound y (hy y (by simp))
      have h2:=ih (fun z hz=>hy z (by simp [hz]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega
  have hs:=hb xs hwell
  simp only [List.flatten_cons,List.flatten_nil,List.append_nil] at hh
  have hl : xs.length=rs.length:=by simp [xs,Function.comp_def]
  omega

theorem prepD0_body_eq {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) : p.body=hint.body := by
  obtain ⟨pc,_,hb⟩:=bind_ok hp
  unfold prepBody at hb
  repeat' (first | (obtain ⟨_,_,hb⟩:=bind_ok hb) | (split at hb) | (dsimp only at hb))
  all_goals first
    | (simp only [pure,Except.pure,Except.ok.injEq] at hb;subst hb;rfl)
    | (exfalso;exact throw_ne (by assumption))

theorem accepted_native_body_bound {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {p : Prep}
    (hp : prepD0 cb (nativeHint k w m)=.ok p)
    (hk : walkD0 cb=.ok k) (hw : decodeW wb=.ok w) (h : checkD0a B0 cb wb=.ok ())
    (hm : m.NativeValid k w) : p.body.length≤1295017 := by
  have hh:=(relD0a_iff B0 cb wb).mpr h
  have hc : checkD0 cb wb=.ok () := by
    have hc:=hh.1
    unfold RelD0 acceptsD0 at hc
    split at hc <;> simp_all
  obtain ⟨raw,codes,_,hd,_⟩:=checkD0_witness_fields hk hw hc
  have hg : k.slotB2.gasLimit≤maxGasLimitD0 := by
    simpa only [a1,hk,decide_eq_true_eq] using hh.2.1
  have hn:=applyNewChunk_receipt_bound hm.run hg
  have hb:=native_body_length_bound (m.ctx k) (appliedReceipts k w) (appliedReceipts_wf hd) hm.run
  rw [prepD0_body_eq hp]
  change (u32 0++encodeReceipts m.result.outgoing).length≤1295017
  omega

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
