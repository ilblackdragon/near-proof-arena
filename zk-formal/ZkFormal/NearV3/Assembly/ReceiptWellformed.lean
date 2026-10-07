import ZkFormal.NearV3.Assembly.AppliedSeeds
import ZkFormal.NearV3.Assembly.NativeCapacity
import ZkFormal.V3.RefundCodec

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

theorem pEntry_receipts_wf {bs rest : Bytes} {e : ProofEntry}
    (h : pEntry bs = .ok (e,rest)) : ∀ r ∈ e.receipts, r.wf = true := by
  unfold pEntry at h
  repeat' (obtain ⟨_,_,h⟩ := bind_ok h)
  dsimp only at h
  cases h
  exact pVec_property pReceipt (fun r => r.wf = true)
    (fun _ _ _ hp => V3.pReceipt_wf hp) (by assumption)

theorem decodeStateWitness_receipts_wf {bs : Bytes} {w : StateWitness}
    (h : decodeStateWitness bs = .ok w) : ∀ e ∈ w.entries, ∀ r ∈ e.receipts, r.wf = true := by
  unfold decodeStateWitness at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    exact pVec_property pEntry (fun e => ∀ r ∈ e.receipts, r.wf = true)
      (fun _ _ _ hp => pEntry_receipts_wf hp) (by assumption)

theorem appliedReceipts_wf {k : WalkD0} {w : StateWitness} {bs : Bytes}
    (hw : decodeStateWitness bs = .ok w) : ∀ r ∈ appliedReceipts k w, r.wf = true := by
  intro r hr
  obtain ⟨e,he,hr⟩ := appliedReceipts_mem_entry hr
  exact decodeStateWitness_receipts_wf hw e he r hr

theorem MainExecutionV3.NativeValid.body_decodes {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {bs : Bytes} (h : m.NativeValid k w)
    (hd : decodeStateWitness bs = .ok w) (hg : k.slotB2.gasLimit ≤ maxGasLimitD0) :
    decodeBody (u32 0 ++ encodeReceipts m.result.outgoing) = .ok m.result.outgoing := by
  have hn := applyNewChunk_receipt_bound h.run hg
  exact V3.decodeBody_outgoing prims (m.ctx k) m.pre (appliedReceipts k w) m.result
    h.run (appliedReceipts_wf hd) (by omega)

end ZkFormal.NearV3.Assembly
