import ZkFormal.NearV3.Assembly.ReceiptWellformed
import ZkFormal.NearV3.Assembly.DecodedShapes

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

/-- Exact unchanged D0 parser domain: system predecessors remain permitted. -/
theorem pReceipt_named {bs rest : Bytes} {r : Receipt}
    (h : pReceipt bs = .ok (r,rest)) : AccountId.isNamed r.receiverId=true := by
  have hh := pReceipt_wfD0 h
  exact (Bool.and_eq_true_iff.mp hh).2

theorem pEntry_receipts_named {bs rest : Bytes} {e : ProofEntry}
    (h : pEntry bs = .ok (e,rest)) : ∀ r ∈ e.receipts, AccountId.isNamed r.receiverId = true := by
  unfold pEntry at h
  repeat' (obtain ⟨_,_,h⟩ := bind_ok h)
  dsimp only at h
  cases h
  exact pVec_property pReceipt (fun r => AccountId.isNamed r.receiverId = true)
    (fun _ _ _ hp => pReceipt_named hp) (by assumption)

theorem decodeStateWitness_receipts_named {bs : Bytes} {w : StateWitness}
    (h : decodeStateWitness bs = .ok w) : ∀ e ∈ w.entries, ∀ r ∈ e.receipts, AccountId.isNamed r.receiverId = true := by
  unfold decodeStateWitness at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    exact pVec_property pEntry (fun e => ∀ r ∈ e.receipts, AccountId.isNamed r.receiverId = true)
      (fun _ _ _ hp => pEntry_receipts_named hp) (by assumption)

theorem appliedReceipts_named {k : WalkD0} {w : StateWitness} {bs : Bytes}
    (hw : decodeStateWitness bs = .ok w) : ∀ r ∈ appliedReceipts k w, AccountId.isNamed r.receiverId = true := by
  intro r hr
  obtain ⟨e,he,hr⟩ := appliedReceipts_mem_entry hr
  exact decodeStateWitness_receipts_named hw e he r hr

end ZkFormal.NearV3.Assembly
