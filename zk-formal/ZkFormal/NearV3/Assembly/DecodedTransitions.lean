import ZkFormal.NearV3.Assembly.ReceiptSeedDecode

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

def TransitionHashes (t : Transition) : Prop := t.blockHash.length = 32 ∧ t.postStateRoot.length = 32

theorem pTransition_hashes {bs rest : Bytes} {t : Transition}
    (h : pTransition bs = .ok (t,rest)) : TransitionHashes t := by
  unfold pTransition at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    constructor
    all_goals exact (pHash_size (by assumption)).1

theorem decodeStateWitness_transition_hashes {bs : Bytes} {w : StateWitness}
    (h : decodeStateWitness bs = .ok w) :
    TransitionHashes w.main ∧ ∀ t ∈ w.implicit, TransitionHashes t := by
  unfold decodeStateWitness at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    constructor
    · exact pTransition_hashes (by assumption)
    · exact pVec_property pTransition TransitionHashes (fun _ _ _ hp => pTransition_hashes hp)
        (by assumption)

end ZkFormal.NearV3.Assembly
