import ZkFormal.NearV3.Assembly.ReceiptWellformed
import ZkFormal.NearV3.Assembly.DecodedTransitions

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

theorem pMany_length {α : Type} (p : P α) : ∀ n {bs rest : Bytes} {xs : List α},
    pMany p n bs = .ok (xs,rest) → xs.length = n
  | 0, _, _, _, h => by cases h; rfl
  | n+1, _, _, _, h => by
    unfold pMany at h
    obtain ⟨⟨x,r⟩,_,h⟩ := bind_ok h
    obtain ⟨⟨xs,r'⟩,hs,h⟩ := bind_ok h
    cases h
    simpa only [List.length_cons] using congrArg (·+1) (pMany_length p n hs)

theorem pVec_length_bound {α : Type} {p : P α} {label : String}
    {bs rest : Bytes} {xs : List α} (h : pVec label p bs = .ok (xs,rest)) :
    xs.length < 4294967296 := by
  unfold pVec at h
  obtain ⟨⟨n,r⟩,hn,h⟩ := bind_ok h
  rw [pMany_length p n h]
  exact (ReexecV3D0.lift_readLE_inv (n := 4) hn).2

theorem pTransition_wf {bs rest : Bytes} {t : Transition}
    (h : pTransition bs = .ok (t,rest)) : V3.transitionWf t = true := by
  unfold pTransition at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    simp only [V3.transitionWf,V3.h32,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
    refine ⟨⟨⟨V3.pHash_len (by assumption),pVec_length_bound (by assumption)⟩,?_⟩,
      V3.pHash_len (by assumption)⟩
    apply List.all_eq_true.mpr
    intro v hv
    apply decide_eq_true
    exact pVec_property (pBytes _) (fun b => b.length < 4294967296)
      (fun _ _ _ hh => (ReexecV3D0.pBytes_inv hh).2) (by assumption) v hv

theorem decodeStateWitness_transition_wf {bs : Bytes} {w : StateWitness}
    (h : decodeStateWitness bs = .ok w) :
    V3.transitionWf w.main = true ∧ w.implicit.length < 4294967296 ∧
      ∀ t ∈ w.implicit, V3.transitionWf t = true := by
  unfold decodeStateWitness at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    exact ⟨pTransition_wf (by assumption),pVec_length_bound (by assumption),
      pVec_property pTransition (fun t => V3.transitionWf t = true)
        (fun _ _ _ hh => pTransition_wf hh) (by assumption)⟩

theorem pReceipt_wfD0 {bs rest : Bytes} {r : Receipt}
    (h : pReceipt bs = .ok (r,rest)) : V3.receiptWfD0 r = true := by
  have hw := V3.pReceipt_wf h
  unfold pReceipt at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    simp only [V3.receiptWfD0,hw,Bool.true_and]
    grind only

theorem pPathItem_wf {bs rest : Bytes} {p : Bytes × Nat}
    (h : pPathItem bs = .ok (p,rest)) : V3.pathWf p = true := by
  unfold pPathItem at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    simp only [V3.pathWf,V3.h32,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
    exact ⟨V3.pHash_len (by assumption),by omega⟩

theorem pEntry_wf {bs rest : Bytes} {e : ProofEntry}
    (h : pEntry bs = .ok (e,rest)) : V3.entryWf e = true := by
  unfold pEntry at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    simp only [V3.entryWf,V3.h32,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨⟨V3.pHash_len (by assumption),pVec_length_bound (by assumption)⟩,?_⟩,
      (ReexecV3D0.lift_readLE_inv (n := 8) (by assumption)).2⟩,
      (ReexecV3D0.lift_readLE_inv (n := 8) (by assumption)).2⟩,
      pVec_length_bound (by assumption)⟩,?_⟩
    · exact List.all_eq_true.mpr (pVec_property pReceipt _
        (fun _ _ _ hh => pReceipt_wfD0 hh) (by assumption))
    · exact List.all_eq_true.mpr (pVec_property pPathItem _
        (fun _ _ _ hh => pPathItem_wf hh) (by assumption))

end ZkFormal.NearV3.Assembly
