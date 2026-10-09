import ZkFormal.NearV3.Rcpt.Link.NativeRouting
import ZkFormal.NearV3.Rcpt.Candidates.DecodedRoutingBoundaries

namespace ZkFormal.NearV3.RcptLink
open NearSpec NearSpecV3 ZkFormal.Near Near.Link

private theorem chars_positive {xs : Bytes} {last : Bool}
    (h : AccountId.charsOk last xs=true) : ∀ b∈xs,0<b.toNat := by
  induction xs generalizing last with
  | nil => simp
  | cons x xs ih =>
    simp only [AccountId.charsOk] at h
    split at h
    · rename_i hx
      have hxpos : 0<x.toNat := by
        simp only [AccountId.isAlnum,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at hx
        omega
      intro b hb
      rcases List.mem_cons.mp hb with rfl|hb
      · exact hxpos
      · exact ih h b hb
    · split at h
      · rename_i hx
        have hxpos : 0<x.toNat := by
          simp only [AccountId.isSep,Bool.or_eq_true,beq_iff_eq] at hx
          omega
        simp only [Bool.and_eq_true] at h
        have ht := h.2
        intro b hb
        rcases List.mem_cons.mp hb with rfl|hb
        · exact hxpos
        · exact ih ht b hb
      · cases h

/-- The exact endpoint byte bounds required by the receipt lexicographic proof. -/
theorem boundaryNats_valid {o : Option Bytes}
    (h : ∀ b,o=some b → AccountId.valid b=true) :
    (∀ y∈boundaryNats o,0<y ∧ y<256) ∧ (boundaryNats o).length≤64 := by
  cases o with
  | none => simp [boundaryNats]
  | some bs =>
    have hv := h bs rfl
    have hl := (valid_length hv).2
    have hc : AccountId.charsOk true bs=true := by
      simp only [AccountId.valid,Bool.and_eq_true] at hv
      exact hv.2
    constructor
    · intro y hy
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hy
      exact ⟨chars_positive hc b hb,b.toNat_lt⟩
    · simpa only [boundaryNats,Option.getD_some,List.length_map] using hl

end ZkFormal.NearV3.RcptLink
