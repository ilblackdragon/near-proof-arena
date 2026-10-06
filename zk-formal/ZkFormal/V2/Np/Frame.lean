import ZkFormal.V2.Np.Compose

/-!
# ZkFormal.V2.Np.Frame — frame lemmas for the v2 bus parts

The v2 bus disjuncts depend on the claim (public messages), the decoded main trace
(`busMsgs`), the header and the finals, exactly like v1's.  So they survive the same
transcript extensions (`OAgree`, same finals).
-/

namespace ZkFormal.V2.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
open ZkFormal.Udr ZkFormal.Udr.Np ZkFormal.V2

section
variable (AP : AirP) (prm : Params)

theorem pubBM_congr {τ τ' : PTn} (h : τ.cb = τ'.cb) (s : Bool) : pubBM AP τ s = pubBM AP τ' s := by
  unfold pubBM pubT; rw [h]

theorem pubGp_congr {τ τ' : PTn} (h : τ.cb = τ'.cb) (α γ : Fp8) (s : Bool) :
    pubGp AP τ α γ s = pubGp AP τ' α γ s := by
  unfold pubGp; rw [pubBM_congr AP h]

theorem busMsgsP_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : 1 ≤ k) (s : Bool) :
    busMsgsP AP prm τ s = busMsgsP AP prm τ' s := by
  unfold busMsgsP; rw [busMsgs_congr h hk, pubBM_congr AP h.1]

theorem fpDifferP_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : 1 ≤ k) (α : Fp8) :
    FpDifferP AP prm τ α ↔ FpDifferP AP prm τ' α := by
  unfold FpDifferP; rw [busMsgsP_congr AP prm h hk, busMsgsP_congr AP prm h hk]

theorem gpDifferP_congr {k : Nat} {τ τ' : PTn} (h : OAgree k τ τ') (hk : 1 ≤ k) (α γ : Fp8) :
    GpDifferP AP prm τ α γ ↔ GpDifferP AP prm τ' α γ := by
  unfold GpDifferP; rw [busMsgsP_congr AP prm h hk, busMsgsP_congr AP prm h hk]

theorem finSends_congr {τ τ' : PTn} (h : τ.header? = τ'.header?) (hf : finalsOf τ = finalsOf τ') :
    finSends AP prm τ = finSends AP prm τ' := by
  unfold finSends finsSplit; rw [layOf_congr _ prm h, hf]

theorem finRecvs_congr {τ τ' : PTn} (h : τ.header? = τ'.header?) (hf : finalsOf τ = finalsOf τ') :
    finRecvs AP prm τ = finRecvs AP prm τ' := by
  unfold finRecvs finsSplit; rw [layOf_congr _ prm h, hf]

theorem busFinalsFailP_congr {τ τ' : PTn} (h : τ.header? = τ'.header?) (hf : finalsOf τ = finalsOf τ')
    (hc : τ.cb = τ'.cb) (α γ : Fp8) :
    BusFinalsFailP AP prm τ α γ ↔ BusFinalsFailP AP prm τ' α γ := by
  unfold BusFinalsFailP
  rw [finSends_congr AP prm h hf, finRecvs_congr AP prm h hf, pubGp_congr AP hc, pubGp_congr AP hc]

theorem count_doom_leP {τ : PTn} {S : PTn → Prop} (Bad : Fp8 → Prop)
    (h : ∀ c, ¬ Bad c → S (τ.pushChal c)) :
    count Fp8.all (fun c => Shaped (VnpP AP prm) (τ.pushChal c) ∧ ¬ S (τ.pushChal c)) ≤
      count Fp8.all Bad :=
  count_mono _ fun c hc => Classical.byContradiction fun hb => hc.2 (h c hb)

/-- `GlobalFailP` survives a challenge. -/
theorem globalFailP_pushChal (τ : PTn) (c : Fp8) (hE : τ.entries ≠ [])
    (h : GlobalFailP AP prm τ) : GlobalFailP AP prm (τ.pushChal c) := by
  have hl : layOf AP.toAir prm (τ.pushChal c) = layOf AP.toAir prm τ := by
    simp [layOf, hdrOf, pushChal_header τ c hE]
  unfold GlobalFailP pubT at h ⊢
  rw [pushChal_chals, pushChal_elems, hl]
  have hcb : (τ.pushChal c).cb = τ.cb := rfl
  rw [hcb]
  revert h
  rcases τ.chals with _ | ⟨a, _ | ⟨b, _ | ⟨d, _ | ⟨z, rest⟩⟩⟩⟩ <;>
    rcases τ.elems with _ | ⟨f, _ | ⟨o, r⟩⟩ <;> simp

end

end ZkFormal.V2.Np
