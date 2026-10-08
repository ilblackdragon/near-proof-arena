import ZkFormal.NearV3.Render.Ups.CompactExtract.LayoutMain
import ZkFormal.NearV3.Extract.Ups.UpsVal
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows

/-- Compact UPS needs only the scheduler length channel. Fresh bytes travel
from Codec directly to SHA, so there is deliberately no SPOST premise. -/
structure SchedLength (v : List UpsSeg) (sv : Nat→NearSpec.Bytes) : Prop where
  splen : ∀m∈(upsTraffic v).recvs B_SPLEN,∃tau,tau<P ∧ m.toFp=Msg.toFp [tau,(sv tau).length]
  len : ∀tau,(sv tau).length<2^24

attribute [local irreducible] UpsSeg.row UpsSeg.next
section
variable {v : List UpsSeg} (hw : Wf v) {sv : Nat→NearSpec.Bytes} (SV : SchedLength v sv)
  {s : UpsSeg} (hs : s∈v) {ps : List (Nat×Nat)} {fls : List (List (Nat×Nat))} {ws : List Nat}
  (hL : UpsLayout s ps fls ws)
include hw SV hs hL
/-- The length decoded from the UPS limbs equals the scheduler value length.
Byte bounds on the three limbs remain explicit, as in the original extraction. -/
theorem ups_vlen (hvb : s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256) :
    (sv (s.row 0 tau)).length = s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2 := by
  have hP := P_lit
  have hlen := lenLe hw hs
  have hsl := SV.len (s.row 0 tau)
  have h4:=hL.walk.1
  -- `SPLEN`
  have hm : [s.row 0 tau, (s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2) % P] ∈
      (upsTraffic v).recvs B_SPLEN :=
    mem_upsRecvs.2 ⟨s, hs, 0, by omega, by
      rw [hL.msgsW 0 (by omega) B_SPLEN false]; simp [hL.walk.2.1]⟩
  obtain ⟨τ, hτ, he⟩ := SV.splen _ hm
  have e := Link.toFp_inj (a := [s.row 0 tau, (s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2) % P])
    (b := [τ, (sv τ).length])
    (by intro x hx; simp at hx; rcases hx with rfl | rfl
        · exact rowLt hw hs _ _
        · exact Nat.mod_lt _ (by omega))
    (by intro x hx; simp at hx; rcases hx with rfl | rfl
        · exact hτ
        · have := SV.len τ; omega) he
  simp only [List.cons.injEq, and_true] at e
  obtain ⟨e1, e2⟩ := e
  subst e1
  rw [Nat.mod_eq_of_lt (by omega)] at e2
  exact e2.symm

end
end ZkFormal.NearV3.Render.UpsRelay.Extract
