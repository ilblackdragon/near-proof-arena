import ZkFormal.NearV3.Render.Ups.NodeHeaderBytes
import ZkFormal.NearV3.Render.Node.WinFacts

/-! Split branch bitmap facts from ordinary child-slot occupancy. -/
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near ZkFormal.Near.Render
open NodeGen (F)

abbrev splitHasNew (I : UpsInst) : Prop := I.ci=4 ∨ I.ci=6 ∨ I.ci=9 ∨ I.ci=10

def splitNewSlot (I : UpsInst) : Nat := if I.ts=1 then 0 else 15

structure SplitBitmap (I : UpsInst) (Q : UpsPartI) (e : NodeEncoding Q) : Prop where
  xbound : I.x < 16
  slots : Q.kind=10 → ∀ j, j<16 →
    ((NodeGen3.kidsOf e.node).getD j .none ≠ .none ↔
      (I.ci≠4 ∧ j=I.x) ∨ (splitHasNew I ∧ j=splitNewSlot I))
  distinct : Q.kind=10 → I.ci≠4 → splitHasNew I → I.x ≠ splitNewSlot I

theorem spYc_indicator (I : UpsInst) : spYc I=ind (splitHasNew I) := by
  by_cases h4 : I.ci=4 <;> by_cases h6 : I.ci=6 <;> by_cases h9 : I.ci=9 <;> by_cases h10 : I.ci=10 <;>
    simp_all [spYc,cin,ind,splitHasNew]

theorem SplitBitmap.slot_bit {I : UpsInst} {Q : UpsPartI} {e : NodeEncoding Q}
    (h : SplitBitmap I Q e) (hk : Q.kind=10) {j : Nat} (hj : j<16) :
    NodeGen.bitOf (kidBitmap (NodeGen3.kidsOf e.node)) j =
      if (I.ci≠4 ∧ j=I.x) ∨ (splitHasNew I ∧ j=splitNewSlot I) then 1 else 0 := by
  rw [NodeGen3.bitOf_kidBitmap]
  simp only [NodeGen3.kbit,h.slots hk j hj]

theorem SplitBitmap.low {I : UpsInst} {Q : UpsPartI} {e : NodeEncoding Q}
    (h : SplitBitmap I Q e) (hk : Q.kind=10) :
    ((kidBitmap (NodeGen3.kidsOf e.node) % 256 : Nat) : Int)=bmLV I := by
  have hb := NodeRow.lo8 (kidBitmap (NodeGen3.kidsOf e.node))
  rw [h.slot_bit hk (by decide : 0<16),h.slot_bit hk (by decide : 1<16),
    h.slot_bit hk (by decide : 2<16),h.slot_bit hk (by decide : 3<16),
    h.slot_bit hk (by decide : 4<16),h.slot_bit hk (by decide : 5<16),
    h.slot_bit hk (by decide : 6<16),h.slot_bit hk (by decide : 7<16)] at hb
  rw [← hb]
  clear hb
  unfold bmLV
  rw [spYc_indicator]
  have hd := h.distinct hk
  have hx := h.xbound
  rcases (show I.x=0 ∨ I.x=1 ∨ I.x=2 ∨ I.x=3 ∨ I.x=4 ∨ I.x=5 ∨ I.x=6 ∨ I.x=7 ∨ I.x=8 ∨ I.x=9 ∨ I.x=10 ∨ I.x=11 ∨ I.x=12 ∨ I.x=13 ∨ I.x=14 ∨ I.x=15 by omega)
    with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx <;>
    by_cases hc : I.ci=4 <;> by_cases hn : splitHasNew I <;> by_cases ht : I.ts=1 <;>
    simp_all [splitHasNew,splitNewSlot,cin,ind,xbit,pxV]

theorem SplitBitmap.high {I : UpsInst} {Q : UpsPartI} {e : NodeEncoding Q}
    (h : SplitBitmap I Q e) (hk : Q.kind=10) :
    ((kidBitmap (NodeGen3.kidsOf e.node) / 256 : Nat) : Int)=bmHV I := by
  have hb := NodeRow.hi8 (kidBitmap (NodeGen3.kidsOf e.node))
  rw [h.slot_bit hk (by decide : 8<16),
    h.slot_bit hk (by decide : 9<16),
    h.slot_bit hk (by decide : 10<16),
    h.slot_bit hk (by decide : 11<16),
    h.slot_bit hk (by decide : 12<16),
    h.slot_bit hk (by decide : 13<16),
    h.slot_bit hk (by decide : 14<16),
    h.slot_bit hk (by decide : 15<16)] at hb
  have hlt : kidBitmap (NodeGen3.kidsOf e.node) < 65536 := by
    have hw := e.wf
    cases hn : e.node with
    | leaf => simp [NodeGen3.kidsOf,kidBitmap]
    | ext => simp [NodeGen3.kidsOf,kidBitmap]
    | branch val kids mem =>
      have hw' : (NodeV3.branch val kids mem).wf := by simpa [hn] using hw
      exact Link.kidBitmap_lt hw'.1
  have hr : kidBitmap (NodeGen3.kidsOf e.node)/256 < 256 := by omega
  rw [Nat.mod_eq_of_lt hr] at hb
  rw [← hb]
  clear hb
  unfold bmHV
  rw [spYc_indicator]
  have hd := h.distinct hk
  have hx := h.xbound
  rcases (show I.x=0 ∨ I.x=1 ∨ I.x=2 ∨ I.x=3 ∨ I.x=4 ∨ I.x=5 ∨ I.x=6 ∨ I.x=7 ∨ I.x=8 ∨ I.x=9 ∨ I.x=10 ∨ I.x=11 ∨ I.x=12 ∨ I.x=13 ∨ I.x=14 ∨ I.x=15 by omega)
    with hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx | hx <;>
    by_cases hc : I.ci=4 <;> by_cases hn : splitHasNew I <;> by_cases ht : I.ts=1 <;>
    simp_all [splitHasNew,splitNewSlot,cin,ind,xbit,pxV]

end ZkFormal.NearV3.Render.UpsGen
