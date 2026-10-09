import ZkFormal.NearV3.Candidates.ProcPriorRecordPhysicalBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordByteActivity
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable
open ProcPriorRecordPhysicalBytes

def gate (j:Nat):Expr:=.mul (c (ProcPriorVertical4Linear.stage 3))
  (if j=2 then sub (words false) (c topLimb) else words false)

theorem flags {tr:Trace Fp} {t r j:Nat} {pub:List Fp}
    (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) (hr:r<tr.height t) (hj:j<3)
    (hm:(verticalByte j).multNat tr t r pub≠0):
    cv tr t r (ProcPriorVertical4Linear.stage 3)=1 ∧
      cv tr t r sender+cv tr t r receiver+cv tr t r amount=1 ∧
      (j=2→cv tr t r topLimb=0) := by
  have hmult:(verticalByte j).mult=[gate j]:=by
    have h:j=0 ∨ j=1 ∨ j=2:=by omega
    rcases h with rfl|rfl|rfl <;> rfl
  have hg:(gate j).eval tr t r pub=1:=by
    by_cases he:(gate j).eval tr t r pub=1
    · exact he
    · simp only [Interaction.multNat,hmult,Interaction.multNat.go,he,ite_false,Nat.zero_add] at hm
      exact (hm rfl).elim
  have hcell (x:Nat):tr.cell t r x=Fp.ofNat (cv tr t r x):=(Fp.ofNat_toNat _).symm
  have hstage:cv tr t r (ProcPriorVertical4Linear.stage 3)=1:=by
    have hb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member
      (Table.boolC (ProcPriorVertical4Linear.stage 3)) (by simp [ProcPriorVertical4Linear.windows]))
    by_cases hz:cv tr t r (ProcPriorVertical4Linear.stage 3)=0
    · have hc:tr.cell t r (ProcPriorVertical4Linear.stage 3)=0:=by rw [hcell _,hz];rfl
      simp only [gate,ZkFormal.Near.eval_mul,Codec.ev_c,hz] at hg
      change (0:Fp)*_=1 at hg
      exact False.elim ((by decide : (0:Fp)≠1) ((Lean.Grind.Semiring.zero_mul _).symm.trans hg))
    · omega
  have hw:=ProcPriorRecordGeometry.words_bound hL hr hstage
  have ha:=ProcPriorRecordSound.flag hL hr hstage act (by simp)
  have hl:=ProcPriorRecordGeometry.limbs_eq hL hr hstage
  have htop:=ProcPriorRecordSound.flag hL hr hstage topLimb (by simp)
  have hwords:(words false).eval tr t r pub=Fp.ofNat (cv tr t r sender+cv tr t r receiver+cv tr t r amount):=by
    change tr.cell t r sender+tr.cell t r receiver+tr.cell t r amount=_
    rw [hcell _,hcell _,hcell _,ZkFormal.Near.ofNat_add',ZkFormal.Near.ofNat_add']
  have hg':(if j=2 then Fp.ofNat (cv tr t r sender+cv tr t r receiver+cv tr t r amount)+ -Fp.ofNat (cv tr t r topLimb)
      else Fp.ofNat (cv tr t r sender+cv tr t r receiver+cv tr t r amount))=(1:Fp):=by
    by_cases he:j=2
    · simpa only [gate,he,ite_true,ZkFormal.Near.eval_mul,ZkFormal.Near.eval_add,ZkFormal.Near.eval_neg,sub,
        Codec.ev_c,hstage,hwords,show Fp.ofNat 1=(1:Fp) from rfl,Lean.Grind.Semiring.one_mul] using hg
    · simpa only [gate,he,ite_false,ZkFormal.Near.eval_mul,Codec.ev_c,hstage,hwords,
        show Fp.ofNat 1=(1:Fp) from rfl,Lean.Grind.Semiring.one_mul] using hg
  have hw1:cv tr t r sender+cv tr t r receiver+cv tr t r amount=1:=by
    by_cases hz:cv tr t r sender+cv tr t r receiver+cv tr t r amount=0
    · have ht0:cv tr t r topLimb=0:=by omega
      rw [hz,ht0] at hg'
      by_cases he:j=2
      · simp only [he,ite_true] at hg'
        exact ((by decide : (Fp.ofNat 0 + -Fp.ofNat 0) ≠ (1:Fp)) hg').elim
      · simp only [he,ite_false] at hg'
        exact ((by decide : Fp.ofNat 0 ≠ (1:Fp)) hg').elim
    · omega
  refine ⟨hstage,hw1,?_⟩
  intro hj2
  rw [hj2,if_pos rfl,hw1] at hg'
  by_cases ht1:cv tr t r topLimb=1
  · rw [ht1] at hg'
    exact ((by decide : (Fp.ofNat 1 + -Fp.ofNat 1) ≠ (1:Fp)) hg').elim
  · omega
end ZkFormal.NearV3.Candidates.ProcPriorRecordByteActivity
