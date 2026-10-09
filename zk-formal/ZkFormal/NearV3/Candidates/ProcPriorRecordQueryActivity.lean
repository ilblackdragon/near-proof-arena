import ZkFormal.NearV3.Candidates.ProcPriorRecordPhysicalBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordQueryActivity
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable

def query:Interaction:=ProcPriorVertical4Linear.interaction 3 (ProcPriorRecordLinear.interactions 75 71 72 67 76)[3]!

theorem flags {tr:Trace Fp} {t r:Nat} {pub:List Fp}
    (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) (hr:r<tr.height t)
    (hm:query.multNat tr t r pub≠0):
    cv tr t r (ProcPriorVertical4Linear.stage 3)=1 ∧ cv tr t r topLimb=1 ∧
      cv tr t r sender+cv tr t r receiver=1 := by
  have hg:tr.cell t r (ProcPriorVertical4Linear.stage 3)*(tr.cell t r topLimb*(tr.cell t r sender+tr.cell t r receiver))=1:=by
    change (if tr.cell t r (ProcPriorVertical4Linear.stage 3)*(tr.cell t r topLimb*(tr.cell t r sender+tr.cell t r receiver))=1 then 1 else 0)+0≠0 at hm
    split at hm
    · assumption
    · exact (hm rfl).elim
  have hc (x:Nat):tr.cell t r x=Fp.ofNat (cv tr t r x):=(Fp.ofNat_toNat _).symm
  have hb:=hL.bool hr (ProcPriorVerticalMemorySound.window_member
    (Table.boolC (ProcPriorVertical4Linear.stage 3)) (by simp [ProcPriorVertical4Linear.windows]))
  have hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1:=by
    by_cases hz:cv tr t r (ProcPriorVertical4Linear.stage 3)=0
    · rw [hc _,hz] at hg
      change (0:Fp)*_=1 at hg
      have he:(0:Fp)=1:=(Lean.Grind.Semiring.zero_mul _).symm.trans hg
      exact ((by decide : (0:Fp)≠1) he).elim
    · omega
  have ht:=ProcPriorRecordSound.flag hL hr hs topLimb (by simp)
  have hw:=ProcPriorRecordGeometry.words_bound hL hr hs
  have ha:=ProcPriorRecordSound.flag hL hr hs act (by simp)
  rw [hc _,hc _,hc _,hc _,hs] at hg
  have ht1:cv tr t r topLimb=1:=by
    by_cases hz:cv tr t r topLimb=0
    · rw [hz] at hg
      change (1:Fp)*(0*_)=1 at hg
      have he:(0:Fp)=1:=by rw [Lean.Grind.Semiring.zero_mul,Lean.Grind.Semiring.mul_zero] at hg;exact hg
      exact ((by decide : (0:Fp)≠1) he).elim
    · omega
  have hw1:cv tr t r sender+cv tr t r receiver=1:=by
    by_cases hz:cv tr t r sender+cv tr t r receiver=0
    · have h0:cv tr t r sender=0:=by omega
      have h1:cv tr t r receiver=0:=by omega
      rw [h0,h1,ht1] at hg
      exact ((by decide : (Fp.ofNat 1*(Fp.ofNat 1*(Fp.ofNat 0+Fp.ofNat 0)))≠(1:Fp)) hg).elim
    · omega
  exact ⟨hs,ht1,hw1⟩
end ZkFormal.NearV3.Candidates.ProcPriorRecordQueryActivity
