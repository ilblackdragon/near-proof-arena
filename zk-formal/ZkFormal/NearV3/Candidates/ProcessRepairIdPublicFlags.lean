import ZkFormal.NearV3.Candidates.ProcessRepairIdPublicReceiver
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdPublicFlags
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorRoutedIdBound ProcPriorRoutedFamilyId
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
def verticalRead:Interaction:=ProcPriorVertical4Linear.interaction 1 ((ProcPriorIdTable.interactions 70 71 72 69)[0]!)
theorem flags {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) (hr:r<tr.height t)
    (hm:verticalRead.multNat tr t r pub≠0) :
    cv tr t r (ProcPriorVertical4Linear.stage 1)=1 ∧ cv tr t r ProcPriorIdTable.act=1 ∧ cv tr t r ProcPriorIdTable.isPublic=1 := by
  open ZkFormal.Chacha.Table.E in
  have hg:(Expr.mul (c (ProcPriorVertical4Linear.stage 1))
      (.mul (c ProcPriorIdTable.act) (c ProcPriorIdTable.isPublic))).eval tr t r pub=1 := by
    by_cases he:(Expr.mul (c (ProcPriorVertical4Linear.stage 1))
      (.mul (c ProcPriorIdTable.act) (c ProcPriorIdTable.isPublic))).eval tr t r pub=1
    · exact he
    · have heq:verticalRead.mult=[Expr.mul (c (ProcPriorVertical4Linear.stage 1))
          (.mul (c ProcPriorIdTable.act) (c ProcPriorIdTable.isPublic))] := rfl
      simp only [Interaction.multNat,heq,Interaction.multNat.go,he,ite_false,Nat.zero_add] at hm
      exact (hm rfl).elim
  have hsbit:=hL.bool hr (ProcPriorVerticalMemorySound.window_member
    (Table.boolC (ProcPriorVertical4Linear.stage 1)) (by simp [ProcPriorVertical4Linear.windows]))
  change tr.cell t r (ProcPriorVertical4Linear.stage 1)*(tr.cell t r ProcPriorIdTable.act*tr.cell t r ProcPriorIdTable.isPublic)=1 at hg
  have hc (x : Nat) :tr.cell t r x=Fp.ofNat (cv tr t r x):=(Fp.ofNat_toNat _).symm
  have hs:cv tr t r (ProcPriorVertical4Linear.stage 1)=1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hz|hz
    · rw [hc _,hz] at hg
      have hn:(0:Fp)≠1:=by decide +kernel
      exact (hn (by change (0:Fp)*_=1 at hg;grind only)).elim
    · exact hz
  have he:=ProcPriorVerticalIdRows.component_value hL hr hs (Table.boolC ProcPriorIdTable.act)
    (by simp [ProcPriorIdTable.constraints])
  have hb:cv tr t r ProcPriorIdTable.act≤1:=Codec.bool_of_eval (pub:=pub) he
  have ha:cv tr t r ProcPriorIdTable.act=1:=by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hz|hz
    · rw [hc ProcPriorIdTable.act,hz] at hg
      have hn:(0:Fp)≠1:=by decide +kernel
      exact (hn (by change _*((0:Fp)*_)=1 at hg;grind only)).elim
    · exact hz
  have hp:tr.cell t r ProcPriorIdTable.isPublic=(1:Fp):=by
    rw [hc (ProcPriorVertical4Linear.stage 1),hs,hc ProcPriorIdTable.act,ha] at hg
    change (1:Fp)*((1:Fp)*tr.cell t r ProcPriorIdTable.isPublic)=1 at hg
    grind only
  exact ⟨hs,ha,congrArg Fp.toNat hp⟩

end ZkFormal.NearV3.Candidates.ProcessRepairIdPublicFlags
