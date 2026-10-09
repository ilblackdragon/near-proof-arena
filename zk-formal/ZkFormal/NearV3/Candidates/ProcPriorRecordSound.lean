import ZkFormal.NearV3.Candidates.ProcPriorRoutedFamilyWrite
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordSound
open ZkFormal.V2 ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorRecordTable
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

theorem component_value (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (e : Expr) (he:e∈constraints) :
    (ProcPriorVertical4Linear.expression e).eval tr t r pub=0 := by
  have hm:.mul (c (ProcPriorVertical4Linear.stage 3)) (ProcPriorVertical4Linear.expression e)∈
      ProcPriorVertical4Linear.table.constraints := by
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨(ProcPriorRecordLinear.table 75 71 72 67 76,3),by simp [ProcPriorVertical4Linear.components,List.zipIdx],?_⟩
    exact List.mem_map.mpr ⟨e,he,rfl⟩
  have hh:=hL r hr _ hm
  have hc:tr.cell t r (ProcPriorVertical4Linear.stage 3)=(1:Fp) := by
    change tr.cell t r (ProcPriorVertical4Linear.stage 3)=Fp.ofNat 1
    rw [←hs];exact (Fp.ofNat_toNat _).symm
  change tr.cell t r (ProcPriorVertical4Linear.stage 3)*(ProcPriorVertical4Linear.expression e).eval tr t r pub=0 at hh
  rw [hc] at hh
  grind only

theorem flag (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (x : Nat) (hx:x∈[act,sender,receiver,amount,firstLimb,midLimb,topLimb,senderFound,receiverFound,big,writeGate]) :
    cv tr t r x≤1 := by
  have hh:=component_value hL hr hs (Table.boolC x)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩))))
  exact Codec.bool_of_eval (pub:=pub) hh

/-- A physical Record write requires both IDs to have been found and is
emitted at the amount's final limb. These flags are derived from constraints. -/
theorem write_flags (hL:ProcPriorVerticalMemorySound.LocalV tr t pub)
    (hr:r<tr.height t) (hs:cv tr t r (ProcPriorVertical4Linear.stage 3)=1)
    (hw:cv tr t r writeGate=1) :
    cv tr t r amount=1 ∧ cv tr t r topLimb=1 ∧
      cv tr t r senderFound=1 ∧ cv tr t r receiverFound=1 := by
  have ha:=flag hL hr hs amount (by simp)
  have ht:=flag hL hr hs topLimb (by simp)
  have hsf:=flag hL hr hs senderFound (by simp)
  have hrf:=flag hL hr hs receiverFound (by simp)
  have he:=component_value hL hr hs
    (sub (c writeGate) (.mul (.mul (.mul (c amount) (c topLimb)) (c senderFound)) (c receiverFound)))
    (by simp [constraints])
  change tr.cell t r writeGate + -(tr.cell t r amount*tr.cell t r topLimb*tr.cell t r senderFound*tr.cell t r receiverFound)=0 at he
  have hc (x : Nat) :tr.cell t r x=Fp.ofNat (cv tr t r x):=(Fp.ofNat_toNat _).symm
  rw [hc writeGate,hc amount,hc topLimb,hc senderFound,hc receiverFound,hw] at he
  have hz:(Fp.ofNat 1 + -Fp.ofNat 0 : Fp)≠0 := by decide +kernel
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with ha|ha <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with ht|ht <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsf with hsf|hsf <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hrf with hrf|hrf <;>
    simp_all
/-- The write flags above hold for the actual Record supplier of every live
prior-memory write receiver in the repaired routed family. -/
theorem physical_write_flags {AP : AirP} {tr : Trace Fp} {pub : List Fp}
    (hH:HoldsP AP pub tr)
    (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀msg,pubCount AP pub 67 true msg=0)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hb:i.bus=67) (hs:i.send=false)
    (hm:i.multNat tr tc r pub≠0) :
    ∃q,q<tr.height 0 ∧
      let projected:=HorizontalTrace.project ProcPriorRoutedFamilyWrite.offset tr
      cv projected 0 q amount=1 ∧ cv projected 0 q topLimb=1 ∧
      cv projected 0 q senderFound=1 ∧ cv projected 0 q receiverFound=1 ∧
      ProcPriorRoutedFamilyWrite.verticalWrite.msgVal projected 0 q pub=i.msgVal tr tc r pub := by
  obtain ⟨q,hq,hstage,hgate,hmsg,_⟩:=ProcPriorRoutedFamilyWrite.family_write_source hH htables hpub ht hr hi hb hs hm
  have ht0:0<AP.tables.length := by rw [htables];decide +kernel
  have hL:=local_of_holdsP hH ht0
  rw [htables] at hL
  have hv:=ProcPriorRoutedFamilyWrite.projected_local hL
  obtain ⟨ha,htop,hfound,hrfound⟩:=write_flags hv hq hstage hgate
  exact ⟨q,hq,ha,htop,hfound,hrfound,hmsg⟩
end ZkFormal.NearV3.Candidates.ProcPriorRecordSound
