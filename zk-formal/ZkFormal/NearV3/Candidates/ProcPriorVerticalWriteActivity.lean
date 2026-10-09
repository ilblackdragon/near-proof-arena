import ZkFormal.NearV3.Candidates.ProcPriorVerticalReadSound
namespace ZkFormal.NearV3.Candidates.ProcPriorVerticalWriteActivity
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorVertical4Linear

def write:Interaction:=interaction 0 ((ProcPriorMemoryTable.interactions 67 68 69)[0]!)
theorem flags {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hL:ProcPriorVerticalMemorySound.LocalV tr t pub) (hr:r<tr.height t)
    (hm:write.multNat tr t r pub≠0) :
    cv tr t r (stage 0)=1 ∧ cv tr t r ProcPriorMemoryTable.act=1 ∧ cv tr t r ProcPriorMemoryTable.query=0 := by
  have hg:(Expr.mul (c (stage 0)) (.mul (c ProcPriorMemoryTable.act) (ProcPriorMemoryTable.notE (c ProcPriorMemoryTable.query)))).eval tr t r pub=1 := by
    by_cases he:(Expr.mul (c (stage 0)) (.mul (c ProcPriorMemoryTable.act) (ProcPriorMemoryTable.notE (c ProcPriorMemoryTable.query)))).eval tr t r pub=1
    · exact he
    · have heq:write.mult=[Expr.mul (c (stage 0)) (.mul (c ProcPriorMemoryTable.act) (ProcPriorMemoryTable.notE (c ProcPriorMemoryTable.query)))] := rfl
      simp only [Interaction.multNat,heq,Interaction.multNat.go,he,ite_false,Nat.zero_add] at hm
      exact (hm rfl).elim
  have hsbit:=hL.bool hr (ProcPriorVerticalMemorySound.window_member (Table.boolC (stage 0)) (by simp [windows]))
  have hzero (x : Nat) (hx:cv tr t r x=0) :tr.cell t r x=(0:Fp) := by
    change tr.cell t r x=Fp.ofNat 0
    rw [←hx];exact (Fp.ofNat_toNat _).symm
  change tr.cell t r (stage 0)*(tr.cell t r ProcPriorMemoryTable.act*(1 + -tr.cell t r ProcPriorMemoryTable.query))=1 at hg
  have hs:cv tr t r (stage 0)=1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsbit with hz|hz
    · rw [hzero _ hz] at hg
      have hf:(0:Fp)≠1 := by decide +kernel
      exact (hf (by grind only)).elim
    · exact hz
  have hb (x : Nat) (hx:x∈[ProcPriorMemoryTable.act,ProcPriorMemoryTable.query,ProcPriorMemoryTable.hi,ProcPriorMemoryTable.beforeHi,ProcPriorMemoryTable.same]) :cv tr t r x≤1 := by
    have hh:=ProcPriorVerticalMemorySound.component_value hL hr hs (Table.boolC x)
      (List.mem_append_left _ (List.mem_map.mpr ⟨x,hx,rfl⟩))
    change (Table.boolC x).eval tr t r pub=0 at hh
    exact Codec.bool_of_eval (pub:=pub) hh
  have ha:=hb ProcPriorMemoryTable.act (by simp)
  have hq:=hb ProcPriorMemoryTable.query (by simp)
  refine ⟨hs,?_,?_⟩
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with hz|hz
    · rw [hzero _ hz] at hg
      have hf:(0:Fp)≠1 := by decide +kernel
      exact (hf (by grind only)).elim
    · exact hz
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hq with hz|hz
    · exact hz
    · have hone:tr.cell t r ProcPriorMemoryTable.query=(1:Fp):=by
        change tr.cell t r ProcPriorMemoryTable.query=Fp.ofNat 1
        rw [←hz];exact (Fp.ofNat_toNat _).symm
      rw [hone] at hg
      have hf:(0:Fp)≠1:=by decide +kernel
      exact (hf (by grind only)).elim

end ZkFormal.NearV3.Candidates.ProcPriorVerticalWriteActivity
