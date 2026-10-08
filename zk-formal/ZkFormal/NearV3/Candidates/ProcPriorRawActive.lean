import ZkFormal.NearV3.Candidates.ProcPriorRawHashEnd
namespace ZkFormal.NearV3.Candidates.ProcPriorRawActive
open ZkFormal.Air ZkFormal.Algebra NearSpec.Bandwidth
open ProcPriorCells ProcPriorRawGen

theorem active_constraints (st : State) (vid i : Nat) (present : Bool)
    (hn : st.links.length < 16777216) (hp : present=false → st=State.initial)
    (hi : i < ProcPriorRawSlots.length st.links.length)
    (e : Expr) (he : e ∈ ProcPriorRawFrame.constraints) :
    e.evalWith (env ((trace st vid present).cell 0 i)
      ((trace st vid present).cell 0 (i+1)) (bit (decide (i=0))) 0 1)=0 := by
  have hpc : present=false → st.links.length=0 := by
    intro h; rw [hp h]; rfl
  rcases ProcPriorRawSlots.coverage st.links.length i hi with
    ⟨g,hg,hi,hs⟩ | ⟨j,g,hj,hg,hi,hs⟩ | ⟨g,hg,hi,hs⟩
  · subst i
    by_cases h0:g=0
    · subst g
      simpa [trace,hs,ProcPriorRawSlots.header_next st.links.length 0 (by omega),
        decide_true,bit] using ProcPriorRawStart.start_constraints st vid present hn hpc e he
    · by_cases h4:g=4
      · subst g
        simpa [trace,hs,ProcPriorRawSlots.header_end,
          ProcPriorRawHeaderEnd.afterHeader,bit,decide_false] using
          ProcPriorRawHeaderEnd.end_constraints st vid present hn hpc e he
      · simpa [trace,hs,ProcPriorRawSlots.header_next st.links.length g (by omega),
          h0,decide_false,bit] using
          ProcPriorRawHeaderInner.inner_constraints st vid g present (by omega) hn hpc e he
  · subst i
    have h0 : ¬5+24*j+g=0 := by omega
    by_cases h23:g=23
    · subst g
      simpa [trace,hs,ProcPriorRawSlots.record_end _ _ hj,
        ProcPriorRawRecordEnd.afterRecord,h0,decide_false,bit] using
        ProcPriorRawRecordEnd.end_constraints st vid j present hj hn hpc e he
    · simpa [trace,hs,ProcPriorRawSlots.record_next st.links.length j g hj (by omega),
        h0,decide_false,bit] using
        ProcPriorRawRecordInner.inner_constraints st vid j g present hj (by omega) hn hpc e he
  · subst i
    have h0 : ¬5+24*st.links.length+g=0 := by omega
    by_cases h31:g=31
    · subst g
      simpa [trace,hs,ProcPriorRawSlots.hash_end,padding_cells,
        h0,decide_false,bit] using
        ProcPriorRawHashEnd.end_constraints st vid present hn hp e he
    · simpa [trace,hs,ProcPriorRawSlots.hash_next st.links.length g (by omega),
        h0,decide_false,bit] using
        ProcPriorRawHashInner.inner_constraints st vid g present (by omega) hn hp e he

end ZkFormal.NearV3.Candidates.ProcPriorRawActive
