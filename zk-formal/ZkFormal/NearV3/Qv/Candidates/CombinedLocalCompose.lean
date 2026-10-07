import ZkFormal.NearV3.Qv.Candidates.CombinedTraceNeighbors

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl NearSpec
open CombinedTable
variable {F : Type} [Lean.Grind.CommRing F]

/- Composition interface. The physical-prefix theorem discharges the boundary
and neighbor groups; no soundness conclusion follows from this lemma alone. -/
set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem plan_row_all_constraints
    (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve) (hv : v.Valid)
    (w : Walk) (hw : w ∈ plan pre v pres resolve) (pos : Nat) (b : UInt8)
    (tr : Trace F) (t r : Nat) (pub : List F)
    (hc : ∀ c, tr.cell t r c = @Nat.cast F Lean.Grind.Semiring.natCast ((w.row pos b).getD c 0))
    (hb : pos=0 → b=w.kind.bytes.headD 0)
    (hn : tr.cell t ((r+1)%tr.height t) ValueTable.act=0 ∨
      tr.cell t ((r+1)%tr.height t) ValueTable.vf=1)
    (hpub : kPublic.eval tr t r pub = @Nat.cast F Lean.Grind.Semiring.natCast pres.length)
    (hfirst : ∀ e ∈ firstConstraints,e.eval tr t r pub=0)
    (hlast : (mul3 .isLast (c walk) (Dsl.not (c wend))).eval tr t r pub=0)
    (hexit : (mul3 .isTransition (c wend) (n walk)).eval tr t r pub=0)
    (hneighbor : ∀ e ∈ insideConstraints ++ startConstraints ++ stepConstraints,e.eval tr t r pub=0) :
    ∀ e ∈ table.allConstraints,e.eval tr t r pub=0 := by
  have hbase := w.base_constraints pos b tr t r pub hc hn
  have hflag := w.flag_constraints pos b tr t r pub hc
  have hinactive := w.inactive_gate_zero pos b tr t r pub hc
  have hbits := w.byte_bit_constraints pos b tr t r pub hc
  have hread := w.read_gate_constraints pos b tr t r pub hc
  have hbyte := w.byte_equation pos b tr t r pub hc
  have hmode := w.mode_equation pos b tr t r pub hc
  have hpos := w.last_position_equation pos b tr t r pub hc
  have hstart := w.first_byte_equation pos b tr t r pub hc hb
  have hmeta := plan_metadata_equations pre v pres resolve w hw pos b tr t r pub hc
  have hcount := plan_last_count_equation pre v pres resolve w hw pos b tr t r pub hc
  have hend := plan_end_main_equation pre v pres resolve w hw pos b tr t r pub hc
  have habsent := plan_absent_buffer_equation pre v pres resolve hv w hw pos b tr t r pub hc
  have hterm := plan_public_termination pre v pres resolve w hw pos b tr t r pub hc hpub
  have hrestart := w.no_restart_equation pos b tr t r pub hc
  have hmult := w.table_bit_constraints pos b tr t r pub hc
  have hbody : ∀ e ∈ constraints,e.eval tr t r pub=0 := by
    simp only [constraints,List.forall_mem_append,List.forall_mem_map]
    refine ⟨⟨⟨⟨⟨hbase,hflag⟩,fun x _ => hinactive x⟩,fun i hi => hbits i (List.mem_range.mp hi)⟩,?_⟩,?_⟩
    · simp only [readGateConstraints,metadataConstraints,firstConstraints,insideConstraints,
        startConstraints,stepConstraints,mainStepConstraints,List.forall_mem_append,
        List.forall_mem_map,List.forall_mem_cons,List.forall_mem_nil,and_true] at hread hmeta hfirst hneighbor
      simp_all only [List.forall_mem_cons,List.forall_mem_nil,and_true]
      simp
    · intro x hx
      exact hneighbor _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.mpr ⟨x,hx,rfl⟩))))
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hbody e he
  · exact hmult e he

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
