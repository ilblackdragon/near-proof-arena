import ZkFormal.NearV3.Candidates.ProcPriorOverlayComponentRows
namespace ZkFormal.NearV3.Candidates.ProcPriorOverlayLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcPriorVertical4Linear ProcPriorVertical4Clock ProcPriorVertical4ClockCases
open ProcPriorOverlayCuts ProcPriorOverlayGeometry

theorem stage_cell (bs : List NativeBlock) (source : Nat→Trace Fp) (t r i : Nat) (hi:i<4) :
    (c (stage i)).eval (trace bs (fun n=>(source n).cell 0)) t r []=
      if i=stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r then 1 else 0 := by
  simp [Expr.eval,Expr.evalWith,rowEnv,c,trace,ProcPriorVertical4ClockTrace.trace,cell,stage,
    show ¬23+i<23 by omega,show 23+i<27 by omega,flag]

theorem stage_eval (bs : List NativeBlock) (source : Nat→Trace Fp) (t r i : Nat) (hi:i<4) (pub : List Fp) :
    (c (stage i)).eval (trace bs (fun n=>(source n).cell 0)) t r pub=
      if i=stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r then 1 else 0 :=
  stage_cell bs source t r i hi

/-- Honest component witnesses are installed at shorter windows only after
proving their zero suffixes and one-row padding space. The marker, component
constraints, multiplicity bits and physical stage boundaries are all checked. -/
theorem local_table (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (hlen:bs.length≤32) (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184)
    (source : Nat→Trace Fp) (used : Nat→Nat)
    (hs:∀T i,(T,i)∈components.zipIdx→(source i).log 0=22 ∧
      TableLocal T (source i) 0 [] ∧ used i<stop bs i-start bs i ∧
      ∀j,used i≤j→(source i).cell 0 j=fun _=>0)
    (t : Nat) (pub : List Fp) :
    TableLocal table (trace bs (fun n=>(source n).cell 0)) t pub := by
  have hh:=cuts bs hn hlen hraw
  have hc:0<cutMemory bs ∧ cutMemory bs<cutIds bs ∧ cutIds bs<cutRaw bs ∧ cutRaw bs<2^22:=
    ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
  have pair (T : Air.Table) (i : Nat) (hi:(T,i)∈components.zipIdx) : T∈components ∧ i<4 := by
    have hg:=List.mk_mem_zipIdx_iff_getElem?.mp hi
    exact ⟨List.mem_of_getElem? hg,by have :=(List.getElem?_eq_some_iff.mp hg).1;change i<4 at this;exact this⟩
  refine ⟨by change 1≤22;decide,by change 22≤22;decide,?_,?_⟩
  · intro r hr e he
    rcases List.mem_append.mp he with hw|he
    · exact windows bs hn hlen hraw _ t r hr pub e hw
    · obtain ⟨⟨T,i⟩,hi,he⟩:=List.mem_flatMap.mp he
      obtain ⟨q,hq,rfl⟩:=List.mem_map.mp he
      obtain ⟨hlog,hloc,hused,hzero⟩:=hs T i hi
      have hpair:=pair T i hi
      simp only [eval_mul]
      rw [stage_eval bs source t r i hpair.2 pub]
      by_cases ha:i=stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r
      · rw [ite_eq_left ha,ProcPriorOverlayComponentRows.current bs hc source i T hpair.1 hlog hloc
          (used i) hused hzero r t hr ha.symm pub q hq]
        grind
      · rw [ite_eq_right ha]
        grind
  · intro r hr a ha e he
    obtain ⟨⟨T,i⟩,hi,ha⟩:=List.mem_flatMap.mp ha
    change a∈T.interactions.map (interaction i) at ha
    obtain ⟨a0,ha0,rfl⟩:=List.mem_map.mp ha
    change e∈a0.mult.map (fun q=>.mul (c (stage i)) (expression q)) at he
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp he
    obtain ⟨hlog,hloc,hused,hzero⟩:=hs T i hi
    have hpair:=pair T i hi
    simp only [eval_mul]
    rw [stage_eval bs source t r i hpair.2 pub]
    by_cases hact:i=stageAt (cutMemory bs) (cutIds bs) (cutRaw bs) r
    · rw [ite_eq_left hact]
      have hb:=ProcPriorOverlayComponentRows.bit bs hc source i T hpair.1 hlog hloc
        (used i) hused hzero r t hr hact.symm pub a0 ha0 q hq
      rcases hb with hb|hb <;> rw [hb] <;> grind
    · rw [ite_eq_right hact]
      left;grind
end ZkFormal.NearV3.Candidates.ProcPriorOverlayLocal
