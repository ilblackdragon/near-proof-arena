import ZkFormal.NearV3.Candidates.VerticalPriorFusion
import ZkFormal.NearV3.Candidates.InteractionPairingWf
import ZkFormal.NearV3.Candidates.HorizontalReceiptWf
namespace ZkFormal.NearV3.Candidates.VerticalPriorAdmission
open ZkFormal.Air ZkFormal.Size HorizontalProfile VerticalPriorFusion

/-- Structural candidate only. Buses67--73 have no global ownership proof yet;
parser/ID/Codec repairs and an actual complete execution remain outstanding. -/
def air : Air := ⟨tables,76,202⟩
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

private theorem widen (T : Air.Table) (A B : Air) (d : Nat)
    (hp : A.numPub=B.numPub) (hb : A.numBuses≤B.numBuses)
    (h : T.wf A d=true) : T.wf B d=true := by
  simp only [Table.wf,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h ⊢
  refine ⟨⟨⟨⟨?_,?_⟩,h.1.1.2⟩,h.1.2⟩,h.2⟩
  · intro e he
    exact ⟨(h.1.1.1.1 e he).1,hp ▸ (h.1.1.1.1 e he).2⟩
  · intro i hi
    exact ⟨Nat.lt_of_lt_of_le (h.1.1.1.2 i hi).1 hb,(h.1.1.1.2 i hi).2⟩

theorem table_wf : air.tables.all (fun T=>T.wf air 16)=true := by
  change (table::HorizontalAccounts.rest).all _=true
  rw [List.all_cons,Bool.and_eq_true]
  constructor
  · change ({raw with interactions:=InteractionPairing.reorder raw.interactions}:Air.Table).wf air 16=true
    rw [InteractionPairing.wf]
    apply HorizontalWf.fuse_wf
    intro T hT
    rcases List.mem_append.mp hT with ht|ht
    · have hT : T∈GatedLengthFusion.selected:=List.mem_of_mem_take ht
      rcases List.mem_or_eq_of_mem_set hT with hT|rfl
      · rcases List.mem_append.mp hT with hT|hT
        · rcases List.mem_append.mp hT with hT|hT
          · rcases List.mem_or_eq_of_mem_set hT with ho|rfl
            · have hh:=List.all_eq_true.mp PackedMerkleFamily.four_wf T (List.mem_filter.mp ho).1
              have hw : T.wf HorizontalReceipt.air 16=true := by
                simp only [Table.wf,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at hh ⊢
                exact ⟨⟨⟨⟨hh.1.1.1.1,hh.1.1.1.2⟩,by intro e he;have h:=hh.1.1.2 e he;omega⟩,hh.1.2⟩,hh.2⟩
              exact widen T HorizontalReceipt.air air 16 rfl (by decide) hw
            · decide +kernel
          · have ht : T=GatedMemoryFusion.memory:=List.mem_singleton.mp hT
            subst T
            decide +kernel
        · have ht : T=GatedIdFusion.memory:=List.mem_singleton.mp hT
          subst T
          decide +kernel
      · decide +kernel
    · have he : T=ProcPriorVertical.table:=List.mem_singleton.mp ht
      subst T
      decide +kernel
  · apply List.all_eq_true.mpr
    intro T hT
    exact widen T HorizontalAccounts.air air 16 rfl (by decide)
      (List.all_eq_true.mp HorizontalCertified.rest_wf T hT)

theorem mult_bound : air.multBound=992583684 := by
  unfold Air.multBound
  simp only [air,tables,List.map_cons,List.sum_cons,mult_weights]
  decide +kernel

theorem fp_bound : air.fpBound=57569853672 := by
  unfold Air.fpBound
  simp only [air,tables,List.map_cons,List.sum_cons,List.flatMap_cons,
    interaction_count,msg_lengths]
  decide +kernel

theorem air_wf : air.wf 16=true := by
  simp only [Air.wf,table_wf,mult_bound,fp_bound,busBudget]
  decide +kernel

theorem grouped_degree : air.tables.all (fun T=>decide (T.degree 2≤16))=true := by
  change (table::HorizontalAccounts.rest).all _=true
  rw [List.all_cons,VerticalPriorFusion.degree]
  decide +kernel

theorem header_max : ZkFormal.Stark.headerOk air (ZkFormal.V2.G.pg 2)
    (tables.map (·.maxLog))=true := by
  unfold ZkFormal.Stark.headerOk
  have hbl : 2^(ZkFormal.V2.G.pg 2).logBlowup=16 := rfl
  have hgr : (ZkFormal.V2.G.pg 2).auxGroup=2 := rfl
  simp only [hbl,hgr]
  rw [air_wf,grouped_degree]
  decide +kernel

theorem proof_bytes : sizeMaxDedup air (ZkFormal.V2.G.pg 2)=8378132 := by
  rw [sizeMaxDedup_eq_model]
  exact bytes_exact

theorem proof_bound : sizeMaxDedup air (ZkFormal.V2.G.pg 2)<8388608 := by
  rw [proof_bytes]
  decide

end ZkFormal.NearV3.Candidates.VerticalPriorAdmission
