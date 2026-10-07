import ZkFormal.NearV3.Qv.Candidates.NaturalBits
import ZkFormal.NearV3.Qv.Candidates.RecordList

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra

theorem records_nat_bits (vs : List Record) (r : Nat) :
    ∀ i ∈ ValueTable.interactions, ∀ b ∈ i.mult,
      rowNatEval ((recordsRows vs).getD r []) b≤1 := by
  by_cases hr : r<(recordsRows vs).length
  · have hm : (recordsRows vs).getD r [] ∈ recordsRows vs := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hr]
    obtain ⟨v,_,hrow⟩ := List.mem_flatMap.mp hm
    obtain ⟨cfg,pos,byte,phase,subpos,entry,regs,he⟩ := v.rows_form _ hrow
    rw [he]
    exact parser_nat_bits_row cfg pos byte phase subpos entry regs
  · have hp : (recordsRows vs).length≤r := by omega
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none hp,Option.getD_none]
    exact parser_nat_bits_zero

theorem records_rowTraffic (vs : List Record) (log r : Nat) (pub : List Fp)
    (bus : Nat) (sd : Bool) :
    rowTraffic ValueTable.interactions (recordsTrace vs log) 0 r pub bus sd =
      (natRowTraffic ValueTable.interactions ((recordsRows vs).getD r []) bus sd).map Msg.toFp := by
  apply rowTraffic_nat _ _ _ _ _ _ (by intro c; rfl)
  intro i hi
  have h := List.all_eq_true.mp interaction_nat_fragment i hi
  simp only [Bool.and_eq_true] at h
  exact ⟨fun b hb => ⟨List.all_eq_true.mp h.1 b hb,records_nat_bits vs r i hi b hb⟩,
    fun e he => List.all_eq_true.mp h.2 e he⟩

theorem natRowTraffic_zero (bus : Nat) (sd : Bool) :
    natRowTraffic ValueTable.interactions [] bus sd=[] := by
  simp [natRowTraffic,ValueTable.interactions,ZkFormal.Near.Dsl.send,ZkFormal.Near.Dsl.recv,
    natMultBits,rowNatEval,ZkFormal.Near.Dsl.c,ValueTable.headerEnd]

theorem flatMap_getD_range {α β : Type} (d : α) (xs : List α) (f : α → List β) :
    (List.range xs.length).flatMap (fun i => f (xs.getD i d))=xs.flatMap f := by
  have hm : (List.range xs.length).map (fun i => xs.getD i d)=xs := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h2]
  rw [← List.flatMap_map,hm]

theorem flatMap_getD_padded {α β : Type} (d : α) (xs : List α) (f : α → List β)
    (hd : f d=[]) (height : Nat) (hh : xs.length≤height) :
    (List.range height).flatMap (fun i => f (xs.getD i d))=xs.flatMap f := by
  rw [show height=xs.length+(height-xs.length) by omega,List.range_add,List.flatMap_append,
    flatMap_getD_range,List.flatMap_map]
  have hp : ∀ i, xs.getD (xs.length+i) d=d := by
    intro i
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : xs.length≤xs.length+i)]
  simp [hp,hd]

def recordsTraffic (vs : List Record) : Traffic where
  sends := fun bus => (recordsRows vs).flatMap (fun row => natRowTraffic ValueTable.interactions row bus true)
  recvs := fun bus => (recordsRows vs).flatMap (fun row => natRowTraffic ValueTable.interactions row bus false)

/-- Exact whole-table traffic as the modular image of generated natural messages.
This does not assume native queue ownership or global bus balance. -/
theorem records_field_traffic (vs : List Record) (log : Nat) (pub : List Fp)
    (hb : (recordsRows vs).length≤2^log) :
    TableTraffic ValueTable.interactions (recordsTrace vs log) 0 pub (recordsTraffic vs) := by
  have hrows (bus : Nat) (sd : Bool) :
      (List.range (2^log)).flatMap (fun r =>
        rowTraffic ValueTable.interactions (recordsTrace vs log) 0 r pub bus sd) =
      ((recordsRows vs).flatMap (fun row =>
        natRowTraffic ValueTable.interactions row bus sd)).map Msg.toFp := by
    simp only [records_rowTraffic]
    rw [← List.map_flatMap,flatMap_getD_padded [] (recordsRows vs)
      (fun row => natRowTraffic ValueTable.interactions row bus sd)
      (natRowTraffic_zero bus sd) (2^log) hb]
  intro bus msg
  rw [tableBusCount_eq,tableBusCount_eq]
  change ((List.range (2^log)).flatMap _).count msg = _ ∧
    ((List.range (2^log)).flatMap _).count msg = _
  rw [hrows,hrows]
  exact ⟨rfl,rfl⟩

end ZkFormal.NearV3.Qv.Candidates.ValueGen
