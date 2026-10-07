import ZkFormal.NearV3.Qv.Candidates.NaturalTraffic
import ZkFormal.NearV3.Qv.Candidates.Records

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Air ZkFormal.Near.Dsl

def RowForm (cells : List Nat) : Prop :=
  ∃ cfg pos byte phase subpos entry regs, cells=row cfg pos byte phase subpos entry regs

theorem wordRows_form (cfg : Config) (offset phase entry : Nat) (bytes regs : Bytes) :
    ∀ cells ∈ wordRows cfg offset phase entry bytes regs, RowForm cells := by
  intro cells hc
  obtain ⟨⟨b,i⟩,hi,rfl⟩ := List.mem_map.mp hc
  exact ⟨cfg,offset+i,b.toNat,phase,i,entry,regs,rfl⟩

theorem Record.rows_form (v : Record) : ∀ cells ∈ v.rows, RowForm cells := by
  cases v with
  | mk vid tau users p =>
    cases p with
    | empty index =>
      intro cells hc
      rcases List.mem_append.mp hc with h | h
      · exact wordRows_form _ _ _ _ _ _ cells h
      · exact wordRows_form _ _ _ _ _ _ cells h
    | buffer es =>
      intro cells hc
      rcases List.mem_append.mp hc with h | h
      · exact wordRows_form _ _ _ _ _ _ cells h
      · obtain ⟨⟨e,i⟩,_,he⟩ := List.mem_flatMap.mp h
        rcases List.mem_append.mp he with h | h
        · rcases List.mem_append.mp h with h | h
          · exact wordRows_form _ _ _ _ _ _ cells h
          · exact wordRows_form _ _ _ _ _ _ cells h
        · exact wordRows_form _ _ _ _ _ _ cells h
    | raw bytes =>
      intro cells hc
      change cells ∈ rawRows vid tau users bytes at hc
      unfold rawRows at hc
      split at hc
      · simp only [List.mem_singleton] at hc
        exact ⟨_,0,0,4,0,0,[],hc⟩
      · obtain ⟨⟨b,i⟩,_,rfl⟩ := List.mem_map.mp hc
        exact ⟨_,i,b.toNat,4,0,0,[],rfl⟩

theorem parser_nat_bits_row (cfg : Config) (pos byte phase subpos entry : Nat) (regs : Bytes) :
    ∀ i ∈ ValueTable.interactions, ∀ b ∈ i.mult,
      rowNatEval (row cfg pos byte phase subpos entry regs) b≤1 := by
  have hb (b : Bool) : b.toNat≤1 := by cases b <;> decide
  have hm (a b : Bool) : a.toNat*b.toNat≤1 := by cases a <;> cases b <;> decide
  simp [ValueTable.interactions,send,recv,rowNatEval,c,ValueTable.headerEnd,
    ValueTable.gb,ValueTable.vf,ValueTable.shard,ValueTable.header,ValueTable.sel,hb,hm]

theorem parser_nat_bits_zero :
    ∀ i ∈ ValueTable.interactions, ∀ b ∈ i.mult, rowNatEval [] b≤1 := by
  simp [ValueTable.interactions,send,recv,rowNatEval,c,ValueTable.headerEnd,
    ValueTable.gb,ValueTable.vf,ValueTable.shard,ValueTable.header,ValueTable.sel]

end ZkFormal.NearV3.Qv.Candidates.ValueGen
