import ZkFormal.NearV3.Assembly.RcptStateHeaderCarry

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

theorem planned_header_inputs (lists : List (List Input)) (p : ListPlan) (row : Coord)
    (hp : PlannedRow.header p row∈plannedRows lists) : p.inputs∈lists := by
  rw [←plannedSegments_rows] at hp
  obtain ⟨seg,hs,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨a,_,he⟩ := List.mem_map.mp hp
  cases seg with
  | receipt rp s => cases he
  | header lp =>
    cases he
    obtain ⟨lp,hl,hs⟩ := List.mem_flatMap.mp hs
    simp only [listSegments,List.mem_cons] at hs
    rcases hs with he|hs
    · cases he
      have hm : p.inputs∈(planLists 0 0 8 lists).map ListPlan.inputs := List.mem_map.mpr ⟨p,hl,rfl⟩
      rw [planLists_inputs lists 0 0 8] at hm
      exact hm
    · obtain ⟨rp,_,hs⟩ := List.mem_flatMap.mp hs
      obtain ⟨s,_,he⟩ := List.mem_map.mp hs
      cases he

set_option maxRecDepth 4096 in
theorem headerStream_count_bytes (own : Nat) (p : ListPlan) :
    (headerStream own p).getD 8 0=Fp.ofNat (p.inputs.length%256) ∧
    (headerStream own p).getD 9 0=Fp.ofNat ((p.inputs.length/256)%256) ∧
    (headerStream own p).getD 10 0=Fp.ofNat ((p.inputs.length/65536)%256) ∧
    (headerStream own p).getD 11 0=Fp.ofNat ((p.inputs.length/16777216)%256) := by
  simp [headerStream,u64,u32,leN,UInt8.toNat_ofNat,Nat.div_div_eq_div_mul]

theorem headerStream_count_small (own : Nat) (p : ListPlan) (hn : p.inputs.length<2^16) :
    Fp.ofNat p.inputs.length=(headerStream own p).getD 8 0+256*(headerStream own p).getD 9 0 ∧
    (headerStream own p).getD 10 0=0 ∧ (headerStream own p).getD 11 0=0 := by
  obtain ⟨hb0,hb1,hb2,hb3⟩ := headerStream_count_bytes own p
  rw [hb0,hb1,hb2,hb3]
  have hdiv : p.inputs.length/256<256 := by omega
  have hz2 : p.inputs.length/65536=0 := by omega
  have hz3 : p.inputs.length/16777216=0 := by omega
  simp only [Nat.mod_eq_of_lt hdiv,hz2,hz3,Nat.zero_mod]
  constructor
  · have he := Nat.mod_add_div p.inputs.length 256
    change (p.inputs.length:Fp)=((p.inputs.length%256:Nat):Fp)+256*((p.inputs.length/256:Nat):Fp)
    have hh := congrArg (fun n:Nat=>(n:Fp)) he
    grind only
  · exact ⟨rfl,rfl⟩

def headerCountConstraints : List Expr :=
  [mul3 (c sCL) (c fs) (sub (c nj) (.add (c (reg 8)) (smul 256 (c (reg 9))))),
   mul3 (c sCL) (c fs) (c (reg 10)),mul3 (c sCL) (c fs) (c (reg 11))]

theorem headerCountConstraints_in_states : ∀e∈headerCountConstraints,e∈cStates := by
  intro e he
  simp only [headerCountConstraints,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [cStates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
