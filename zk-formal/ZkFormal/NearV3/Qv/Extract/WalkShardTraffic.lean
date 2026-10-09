import ZkFormal.NearV3.Qv.Extract.ShardAggregate

set_option maxRecDepth 2048

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
include hL

/-- Walk rows use the raw parser phase, so cannot forge parser shard sends. -/
theorem walk_shard_silent {r : Nat} (hr : r<tr.height tt)
    (hw : tr.cell tt r Candidates.CombinedTable.walk=1) :
    rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH true=[] := by
  have ha := con hL hr (e:=eqG (c Candidates.CombinedTable.walk) (c act) (k 1))
    (by simp [Candidates.CombinedTable.constraints])
  have hm := con hL hr (e:=eqG (c Candidates.CombinedTable.walk) (c mRaw) (k 1))
    (by simp [Candidates.CombinedTable.constraints])
  simp only [eval_eqG,eval_c,eval_k,hw] at ha hm
  have ha' : tr.cell tt r act=1 := by grind
  have hm' : tr.cell tt r mRaw=1 := by grind
  have hsum := con hL hr (Candidates.CombinedTable.parser_constraint_mem
    (e:=sub (sum (phases.map c)) (c act)) (by simp [constraints]))
  have he : RcptProof.fsum (tr.cell tt r) phases=tr.cell tt r act := by
    simp [sub,sum,phases,c,Candidates.CombinedTable.parserExpr,act,header,shard,firstIndex,nextIndex,mRaw,len,
      Expr.eval,Expr.evalWith,rowEnv] at hsum
    simp [RcptProof.fsum,phases,act,header,shard,firstIndex,nextIndex,mRaw]
    grind
  have hbool : ∀ x∈phases, tr.cell tt r x=0 ∨ tr.cell tt r x=1 := by
    intro x hx
    have hh := con hL hr (Candidates.CombinedTable.parser_constraint_mem
      (e:=Dsl.bool (c x)) (by
        have hx' : x∈([act,vf,vl,vz,gb,cont] ++ modes ++ [header,shard,firstIndex,nextIndex] ++ selectors) := by
          simp only [phases,List.mem_cons,List.not_mem_nil,or_false] at hx
          rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp [modes]
        have hmem := List.mem_map_of_mem (f:=fun x => Dsl.bool (c x)) hx'
        unfold constraints
        simp only [List.mem_append,hmem,true_or]))
    have hxlen : x≠len := by
      simp only [phases,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl <;> decide
    simp [Dsl.bool,sub,k,c,Candidates.CombinedTable.parserExpr,hxlen,Expr.eval,Expr.evalWith,rowEnv] at hh
    apply bool_cases
    grind
  have hot := RcptProof.oneHot_of (tr.cell tt r) phases (by decide) (tr.cell tt r act)
    hbool (Or.inr ha') he (by simp [phases] : mRaw∈phases) hm'
  have hh := hot.2 header (by simp [phases]) (by decide)
  have hs := hot.2 shard (by simp [phases]) (by decide)
  have hz : (0:Fp)*tr.cell tt r (sel 3)≠1 := by grind
  simp [rowTraffic,Candidates.CombinedTable.interactions,send,recv,B_QVC,B_VBYTES,B_QSH,
    B_FINAL,B_KEYNIB,Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,
    headerEnd,eval_c,eval_mul,hh,hs,hz]

/-- The entire walk prefix is silent on the sending side of QSH. -/
theorem walk_shard_prefix_silent (q : WalkChain tr tt) :
    (List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH true)=[] := by
  have hrange := range'_segs q.segs 0 q.consecutive
  simp only [Nat.sub_zero] at hrange
  rw [List.range_eq_range',hrange,List.flatMap_assoc]
  apply List.flatMap_eq_nil_iff.mpr
  intro p hp
  apply List.flatMap_eq_nil_iff.mpr
  intro r hr
  obtain ⟨i,hi,he⟩ := List.mem_range'.mp hr
  simp only [Nat.one_mul] at he
  have hb := seg_le_end q.segs 0 q.consecutive p hp
  have hw : tr.cell tt r Candidates.CombinedTable.walk=1 := by
    simpa only [isOne,decide_eq_true_eq] using (q.valid p hp).2.2.2.1 r (by omega) (by omega)
  exact walk_shard_silent hL (by have := q.fits; omega) hw

/-- Full-table QSH sends come exclusively from the parser suffix. -/
theorem shard_sends_suffix (q : WalkChain tr tt) :
    (List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH true)=
    (List.range' (segEnd 0 q.segs) (tr.height tt-segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH true) := by
  have he : List.range (tr.height tt)=List.range (segEnd 0 q.segs) ++
      List.range' (segEnd 0 q.segs) (tr.height tt-segEnd 0 q.segs) := by
    simpa only [List.range_eq_range'] using range'_split (segEnd 0 q.segs) (tr.height tt) q.fits
  rw [he,List.flatMap_append,walk_shard_prefix_silent hL q,List.nil_append]

/-- Full-table QSH receives come exclusively from the walk prefix. -/
theorem shard_receives_prefix (q : WalkChain tr tt) :
    (List.range (tr.height tt)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH false)=
    (List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH false) := by
  have he : List.range (tr.height tt)=List.range (segEnd 0 q.segs) ++
      List.range' (segEnd 0 q.segs) (tr.height tt-segEnd 0 q.segs) := by
    simpa only [List.range_eq_range'] using range'_split (segEnd 0 q.segs) (tr.height tt) q.fits
  rw [he,List.flatMap_append,parser_shard_receives hL q,List.append_nil]

end ZkFormal.NearV3.Qv.Extract
