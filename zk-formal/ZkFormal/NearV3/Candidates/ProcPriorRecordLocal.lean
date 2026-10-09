import ZkFormal.NearV3.Candidates.ProcPriorRecordBits
import ZkFormal.NearV3.Candidates.ProcPriorDecode
namespace ZkFormal.NearV3.Candidates.ProcPriorRecordLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpec.Bandwidth ZkFormal.NearV3.Sched
open ProcPriorCells ProcPriorRecordTrace

theorem bounds (rb qb ib wb pb : Nat) :
    ∀e∈(ProcPriorRecordLinear.table rb qb ib wb pb).exprs,e.pubBound=0 := by
  have h:((ProcPriorRecordLinear.table rb qb ib wb pb).exprs.all (fun e=>decide (e.pubBound=0)))=true := by
    change ((ProcPriorRecordLinear.table 0 0 0 0 0).exprs.all (fun e=>decide (e.pubBound=0)))=true
    decide +kernel
  exact fun e he=>of_decide_eq_true (List.all_eq_true.mp h e he)

theorem bits (ids : List Nat) (tau : Nat) (rs : List LinkAllowance)
    (tt p rb qb ib wb pb : Nat) (pub : List Fp) (i : Interaction)
    (hi:i∈ProcPriorRecordLinear.interactions rb qb ib wb pb) (e : Expr) (he:e∈i.mult) :
    e.eval (trace ids tau rs) tt p pub=0 ∨ e.eval (trace ids tau rs) tt p pub=1 := by
  have hpub:e.pubBound=0:=bounds rb qb ib wb pb e (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_left _ he⟩))
  rw [row_eval ids tau rs tt p pub e hpub]
  by_cases h0:p=0
  · subst p
    rw [header]
    exact ProcPriorRecordBits.header_bits ids tau _ _ _ _ rb qb ib wb pb i hi e he
  · have hcell:cells ids tau rs p=(match rs[(p-1)/9]? with
        | none=>fun _=>0
        | some r=>ProcPriorRecordCells.cell ids tau ⟨(p-1)/9,((p-1)%9)/3,(p-1)%3,r⟩):=by
      simp only [cells,h0,ite_false]; rfl
    rw [hcell]
    cases hr:rs[(p-1)/9]? with
    | none=>
      simp only [hr]
      exact Or.inl (ProcPriorRecordBits.padding_bits _ _ _ _ rb qb ib wb pb i hi e he)
    | some r=>
      simp only [hr]
      exact ProcPriorRecordBits.active_bits ids tau ((p-1)/9) (((p-1)%9)/3) ((p-1)%3) r
        (by omega) (by omega) _ _ _ _ rb qb ib wb pb i hi e he

theorem native_local (ids : List Nat) (rs : List LinkAllowance)
    (hr:∀r∈rs,LinkOk r) (hc:1+9*rs.length<2^22)
    (tt rb qb ib wb pb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorRecordLinear.table rb qb ib wb pb) (trace ids 0 rs) tt pub := by
  refine ⟨by change 1≤22; decide +kernel,by change 22≤22; decide +kernel,?_,?_⟩
  · intro p hp e he
    exact ProcPriorRecordConstraints.constraints ids rs hr hc tt p hp pub e he
  · intro p hp i hi e he
    exact bits ids 0 rs tt p rb qb ib wb pb pub i hi e he

/-- Original decoded records, including unmatched IDs and repetitions, populate
all three word/limb groups. The serialized input length supplies the row cap. -/
theorem decoded_local (ids : List Nat) (bytes : Bytes) (st : State)
    (hd:State.decode bytes=some st) (hb:bytes.length≤2000000)
    (tt rb qb ib wb pb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorRecordLinear.table rb qb ib wb pb) (trace ids 0 st.links) tt pub := by
  apply native_local ids st.links (ProcPriorDecode.decode_exact bytes st hd).2.1
  have hh:=ProcPriorDecode.decode_length bytes st hd
  omega

theorem empty_local (ids : List Nat) (tt rb qb ib wb pb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorRecordLinear.table rb qb ib wb pb) (trace ids 0 []) tt pub :=
  native_local ids [] (by simp) (by decide +kernel) tt rb qb ib wb pb pub
end ZkFormal.NearV3.Candidates.ProcPriorRecordLocal
