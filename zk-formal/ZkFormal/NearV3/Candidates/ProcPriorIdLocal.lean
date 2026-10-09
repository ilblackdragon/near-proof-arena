import ZkFormal.NearV3.Candidates.ProcPriorIdTraceConstraints
namespace ZkFormal.NearV3.Candidates.ProcPriorIdLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpec.Bandwidth ZkFormal.NearV3.Sched
open ProcPriorIdRows ProcPriorCells ProcPriorIdTrace

theorem bits (xs : List Row) (t tt j : Nat) (pub : List Fp)
    (pb qb rb cb : Nat) (i : Interaction) (hi:i∈ProcPriorIdTable.interactions pb qb rb cb)
    (e : Expr) (he:e∈i.mult) :
    e.eval (trace xs t) tt j pub=0 ∨ e.eval (trace xs t) tt j pub=1 := by
  have hpub:e.pubBound=0:=bounds pb qb rb cb e (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_left _ he⟩))
  rw [row_eval xs t tt j pub e hpub]
  cases ha:xs[j]? with
  | none =>
    rw [cells_none xs t j ha]
    exact Or.inl (ProcPriorIdBits.padding_bits _ _ _ _ pb qb rb cb i hi e he)
  | some a =>
    rw [cells_some xs t j a ha]
    apply ProcPriorIdBits.active_bits a (xs[j+1]?) t _ _ _ _ _ pb qb rb cb i hi e he
    cases hb:xs[(j+1)%2^22]? with
    | none => rw [cells_none xs t _ hb]; exact Or.inl rfl
    | some b => rw [cells_some xs t _ b hb]; exact Or.inr rfl

theorem native_local (ids : List Nat) (rs : List LinkAllowance)
    (hi:∀id∈ids,id<2^64) (hr:∀r∈rs,LinkOk r)
    (hc:(rows ids rs).length<2^22) (t tt pb qb rb cb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorIdTable.table pb qb rb cb) (trace (rows ids rs) t) tt pub := by
  refine ⟨by change 1≤22; decide +kernel,by change 22≤22; decide +kernel,?_,?_⟩
  · intro j hj e he
    exact ProcPriorIdTraceConstraints.constraints ids rs hi hr hc t tt j hj pub e he
  · intro j hj i hi e he
    exact bits (rows ids rs) t tt j pub pb qb rb cb i hi e he

/-- Successful decoding discharges every original key and row bound; duplicate
public IDs and arbitrary original record order remain admitted. -/
theorem decoded_local (ids : List Nat) (bytes : Bytes) (st : State)
    (hd:State.decode bytes=some st) (hi:∀id∈ids,id<2^64) (hn:ids.length≤64)
    (hb:bytes.length≤2000000) (t tt pb qb rb cb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorIdTable.table pb qb rb cb) (trace (rows ids st.links) t) tt pub := by
  apply native_local ids st.links hi (ProcPriorDecode.decode_exact bytes st hd).2.1
  rw [rows_length]
  have hh:=ProcPriorDecode.decode_length bytes st hd
  omega

end ZkFormal.NearV3.Candidates.ProcPriorIdLocal
