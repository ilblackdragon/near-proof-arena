import ZkFormal.NearV3.Candidates.ProcRecordConcatActive
namespace ZkFormal.NearV3.Candidates.ProcRecordConcatLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest
open ProcRecordConcatTraffic ProcRecordConcatCells ProcRecordConcatGeometry ProcRecordConcatActive ProcPriorCells

theorem row_eval (ids : NativeBlock→List Nat) (bs : List NativeBlock) (t r : Nat) (pub : List Fp)
    (e : Expr) (he:e.pubBound=0) :
    e.eval (trace ids bs) t r pub=e.evalWith
      (env (cell ids bs r) (cell ids bs ((r+1)%2^22)) (if r=0 then 1 else 0)
        (if r+1=2^22 then 1 else 0) (if r+1=2^22 then 0 else 1)) := by
  let en:=env (cell ids bs r) (cell ids bs ((r+1)%2^22)) (if r=0 then 1 else 0)
    (if r+1=2^22 then 1 else 0) (if r+1=2^22 then 0 else 1)
  have hh:rowEnv (trace ids bs) t r pub={en with pub:=fun i=>pub.getD i 0} := by
    simp only [rowEnv,trace,Trace.height,en,env,ProcRecordConcatGeometry.cell]
    congr 1
    funext c nx
    cases nx <;> rfl
  change e.evalWith (rowEnv (trace ids bs) t r pub)=e.evalWith en
  rw [hh]
  exact ProcPriorTrace.eval_pub e he en (fun i=>pub.getD i 0)

theorem mult_same (tr tr' : Trace Fp) (t r t' r' : Nat) (pub pub' : List Fp)
    (hc:tr.cell t r=tr'.cell t' r') (i : Interaction)
    (hi:i∈ProcPriorRecordLinear.interactions 75 71 72 67 76) (e : Expr) (he:e∈i.mult) :
    e.eval tr t r pub=e.eval tr' t' r' pub' := by
  simp only [ProcPriorRecordLinear.interactions,ProcPriorRecordTable.interactions,
    List.take,List.drop,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [List.mem_singleton] at he
  all_goals subst e
  all_goals simp [Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,ProcPriorRecordTable.words,
    ProcPriorRecordTable.queryGate,ProcPriorRecordTable.header,hc]

theorem table (ids : NativeBlock→List Nat) (bs : List NativeBlock) (hb:∀b∈bs,b.Valid)
    (hfirst:∀b rest,bs=b::rest→b.run.tau=0)
    (hnext:∀pre b c rest,bs=pre++b::c::rest→c.run.tau=b.run.tau+1)
    (hraw:(ProcRawConcatGeometry.rows bs).length<2^22) (t : Nat) (pub : List Fp) :
    TableLocal (ProcPriorRecordLinear.table 75 71 72 67 76) (trace ids bs) t pub := by
  have hcap:(rows ids bs).length<2^22:=Nat.lt_of_le_of_lt (capacity ids bs) hraw
  refine ⟨by change 1≤22; decide +kernel,by change 22≤22; decide +kernel,?_,?_⟩
  · intro r hr e he
    have hpub:=ProcPriorRecordLocal.bounds 75 71 72 67 76 e (List.mem_append_left _ he)
    rw [row_eval ids bs t r pub e hpub]
    by_cases ha:r<(rows ids bs).length
    · have hlt:r+1<2^22:=by omega
      rw [Nat.mod_eq_of_lt hlt,ite_eq_right (show r+1≠2^22 by omega),ite_eq_right (show r+1≠2^22 by omega)]
      exact active ids bs hb hfirst hnext r ha e he
    · rw [padding ids bs r (by omega)]
      apply ProcPriorRecordPadding.padding_constraints
      · by_cases hz:r+1=2^22
        · left; simp [hz]
        · right
          have hlt:r+1<2^22:=by change r<2^22 at hr; omega
          rw [Nat.mod_eq_of_lt hlt,padding ids bs (r+1) (by omega)]
      · exact he
  · intro r hr i hi e he
    by_cases ha:r<(rows ids bs).length
    · obtain ⟨pre,b,post,j,hbs,hj,heq⟩:=active_cases ids bs r ha
      have hc:(trace ids bs).cell t r=(ProcPriorRecordTrace.trace (ids b) b.run.tau b.old.links).cell 0 j := by
        change cell ids bs r=blockCell (ids b) b j
        rw [heq,block_lookup ids bs pre post b hbs j hj]
      rw [mult_same _ _ t r 0 j pub pub hc i hi e he]
      exact ProcPriorRecordLocal.bits (ids b) b.run.tau b.old.links 0 j 75 71 72 67 76 pub i hi e he
    · have hpub:=ProcPriorRecordLocal.bounds 75 71 72 67 76 e (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨i,hi,List.mem_append_left _ he⟩))
      rw [row_eval ids bs t r pub e hpub,padding ids bs r (by omega)]
      exact Or.inl (ProcPriorRecordBits.padding_bits _ _ _ _ 75 71 72 67 76 i hi e he)
theorem native (ids : NativeBlock→List Nat) (bs : List NativeBlock) (hv:∀b∈bs,b.Valid)
    (ho:∀(i : Nat)(b : NativeBlock),bs[i]?=some b→b.run.tau=i)
    (hcap:(ProcRawConcatGeometry.rows bs).length<2^22) (t : Nat) (pub : List Fp) :
    TableLocal (ProcPriorRecordLinear.table 75 71 72 67 76) (trace ids bs) t pub := by
  apply table ids bs hv ?_ ?_ hcap
  · intro b rest he
    apply ho 0 b
    simp [he]
  · intro pre b c rest he
    have hb:bs[pre.length]?=some b := by simp [he]
    have hc:bs[pre.length+1]?=some c := by simp [he]
    rw [ho _ b hb,ho _ c hc]
end ZkFormal.NearV3.Candidates.ProcRecordConcatLocal
