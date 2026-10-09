import ZkFormal.NearV3.Candidates.ProcIdTaggedCells
namespace ZkFormal.NearV3.Candidates.ProcIdTaggedBoundary
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E
open ProcPriorIdRows ProcPriorCells ProcPriorIdCells ProcPriorIdTable
open ProcPriorIdCarryFields ProcPriorIdGateFields ProcIdTaggedCells

theorem boolean_cross (a b : Tagged) (col : Nat)
    (hc:col∈[0,6,7,9,10,11,12,16,17,18,19]) : cross a b col=0 ∨ cross a b col=1 := by
  unfold cross
  split
  · exact Or.inl rfl
  · have hn:col≠13:=by simp only [List.mem_cons,List.not_mem_nil,or_false] at hc; omega
    rw [ite_eq_right hn]
    exact ProcPriorIdCells.boolean_cells a.2 (some b.2) a.1 col hc

theorem cross_constraints (a b : Tagged) (after : Option Row) (fi : Fp)
    (hat:a.1<32) (hbt:b.1<32) (ht:a.1<b.1)
    (ha:a.2.event.key<2^64) (hb:b.2.event.key<2^64)
    (hf:fi=0 ∨ a.2.before=none) (hn:b.2.before=none)
    (e : Expr) (he:e∈constraints) :
    e.evalWith (env (cross a b) (ProcPriorIdCells.cells b.2 after b.1) fi 0 1)=0 := by
  have hone:Fp.ofNat 1=(1:Fp):=rfl
  have hzero:Fp.ofNat 0=(0:Fp):=rfl
  have hbf:bit false=(0:Fp):=rfl
  have htake:=take_field a.2
  have hmissing:=missing_index a.2
  obtain ⟨hal,ham,hah⟩:=ProcPriorIdLimbs.bounds a.2.event.key ha
  obtain ⟨hbl,hbm,hbh⟩:=ProcPriorIdLimbs.bounds b.2.event.key hb
  have hp:P>16777216:=by decide +kernel
  have hmid:=limb_inverse ProcPriorIdLimbs.mid a.2 b.2 (by omega) (by omega)
  have hlo:=limb_inverse ProcPriorIdLimbs.lo a.2 b.2 (by omega) (by omega)
  have htop:=ProcPriorRawBoolean.inv_delta (ProcIdTaggedCells.top b) (ProcIdTaggedCells.top a)
    (top_bound b hbt hb) (top_bound a hat ha)
  have hne:ProcIdTaggedCells.top b≠ProcIdTaggedCells.top a:=by have:=top_lt a b ht ha; omega
  simp [hne,bit] at htop
  have hfirst:fi*bit a.2.before.isSome=0 ∧ fi*Fp.ofNat (a.2.before.getD 0)=0 := by
    rcases hf with hf|hf
    · subst fi; grind
    · simp [hf,bit,hzero]; grind
  have htopcast (x:Tagged):Fp.ofNat (ProcIdTaggedCells.top x)=
      (65536:Fp)*Fp.ofNat x.1+Fp.ofNat (ProcPriorIdLimbs.hi x.2.event.key) := by
    change ((65536*x.1+ProcPriorIdLimbs.hi x.2.event.key:Nat):Fp)=
      65536*(x.1:Fp)+(ProcPriorIdLimbs.hi x.2.event.key: Fp)
    grind
  have htopcast' (x:Tagged):Fp.ofNat (ProcPriorIdLimbs.hi x.2.event.key+65536*x.1)=Fp.ofNat (ProcIdTaggedCells.top x):=by
    congr 1
    exact Nat.add_comm _ _
  simp only [constraints,List.mem_append] at he
  rcases he with (((he|he)|he)|he)|he
  · obtain ⟨cc,hc,rfl⟩:=List.mem_map.mp he
    rcases boolean_cross a b cc hc with hv|hv
    all_goals simp [ZkFormal.Chacha.Table.boolC,sub,k,c,Expr.evalWith,env,hv,hone]
    all_goals grind
  all_goals simp only [eqs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at he
  all_goals first
    | (rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
    | (rcases he with rfl|rfl)
  all_goals
    simp [eqs,dTop,dMid,dLo,ProcPriorIdTable.top,adjacent,notE,sub,k,c,n,Expr.evalWith,env,
      cross,ProcPriorIdCells.cells,act,tau,keyLo,keyMid,keyHi,ordinal,isPublic,found,index,
      ProcPriorIdTable.take,eqTop,eqMid,eqLo,invTop,invMid,invLo,gTop,gMid,gAll,gPublic,hone,hzero,hn,hbf]
  all_goals try simp only [htopcast',htopcast]
  all_goals simp only [htopcast] at htop
  all_goals grind [sameMid,sameLo]
end ZkFormal.NearV3.Candidates.ProcIdTaggedBoundary
