import ZkFormal.NearV3.Candidates.ProcPriorIdGateFields
namespace ZkFormal.NearV3.Candidates.ProcPriorIdActive
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E
open ProcPriorIdRows ProcPriorCells ProcPriorIdCells ProcPriorIdTable ProcPriorIdCarryFields ProcPriorIdGateFields

theorem pair_constraints (a b : Row) (after : Option Row) (t : Nat) (fi : Fp)
    (ha:a.event.key<18446744073709551616) (hb:b.event.key<18446744073709551616)
    (hf:fi=0 ∨ a.before=none)
    (hn:b.before=if a.event.key=b.event.key then ProcPriorIdCarry.update a.before a.event else none)
    (ho:ProcPriorIds.precedes a.event b.event=true)
    (e : Expr) (he:e∈constraints) :
    e.evalWith (env (cells a (some b) t) (cells b after t) fi 0 1)=0 := by
  have hone:Fp.ofNat 1=(1:Fp):=rfl
  have hcarry:=carry_fields a b hn
  have htake:=take_field a
  have hmissing:=missing_index a
  have horder:=no_query_public a b ho
  obtain ⟨hgm,hga,hgp⟩:=gates a b
  obtain ⟨hal,ham,hah⟩:=ProcPriorIdLimbs.bounds a.event.key ha
  obtain ⟨hbl,hbm,hbh⟩:=ProcPriorIdLimbs.bounds b.event.key hb
  have hp:P>16777216:=by decide +kernel
  have htop:Fp.ofNat (65536*t+ProcPriorIdLimbs.hi b.event.key)-
      Fp.ofNat (65536*t+ProcPriorIdLimbs.hi a.event.key)=
      Fp.ofNat (ProcPriorIdLimbs.hi b.event.key)-Fp.ofNat (ProcPriorIdLimbs.hi a.event.key) := by
    change (↑(65536*t+ProcPriorIdLimbs.hi b.event.key):Fp)-↑(65536*t+ProcPriorIdLimbs.hi a.event.key)=
      ↑(ProcPriorIdLimbs.hi b.event.key)-↑(ProcPriorIdLimbs.hi a.event.key)
    grind
  have hhi:=limb_inverse ProcPriorIdLimbs.hi a b (by omega) (by omega)
  have hmid:=limb_inverse ProcPriorIdLimbs.mid a b (by omega) (by omega)
  have hlo:=limb_inverse ProcPriorIdLimbs.lo a b (by omega) (by omega)
  have hfirst:fi*bit a.before.isSome=0 ∧ fi*Fp.ofNat (a.before.getD 0)=0 := by
    have hz:Fp.ofNat 0=(0:Fp):=rfl
    rcases hf with hf|hf
    · subst fi; grind
    · simp [hf,bit,hz]; grind
  simp only [constraints,List.mem_append] at he
  rcases he with (((he|he)|he)|he)|he
  · obtain ⟨cc,hc,rfl⟩:=List.mem_map.mp he
    have hc':cc∈[0,6,7,9,10,11,12,16,17,18,19]:=hc
    rcases boolean_cells a (some b) t cc hc' with hv|hv
    all_goals simp [ZkFormal.Chacha.Table.boolC,sub,k,c,Expr.evalWith,env,hv,hone]
    all_goals grind
  all_goals simp only [eqs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at he
  all_goals first
    | (rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
    | (rcases he with rfl|rfl)
  all_goals
    simp [eqs,dTop,dMid,dLo,top,adjacent,notE,sub,k,c,n,Expr.evalWith,env,cells,
      act,tau,keyLo,keyMid,keyHi,ordinal,isPublic,found,index,ProcPriorIdTable.take,
      eqTop,eqMid,eqLo,invTop,invMid,invLo,gTop,gMid,gAll,gPublic,hone]
  all_goals grind [sameTop,sameMid,sameLo]

end ZkFormal.NearV3.Candidates.ProcPriorIdActive
