import ZkFormal.NearV3.Candidates.ProcPriorRawHeaderInner
namespace ZkFormal.NearV3.Candidates.ProcPriorRawHeaderEnd
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E NearSpec.Bandwidth
open ProcPriorCells ProcPriorRawFrame ProcPriorRawGen ProcPriorRawHeader

def afterHeader (st : State) : ProcPriorRawSlots.Slot:=
  if st.links.length=0 then .hash 0 else .record 0 0

theorem end_constraints (st : State) (vid : Nat) (present : Bool)
    (hn:st.links.length<16777216) (hp:present=false→st.links.length=0)
    (e : Expr) (he:e∈constraints) :
    e.evalWith (env (cells st vid present 4 (.header 4))
      (cells st vid present 5 (afterHeader st)) 0 0 1)=0 := by
  have hzm (x:Fp):(0:Fp)*x=0:=by grind
  have hmz (x:Fp):x*(0:Fp)=0:=by grind
  have hom (x:Fp):(1:Fp)*x=x:=by grind
  have hmo (x:Fp):x*(1:Fp)=x:=by grind
  have ha (x:Fp):(0:Fp)+x=x:=by grind
  have haz (x:Fp):x+(0:Fp)=x:=by grind
  have hnz:-(0:Fp)=0:=by grind
  have hself (x:Fp):x+ -x=0:=by grind
  have hone:Fp.ofNat 1=(1:Fp):=rfl
  have hzero:Fp.ofNat 0=(0:Fp):=rfl
  have hfour:Fp.ofNat 4=(4:Fp):=rfl
  have hfive:Fp.ofNat 5=(5:Fp):=rfl
  have hi4:(-(4:Fp))*(-(4:Fp))⁻¹=1:=by decide +kernel
  have hcount:=ProcPriorRawBoolean.inv_delta st.links.length 0 (by
    have hP:P>16777216:=by decide +kernel
    omega) (by decide +kernel)
  simp only [hzero] at hcount
  have hsub (x:Fp):x-0=x:=by grind
  rw [hsub] at hcount
  have hl:=header_last st hn
  have hbf:Fp.ofNat (st.encode.getD 4 0).toNat=0:=by rw [hl.1]; rfl
  have hip:(4:Fp)*(4:Fp)⁻¹=1:=by decide +kernel
  have hf:constraints.map (·.evalWith (env (cells st vid present 4 (.header 4))
      (cells st vid present 5 (afterHeader st)) 0 0 1))=List.replicate constraints.length (0:Fp) := by
    cases hh:present <;> by_cases hz:st.links.length=0
    all_goals simp [constraints,isZero,ZkFormal.Chacha.Table.boolC,mul3,notE,nextWithin,done,
      ProcPriorRawFrame.endAt,sub,k,c,n,Expr.evalWith,env,cells,ProcPriorRawGen.isHeader,
      ProcPriorRawGen.isRecord,ProcPriorRawGen.isHash,ProcPriorRawGen.offset,ProcPriorRawGen.record,
      ProcPriorRawGen.endAt,ProcPriorRawFrame.act,ProcPriorRawFrame.tau,ProcPriorRawFrame.vid,
      ProcPriorRawFrame.present,ProcPriorRawFrame.pos,byte,hdr,rec,ProcPriorRawFrame.hash,
      ProcPriorRawFrame.offset,ProcPriorRawFrame.record,count,phaseEnd,endInv,recordEnd,recordInv,
      empty,emptyInv,ProcPriorRawFrame.first,acc,byteGate,firstInv,lengthGate,
      bit,hz,afterHeader,hbf,hcount,hl.1,hl.2,hip,hzm,hmz,hom,hmo,ha,haz,hnz,hself,hone,hzero,hfour,hi4,List.replicate]
    all_goals grind
  have hm:e.evalWith (env (cells st vid present 4 (.header 4)) (cells st vid present 5 (afterHeader st)) 0 0 1)
      ∈constraints.map (·.evalWith (env (cells st vid present 4 (.header 4)) (cells st vid present 5 (afterHeader st)) 0 0 1)):=List.mem_map.mpr ⟨e,he,rfl⟩
  rw [hf] at hm
  exact (List.mem_replicate.mp hm).2

end ZkFormal.NearV3.Candidates.ProcPriorRawHeaderEnd
