import ZkFormal.NearV3.Candidates.ProcRawInstancePresence
import ZkFormal.NearV3.Candidates.ProcPriorRawHashEnd
namespace ZkFormal.NearV3.Candidates.ProcRawConcatBoundary
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E NearSpec.Bandwidth
open ProcPriorCells ProcPriorRawFrame ProcPriorRawGen ProcPriorRawHeader

def stamp (tauV : Fp) (row : Nat→Fp) : Nat→Fp :=
  fun c=>if c=ProcPriorRawFrame.tau then tauV else row c

theorem next_constraints (st next : State) (vid vidNext : Nat) (present presentNext : Bool) (tauV : Fp)
    (hn:st.links.length<16777216) (hp:present=false→st=State.initial)
    (e : Expr) (he:e∈constraints) :
    e.evalWith (env (stamp tauV (cells st vid present (5+24*st.links.length+31) (.hash 31)))
      (stamp (tauV+1) (cells next vidNext presentNext 0 (.header 0))) 0 0 1)=0 := by
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
  have hi4:(-(4:Fp))*(-(4:Fp))⁻¹=1:=by decide +kernel
  have hcount:=ProcPriorRawBoolean.inv_delta st.links.length 0 (by
    have hP:P>16777216:=by decide +kernel
    omega) (by decide +kernel)
  simp only [hzero] at hcount
  have hsub (x:Fp):x-0=x:=by grind
  rw [hsub] at hcount
  have hthirtyone:Fp.ofNat 31=(31:Fp):=rfl
  have hbf:present=false→Fp.ofNat (st.encode.getD (5+24*st.links.length+31) 0).toNat=0:=by
    intro hh
    rw [hp hh,ProcPriorRawHashInner.initial_byte]
    rfl
  have hpCount : present=false → st.links.length=0 := by
    intro hh
    rw [hp hh]
    rfl
  have hf:constraints.map (·.evalWith (env (stamp tauV (cells st vid present (5+24*st.links.length+31) (.hash 31)))
      (stamp (tauV+1) (cells next vidNext presentNext 0 (.header 0))) 0 0 1))=List.replicate constraints.length (0:Fp) := by
    cases hh:present <;> by_cases hz:st.links.length=0
    all_goals simp [stamp,constraints,isZero,ZkFormal.Chacha.Table.boolC,mul3,notE,nextWithin,done,
      ProcPriorRawFrame.endAt,sub,k,c,n,Expr.evalWith,env,cells,ProcPriorRawGen.isHeader,
      ProcPriorRawGen.isRecord,ProcPriorRawGen.isHash,ProcPriorRawGen.offset,ProcPriorRawGen.record,
      ProcPriorRawGen.endAt,ProcPriorRawFrame.act,ProcPriorRawFrame.tau,ProcPriorRawFrame.vid,
      ProcPriorRawFrame.present,ProcPriorRawFrame.pos,byte,hdr,rec,ProcPriorRawFrame.hash,
      ProcPriorRawFrame.offset,ProcPriorRawFrame.record,count,phaseEnd,endInv,recordEnd,recordInv,
      empty,emptyInv,ProcPriorRawFrame.first,acc,byteGate,firstInv,lengthGate,
      bit,hz,hcount,hthirtyone,hzm,hmz,hom,hmo,ha,haz,hnz,hself,hone,hzero,hfour,hi4,List.replicate]
    all_goals grind
  have hm:e.evalWith (env (stamp tauV (cells st vid present (5+24*st.links.length+31) (.hash 31))) (stamp (tauV+1) (cells next vidNext presentNext 0 (.header 0))) 0 0 1)
      ∈constraints.map (·.evalWith (env (stamp tauV (cells st vid present (5+24*st.links.length+31) (.hash 31))) (stamp (tauV+1) (cells next vidNext presentNext 0 (.header 0))) 0 0 1)):=List.mem_map.mpr ⟨e,he,rfl⟩
  rw [hf] at hm
  exact (List.mem_replicate.mp hm).2

theorem padding_constraints (st : State) (vid : Nat) (present : Bool) (tauV : Fp)
    (hn:st.links.length<16777216) (hp:present=false→st=State.initial)
    (e : Expr) (he:e∈constraints) :
    e.evalWith (env (stamp tauV (cells st vid present (5+24*st.links.length+31) (.hash 31)))
      (fun _=>0) 0 0 1)=0 := by
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
  have hi4:(-(4:Fp))*(-(4:Fp))⁻¹=1:=by decide +kernel
  have hcount:=ProcPriorRawBoolean.inv_delta st.links.length 0 (by
    have hP:P>16777216:=by decide +kernel
    omega) (by decide +kernel)
  simp only [hzero] at hcount
  have hsub (x:Fp):x-0=x:=by grind
  rw [hsub] at hcount
  have hthirtyone:Fp.ofNat 31=(31:Fp):=rfl
  have hbf:present=false→Fp.ofNat (st.encode.getD (5+24*st.links.length+31) 0).toNat=0:=by
    intro hh
    rw [hp hh,ProcPriorRawHashInner.initial_byte]
    rfl
  have hpCount : present=false → st.links.length=0 := by
    intro hh
    rw [hp hh]
    rfl
  have hf:constraints.map (·.evalWith (env (stamp tauV (cells st vid present (5+24*st.links.length+31) (.hash 31)))
      (fun _=>0) 0 0 1))=List.replicate constraints.length (0:Fp) := by
    cases hh:present <;> by_cases hz:st.links.length=0
    all_goals simp [stamp,constraints,isZero,ZkFormal.Chacha.Table.boolC,mul3,notE,nextWithin,done,
      ProcPriorRawFrame.endAt,sub,k,c,n,Expr.evalWith,env,cells,ProcPriorRawGen.isHeader,
      ProcPriorRawGen.isRecord,ProcPriorRawGen.isHash,ProcPriorRawGen.offset,ProcPriorRawGen.record,
      ProcPriorRawGen.endAt,ProcPriorRawFrame.act,ProcPriorRawFrame.tau,ProcPriorRawFrame.vid,
      ProcPriorRawFrame.present,ProcPriorRawFrame.pos,byte,hdr,rec,ProcPriorRawFrame.hash,
      ProcPriorRawFrame.offset,ProcPriorRawFrame.record,count,phaseEnd,endInv,recordEnd,recordInv,
      empty,emptyInv,ProcPriorRawFrame.first,acc,byteGate,firstInv,lengthGate,
      bit,hz,hcount,hthirtyone,hzm,hmz,hom,hmo,ha,haz,hnz,hself,hone,hzero,hfour,hi4,List.replicate]
    all_goals grind
  have hm:e.evalWith (env (stamp tauV (cells st vid present (5+24*st.links.length+31) (.hash 31))) (fun _=>0) 0 0 1)
      ∈constraints.map (·.evalWith (env (stamp tauV (cells st vid present (5+24*st.links.length+31) (.hash 31))) (fun _=>0) 0 0 1)):=List.mem_map.mpr ⟨e,he,rfl⟩
  rw [hf] at hm
  exact (List.mem_replicate.mp hm).2

end ZkFormal.NearV3.Candidates.ProcRawConcatBoundary
