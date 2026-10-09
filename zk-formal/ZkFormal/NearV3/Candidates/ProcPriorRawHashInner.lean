import ZkFormal.NearV3.Candidates.ProcPriorRawRecordEnd
namespace ZkFormal.NearV3.Candidates.ProcPriorRawHashInner
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E NearSpec.Bandwidth
open ProcPriorCells ProcPriorRawFrame ProcPriorRawGen ProcPriorRawHeader

theorem initial_byte (i : Nat) : State.initial.encode.getD i 0=0 := by
  have he:State.initial.encode=List.replicate 37 0:=by decide +kernel
  rw [he]
  have hz (n i : Nat) : (List.replicate n (0 : UInt8)).getD i 0 = 0 := by
    induction n generalizing i with
    | zero => simp
    | succ n ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i
  exact hz 37 i

theorem inner_constraints (st : State) (vid g : Nat) (present : Bool) (hg:g<31)
    (hn:st.links.length<16777216) (hp:present=false→st=State.initial)
    (e : Expr) (he:e∈constraints) :
    e.evalWith (env (cells st vid present (5+24*st.links.length+g) (.hash g))
      (cells st vid present (5+24*st.links.length+g+1) (.hash (g+1))) 0 0 1)=0 := by
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
  have hg31:g≠31:=by omega
  have hpos:Fp.ofNat (5+24*st.links.length+g+1)=Fp.ofNat (5+24*st.links.length+g)+1:=by
    change (↑(5+24*st.links.length+g+1):Fp)=↑(5+24*st.links.length+g)+1
    grind
  have hgpos:Fp.ofNat (g+1)=Fp.ofNat g+1:=by
    change (↑(g+1):Fp)=↑g+1
    grind
  have hend:=ProcPriorRawBoolean.inv_delta g 31 (by
    have hP:P>32:=by decide +kernel
    omega) (by decide +kernel)
  have hthirtyone:Fp.ofNat 31=(31:Fp):=rfl
  simp only [bit,hg31,decide_false] at hend
  have hbf:present=false→Fp.ofNat (st.encode.getD (5+24*st.links.length+g) 0).toNat=0:=by
    intro hh
    rw [hp hh,initial_byte]
    rfl
  have hpCount : present=false → st.links.length=0 := by
    intro hh
    rw [hp hh]
    rfl
  have hf:constraints.map (·.evalWith (env (cells st vid present (5+24*st.links.length+g) (.hash g))
      (cells st vid present (5+24*st.links.length+g+1) (.hash (g+1))) 0 0 1))=List.replicate constraints.length (0:Fp) := by
    cases hh:present <;> by_cases hz:st.links.length=0
    all_goals simp [constraints,isZero,ZkFormal.Chacha.Table.boolC,mul3,notE,nextWithin,done,
      ProcPriorRawFrame.endAt,sub,k,c,n,Expr.evalWith,env,cells,ProcPriorRawGen.isHeader,
      ProcPriorRawGen.isRecord,ProcPriorRawGen.isHash,ProcPriorRawGen.offset,ProcPriorRawGen.record,
      ProcPriorRawGen.endAt,ProcPriorRawFrame.act,ProcPriorRawFrame.tau,ProcPriorRawFrame.vid,
      ProcPriorRawFrame.present,ProcPriorRawFrame.pos,byte,hdr,rec,ProcPriorRawFrame.hash,
      ProcPriorRawFrame.offset,ProcPriorRawFrame.record,count,phaseEnd,endInv,recordEnd,recordInv,
      empty,emptyInv,ProcPriorRawFrame.first,acc,byteGate,firstInv,lengthGate,
      bit,hz,hg31,hpos,hgpos,hcount,hthirtyone,hzm,hmz,hom,hmo,ha,haz,hnz,hself,hone,hzero,hfour,hi4,List.replicate]
    all_goals grind
  have hm:e.evalWith (env (cells st vid present (5+24*st.links.length+g) (.hash g)) (cells st vid present (5+24*st.links.length+g+1) (.hash (g+1))) 0 0 1)
      ∈constraints.map (·.evalWith (env (cells st vid present (5+24*st.links.length+g) (.hash g)) (cells st vid present (5+24*st.links.length+g+1) (.hash (g+1))) 0 0 1)):=List.mem_map.mpr ⟨e,he,rfl⟩
  rw [hf] at hm
  exact (List.mem_replicate.mp hm).2

end ZkFormal.NearV3.Candidates.ProcPriorRawHashInner
