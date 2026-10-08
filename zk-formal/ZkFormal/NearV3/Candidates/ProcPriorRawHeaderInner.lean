import ZkFormal.NearV3.Candidates.ProcPriorRawStart
namespace ZkFormal.NearV3.Candidates.ProcPriorRawHeaderInner
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E NearSpec.Bandwidth
open ProcPriorCells ProcPriorRawFrame ProcPriorRawGen ProcPriorRawHeader

theorem inner_constraints (st : State) (vid g : Nat) (present : Bool) (hg:1≤g ∧ g<4)
    (hn:st.links.length<16777216) (hp:present=false→st.links.length=0)
    (e : Expr) (he:e∈constraints) :
    e.evalWith (env (cells st vid present g (.header g))
      (cells st vid present (g+1) (.header (g+1))) 0 0 1)=0 := by
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
  have hb:=header_byte st g (by omega)
  have hacc:=header_acc_field st g hg
  have haccN:=congrArg Fp.ofNat (header_acc st g hg)
  have hfirst:=ProcPriorRawBoolean.inv_delta g 0 (by
    have hP:P>4:=by decide +kernel
    omega) (by decide +kernel)
  have hend:=ProcPriorRawBoolean.inv_delta g 4 (by
    have hP:P>4:=by decide +kernel
    omega) (by decide +kernel)
  have hg0:g≠0:=by omega
  have hg4:g≠4:=by omega
  have hgn:g+1≠0:=by omega
  have hgsub:g+1-1=g:=by omega
  have hpos:Fp.ofNat (g+1)=Fp.ofNat g+1:=by
    change (↑(g+1):Fp)=↑g+1
    grind
  simp only [hzero,hsub,bit,hg0,hg4,decide_false,ite_false] at hfirst hend
  have hbn:st.links.length=0→Fp.ofNat (st.encode.getD g 0).toNat=0:=by
    intro hh
    rw [hb,ite_eq_right hg0,hh]
    simp
    rfl
  have hbf:present=false→Fp.ofNat (st.encode.getD g 0).toNat=0:=by
    intro hh
    rw [hb,ite_eq_right hg0,hp hh]
    simp
    rfl
  have hf:constraints.map (·.evalWith (env (cells st vid present g (.header g))
      (cells st vid present (g+1) (.header (g+1))) 0 0 1))=List.replicate constraints.length (0:Fp) := by
    cases hh:present <;> by_cases hz:st.links.length=0
    all_goals simp [constraints,isZero,ZkFormal.Chacha.Table.boolC,mul3,notE,nextWithin,done,
      ProcPriorRawFrame.endAt,sub,k,c,n,Expr.evalWith,env,cells,ProcPriorRawGen.isHeader,
      ProcPriorRawGen.isRecord,ProcPriorRawGen.isHash,ProcPriorRawGen.offset,ProcPriorRawGen.record,
      ProcPriorRawGen.endAt,ProcPriorRawFrame.act,ProcPriorRawFrame.tau,ProcPriorRawFrame.vid,
      ProcPriorRawFrame.present,ProcPriorRawFrame.pos,byte,hdr,rec,ProcPriorRawFrame.hash,
      ProcPriorRawFrame.offset,ProcPriorRawFrame.record,count,phaseEnd,endInv,recordEnd,recordInv,
      empty,emptyInv,ProcPriorRawFrame.first,acc,byteGate,firstInv,lengthGate,
      bit,hz,hg0,hg4,hgn,hgsub,hpos,hcount,hzm,hmz,hom,hmo,ha,haz,hnz,hself,hone,hzero,hfour,hi4,List.replicate]
    all_goals grind
  have hm:e.evalWith (env (cells st vid present g (.header g)) (cells st vid present (g+1) (.header (g+1))) 0 0 1)
      ∈constraints.map (·.evalWith (env (cells st vid present g (.header g)) (cells st vid present (g+1) (.header (g+1))) 0 0 1)):=List.mem_map.mpr ⟨e,he,rfl⟩
  rw [hf] at hm
  exact (List.mem_replicate.mp hm).2

end ZkFormal.NearV3.Candidates.ProcPriorRawHeaderInner
