import ZkFormal.NearV3.Candidates.ProcPriorRawRecordInner
namespace ZkFormal.NearV3.Candidates.ProcPriorRawRecordEnd
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E NearSpec.Bandwidth
open ProcPriorCells ProcPriorRawFrame ProcPriorRawGen ProcPriorRawHeader

def afterRecord (st : State) (j : Nat) : ProcPriorRawSlots.Slot:=
  if j+1=st.links.length then .hash 0 else .record (j+1) 0

theorem end_constraints (st : State) (vid j : Nat) (present : Bool) (hj:j<st.links.length)
    (hn:st.links.length<16777216) (hp:present=false→st.links.length=0)
    (e : Expr) (he:e∈constraints) :
    e.evalWith (env (cells st vid present (5+24*j+23) (.record j 23))
      (cells st vid present (5+24*j+23+1) (afterRecord st j)) 0 0 1)=0 := by
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
  have hnp:st.links.length<P:=by
    have hP:P>16777216:=by decide +kernel
    omega
  have hn0:st.links.length≠0:=by omega
  have hptrue:present=true:=by cases present <;> simp_all
  subst present
  have hpos:Fp.ofNat (5+24*j+23+1)=Fp.ofNat (5+24*j+23)+1:=by
    change (↑(5+24*j+23+1):Fp)=↑(5+24*j+23)+1
    grind
  have hjpos:Fp.ofNat (j+1)=Fp.ofNat j+1:=by
    change (↑(j+1):Fp)=↑j+1
    grind
  have hrec:=ProcPriorRawBoolean.inv_delta (j+1) st.links.length (by omega) hnp
  have htwentythree:Fp.ofNat 23=(23:Fp):=rfl
  have hf:constraints.map (·.evalWith (env (cells st vid true (5+24*j+23) (.record j 23))
      (cells st vid true (5+24*j+23+1) (afterRecord st j)) 0 0 1))=List.replicate constraints.length (0:Fp) := by
    by_cases hje:j+1=st.links.length
    all_goals simp [bit,hje,hjpos] at hrec
    all_goals simp [constraints,isZero,ZkFormal.Chacha.Table.boolC,mul3,notE,nextWithin,done,
      ProcPriorRawFrame.endAt,sub,k,c,n,Expr.evalWith,env,cells,ProcPriorRawGen.isHeader,
      ProcPriorRawGen.isRecord,ProcPriorRawGen.isHash,ProcPriorRawGen.offset,ProcPriorRawGen.record,
      ProcPriorRawGen.endAt,ProcPriorRawFrame.act,ProcPriorRawFrame.tau,ProcPriorRawFrame.vid,
      ProcPriorRawFrame.present,ProcPriorRawFrame.pos,byte,hdr,rec,ProcPriorRawFrame.hash,
      ProcPriorRawFrame.offset,ProcPriorRawFrame.record,count,phaseEnd,endInv,recordEnd,recordInv,
      empty,emptyInv,ProcPriorRawFrame.first,acc,byteGate,firstInv,lengthGate,
      bit,hn0,hje,afterRecord,hpos,hjpos,hcount,htwentythree,hzm,hmz,hom,hmo,ha,haz,hnz,hself,hone,hzero,hfour,hi4,List.replicate]
    all_goals grind
  have hm:e.evalWith (env (cells st vid true (5+24*j+23) (.record j 23)) (cells st vid true (5+24*j+23+1) (afterRecord st j)) 0 0 1)
      ∈constraints.map (·.evalWith (env (cells st vid true (5+24*j+23) (.record j 23)) (cells st vid true (5+24*j+23+1) (afterRecord st j)) 0 0 1)):=List.mem_map.mpr ⟨e,he,rfl⟩
  rw [hf] at hm
  exact (List.mem_replicate.mp hm).2

end ZkFormal.NearV3.Candidates.ProcPriorRawRecordEnd
