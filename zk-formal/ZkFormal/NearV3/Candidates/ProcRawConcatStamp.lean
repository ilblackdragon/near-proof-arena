import ZkFormal.NearV3.Candidates.ProcRawConcatBoundary
namespace ZkFormal.NearV3.Candidates.ProcRawConcatStamp
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha.Table.E
open ProcPriorCells ProcPriorRawFrame ProcRawConcatBoundary

/-- Away from an instance endpoint, a common tau stamp changes no constraint
when the physical row is not the first row. -/
theorem interior (cur nxt : Nat→Fp) (tauV : Fp)
    (hc : cur tau=0) (hn : nxt tau=0)
    (hd : cur hash*cur phaseEnd=0)
    (e : Expr) (he : e∈constraints) :
    e.evalWith (env (stamp tauV cur) (stamp tauV nxt) 0 0 1)=
      e.evalWith (env cur nxt 0 0 1) := by
  change cur 1=0 at hc
  change nxt 1=0 at hn
  change cur 8*cur 12=0 at hd
  have hh : constraints.map (fun e=>e.evalWith (env (stamp tauV cur) (stamp tauV nxt) 0 0 1))=
      constraints.map (fun e=>e.evalWith (env cur nxt 0 0 1)) := by
    simp [constraints,isZero,ZkFormal.Chacha.Table.boolC,mul3,notE,nextWithin,done,
      endAt,sub,k,c,n,Expr.evalWith,env,stamp,act,tau,vid,present,pos,byte,hdr,rec,ProcPriorRawFrame.hash,
      offset,record,count,phaseEnd,endInv,recordEnd,recordInv,empty,emptyInv,first,acc,
      byteGate,firstInv,lengthGate]
    all_goals grind
  have hm:=List.getElem_of_mem he
  obtain ⟨i,hi,heq⟩:=hm
  have hh':(constraints.map (fun e=>e.evalWith (env (stamp tauV cur) (stamp tauV nxt) 0 0 1)))[i]'(by simpa using hi)=
      (constraints.map (fun e=>e.evalWith (env cur nxt 0 0 1)))[i]'(by simpa using hi) := by simp only [hh]
  simpa only [List.getElem_map,heq] using hh'
theorem without_first (cur nxt : Nat→Fp) (firstV : Fp)
    (hc : cur tau=0) (ha : cur act=cur first)
    (e : Expr) (he : e∈constraints) :
    e.evalWith (env cur nxt firstV 0 1)=
      e.evalWith (env cur nxt 0 0 1) := by
  change cur 1=0 at hc
  change cur 0=cur 18 at ha
  have hh : constraints.map (fun e=>e.evalWith (env cur nxt firstV 0 1))=
      constraints.map (fun e=>e.evalWith (env cur nxt 0 0 1)) := by
    simp [constraints,isZero,ZkFormal.Chacha.Table.boolC,mul3,notE,nextWithin,done,
      endAt,sub,k,c,n,Expr.evalWith,env,stamp,act,tau,vid,present,pos,byte,hdr,rec,ProcPriorRawFrame.hash,
      offset,record,count,phaseEnd,endInv,recordEnd,recordInv,empty,emptyInv,first,acc,
      byteGate,firstInv,lengthGate]
    all_goals grind
  have hm:=List.getElem_of_mem he
  obtain ⟨i,hi,heq⟩:=hm
  have hh':(constraints.map (fun e=>e.evalWith (env cur nxt firstV 0 1)))[i]'(by simpa using hi)=
      (constraints.map (fun e=>e.evalWith (env cur nxt 0 0 1)))[i]'(by simpa using hi) := by simp only [hh]
  simpa only [List.getElem_map,heq] using hh'
end ZkFormal.NearV3.Candidates.ProcRawConcatStamp
