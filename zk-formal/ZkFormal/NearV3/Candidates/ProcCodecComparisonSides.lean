import ZkFormal.NearV3.Candidates.ProcCodecComparisonTraffic
namespace ZkFormal.NearV3.Candidates.ProcCodecComparisonSides
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash SchedSetAll

set_option maxRecDepth 8192
set_option maxHeartbeats 500000

theorem header (I : Input) (R : Run) (present : Bool) (vid p : Nat) (params hdr : List Nat) :
    (headerRow (instanceCells I R present vid) params hdr present p)[cg]! =0 := by
  unfold headerRow
  rw [SchedSetAll.cell _ _ _ (by decide)]
  simp [lookup,instanceCells,List.foldl_append,List.range_succ,
    cg,act,tau,pres,Codec.vid,nn,NN,base,fair,itz,zt,kH,kF,pos,bpost,bpre,vbg,ihp,ehp,reg,overlay,kidx,klo,khi,Codec.g,ig7,ig2,wt,ap,ib,apost,ikl,a1,afin,gfin,gb,a2,g2,cx,cy,lowf,nzb,al,cb,bF,srcC,apR,hasC,bigR,pbit,prbit]

theorem hash (I : Input) (R : Run) (present : Bool) (vid base0 j : Nat) (digest hpre : List Nat) :
    (hashRow (instanceCells I R present vid) digest hpre present base0 j)[cg]! =0 := by
  unfold hashRow
  rw [SchedSetAll.cell _ _ _ (by decide)]
  simp [lookup,instanceCells,List.foldl_append,List.range_succ,
    cg,act,tau,pres,Codec.vid,nn,NN,base,fair,itz,zt,kZ,dgg,pos,sj,bpost,bpre,bsha,vbg,isj,esj,reg,overlay,kidx,klo,khi,Codec.g,ig7,ig2,wt,ap,ib,apost,ikl,a1,afin,gfin,gb,a2,g2,cx,cy,lowf,nzb,al,cb,bF,srcC,apR,hasC,bigR,pbit,prbit]

theorem ash (I : Input) (R : Run) (present : Bool) (vid base0 j : Nat) :
    (ashRow (instanceCells I R present vid) I base0 j)[cg]! =0 := by
  unfold ashRow
  rw [SchedSetAll.cell _ _ _ (by decide)]
  simp [lookup,instanceCells,List.foldl_append,
    cg,act,tau,pres,Codec.vid,nn,NN,base,fair,itz,zt,kA,pos,sj,bsha,pm0,pm1,isj,esj]

theorem quiet (row : Array Nat) (h:row[cg]! =0) : ProcCodecConcatTraffic.natMessages row B_SCMP true=[] := by
  rw [ProcCodecComparisonTraffic.nat_messages,h]
  simp only [show ZkFormal.Algebra.Fp.ofNat 0 = (0:ZkFormal.Algebra.Fp) from rfl,
    show (0:ZkFormal.Algebra.Fp)≠1 from by decide +kernel,if_false,List.replicate_zero]
end ZkFormal.NearV3.Candidates.ProcCodecComparisonSides
