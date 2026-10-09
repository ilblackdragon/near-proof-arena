import ZkFormal.NearV3.Candidates.ProcCodecHeaderKind
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedInstance
namespace ZkFormal.NearV3.Candidates.ProcCodecSanityGate
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecAssignments ProcPriorCodecNativeHash
open SchedSetAll

theorem header (I : Input) (R : Run) (present : Bool) (vid : Nat) (params hdr : List Nat) (p : Nat) :
    (headerRow (instanceCells I R present vid) params hdr present p)[kZ]! = 0 := by
  rw [ProcPriorCodecHeaderReads.projection _ _ _ _ _ _ (by decide +kernel),append]
  simp [ProcPriorCodecHeaderReads.headerScalars,lookup,kH,kZ,kF,pos,bpost,bpre,vbg,ihp,ehp,instanceCells,act,tau,pres,Codec.vid,nn,NN,base,fair,itz,zt]

theorem record (I : Input) (R : Run) (present : Bool) (vid k f g p bpo bpr a b : Nat)
    (tail : List (Nat×Nat)) (ht : ProcPriorCodecExtraColumns.Tail tail) :
    (recordRow I present R.n k f g p bpo bpr (instanceCells I R present vid)
      (ProcPriorCodecExtra.baseExtra R.n k f g a b++tail))[kZ]! =0 := by
  rw [ProcPriorCodecRecordReads.native_projection _ _ _ _ _ _ _ _ _ _ _ _ _ ht kZ (by decide +kernel),append]
  simp [ProcPriorCodecRecordReads.scalars,instanceCells,lookup,act,tau,pres,Codec.vid,nn,NN,base,fair,
    itz,zt,kH,kR,kZ,kA,kZ,pos,bpost,bpre,vbg,kidx,klo,khi,fS,fR,fA,Codec.g,ig7,e7,ikl,ekl]

theorem hash (I : Input) (R : Run) (present : Bool) (vid : Nat) (digest hpre : List Nat) (p j : Nat) :
    (hashRow (instanceCells I R present vid) digest hpre present p j)[kZ]! =1 := by
  rw [ProcPriorCodecHashReads.projection _ _ _ _ _ _ _ (by decide +kernel),append]
  simp [ProcPriorCodecHashReads.hashScalars,instanceCells,lookup,act,tau,pres,Codec.vid,nn,NN,base,fair,
    itz,zt,kZ,kZ,pos,bpost,bpre,vbg,dgg,sj,bsha,isj,esj]

theorem ash (I : Input) (R : Run) (present : Bool) (vid p j : Nat) :
    (ashRow (instanceCells I R present vid) I p j)[kZ]! =0 := by
  unfold ashRow
  rw [SchedSetAll.cell _ _ _ (by decide +kernel),append]
  simp [instanceCells,lookup,act,tau,pres,Codec.vid,nn,NN,base,fair,
    itz,zt,kA,kZ,pos,sj,bsha,pm0,pm1,isj,esj]

theorem active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out)
    (r : Nat) (hr : r<out.rows.size) :out.rows[r]![kZ]! =
      if 5+24*(R.n*R.n)≤r ∧ r<5+24*(R.n*R.n)+32 then 1 else 0 := by
  have hl:=generated_length I R present vid gb fwd out h
  by_cases hh:r<5
  · rw [ite_eq_right (by omega),ProcCodecHeaderKind.header_cell I R present vid gb fwd out h r hh,header]
  · by_cases hrec:r<5+24*(R.n*R.n)
    · rw [ite_eq_right (by omega)]
      have he:r=5+24*((r-5)/24)+8*((r-5)%24/8)+(r-5)%24%8:=by omega
      rw [he]
      apply ProcCodecGeneratedRecordPosition.property I R present vid gb fwd out h _ _ _
        (by omega) (by omega) (by omega) (fun a=>a[kZ]! =0)
      intro before after hs
      obtain ⟨tail,ht,ha⟩:=ProcPriorCodecStepRows.successful_row I R present gb fwd
        (instanceCells I R present vid) _ _ _ before after (by omega) (by omega) hs
      exact ⟨_,ha,record I R present vid _ _ _ _ _ _ _ _ tail ht⟩
    · by_cases hz:r<5+24*(R.n*R.n)+32
      · rw [ite_eq_left (by omega)]
        have he:r=5+24*(R.n*R.n)+(r-(5+24*(R.n*R.n))):=by omega
        rw [he,ProcCodecSuffixCells.hash_cell I R present vid gb fwd out h _ (by omega)]
        exact hash I R present vid _ _ _ _
      · rw [ite_eq_right (by omega)]
        have he:r=5+24*(R.n*R.n)+32+(r-(5+24*(R.n*R.n)+32)):=by omega
        rw [he,ProcCodecSuffixCells.ash_cell I R present vid gb fwd out h _ (by omega)]
        exact ash I R present vid _ _
end ZkFormal.NearV3.Candidates.ProcCodecSanityGate
