import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordBase
import ZkFormal.NearV3.Candidates.ProcPriorCodecRegisterMiss
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordReads
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecExtra ProcPriorCodecExtraColumns SchedSetAll
open ProcPriorCodecRegisterMiss

def scalars (present : Bool) (n k f g p bpo bpr : Nat) : List (Nat×Nat) :=
  [(kR,1),(pos,p),(bpost,bpo),(bpre,bpr),(vbg,b2n present),
    (kidx,k),(klo,k%256),(khi,k/256),(fS,if f=0 then 1 else 0),
    (fR,if f=1 then 1 else 0),(fA,if f=2 then 1 else 0),
    (Codec.g,g),(ig7,finv (fsub g 7)),(e7,if g=7 then 1 else 0),
    (ikl,finv (fsub k (n*n-1))),(ekl,if k+1=n*n then 1 else 0)]

theorem projection (I : Input) (present : Bool) (n k f g p bpo bpr : Nat)
    (inst extra : List (Nat×Nat)) (c : Nat) (hc:c∈untouched) :
    (recordRow I present n k f g p bpo bpr inst extra)[c]! =
      lookup extra c (lookup (inst++scalars present n k f g p bpo bpr) c 0) := by
  have hw:c<Codec.width := by
    have h : ∀c∈untouched,c<Codec.width := by decide +kernel
    exact h c hc
  unfold recordRow
  rw [SchedSetAll.cell _ _ _ hw,append,append]
  split
  · rw [prior_bits _ _ _ hc,append,post_bits _ _ _ hc]
    simp [scalars, *]
  · simp only [show ∀v,lookup [] c v=v from fun _=>rfl]
    rw [append,post_bits _ _ _ hc]
    simp [scalars, *]

/-- Native suffix writes cannot clobber record phase, byte, or instance fields. -/
theorem extra_preserves (n k f g a b c v : Nat) (tail : List (Nat×Nat)) (ht:Tail tail)
    (hc:c∈[act,tau,pres,vid,nn,NN,base,fair,kH,kR,kZ,kA,kF,ehp,fS,fR,fA,bpost,bpre]) :
    lookup (baseExtra n k f g a b++tail) c v=v := by
  apply lookup_miss
  intro q hq he
  rcases List.mem_append.mp hq with hq|hq
  · simp only [baseExtra,List.mem_cons,List.mem_nil_iff,or_false] at hq
    have dis : ∀c∈[act,tau,pres,vid,nn,NN,base,fair,kH,kR,kZ,kA,kF,ehp,fS,fR,fA,bpost,bpre],
      c∉[rs,al,gb,srcC,hasC,useC] := by decide +kernel
    apply dis c hc
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all
  · have dis : ∀c∈[act,tau,pres,vid,nn,NN,base,fair,kH,kR,kZ,kA,kF,ehp,fS,fR,fA,bpost,bpre],
      c∉tailColumns := by decide +kernel
    exact dis c hc (he ▸ ht q hq)
theorem native_projection (I : Input) (present : Bool) (n k f g p bpo bpr a b : Nat)
    (inst tail : List (Nat×Nat)) (ht:Tail tail) (c : Nat)
    (hc:c∈[act,tau,pres,vid,nn,NN,base,fair,kH,kR,kZ,kA,kF,ehp,fS,fR,fA,bpost,bpre]) :
    (recordRow I present n k f g p bpo bpr inst (baseExtra n k f g a b++tail))[c]! =
      lookup (inst++scalars present n k f g p bpo bpr) c 0 := by
  have hu:c∈untouched := by
    have h : ∀c∈[act,tau,pres,vid,nn,NN,base,fair,kH,kR,kZ,kA,kF,ehp,fS,fR,fA,bpost,bpre],c∈untouched := by decide +kernel
    exact h c hc
  rw [projection _ _ _ _ _ _ _ _ _ _ _ _ hu,extra_preserves _ _ _ _ _ _ _ _ _ ht hc]

end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordReads
