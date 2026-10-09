import ZkFormal.NearV3.Candidates.ProcPriorCodecIndexSuccessor
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndIndexData
import ZkFormal.NearV3.Candidates.ProcCodecPhysicalAdditionGroups
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedIndexTransition
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.Chacha.Table.E

def equations : List Expr := (ProcPriorCodecActual.additions.drop 8).take 2

theorem record (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  let r:=5+24*k+8*f+g
  have hdata : out.rows[r]![srcC]! =k/R.n ∧ out.rows[r]![useC]! =k%R.n ∧
      out.rows[r]![hasC]! =(if k%R.n+1=R.n then 1 else 0) ∧
      out.rows[r]![rend]! =(if f=2 ∧ g=7 then 1 else 0) ∧
      out.rows[r]![ekl]! =(if k+1=R.n*R.n then 1 else 0) ∧ out.rows[r]![fA]! =(if f=2 then 1 else 0) := by
    apply ProcCodecGeneratedRecordPosition.property I R present vidV gb fwd out h k f g hk hf hg
      (fun a=>a[srcC]! =k/R.n ∧ a[useC]! =k%R.n ∧ a[hasC]! =(if k%R.n+1=R.n then 1 else 0) ∧
        a[rend]! =(if f=2 ∧ g=7 then 1 else 0) ∧ a[ekl]! =(if k+1=R.n*R.n then 1 else 0) ∧ a[fA]! =(if f=2 then 1 else 0))
    intro before after hs
    exact ProcPriorCodecEndIndexData.actual I R present gb fwd vidV k f g before after hk hf hg hs
  obtain ⟨hsrc,huse,hhas,hrend,hekl,_⟩:=hdata
  have hlen:=ZkFormal.NearV3.Assembly.CodecDigest.generated_length I R present vidV gb fwd out h
  have hnext:r+1<out.rows.size := by dsimp [r]; omega
  have he : equations=[mul3 (c rend) (notE (c ekl)) (sub (n srcC) (.add (c srcC) (c hasC))),
      mul3 (c rend) (notE (c ekl)) (sub (n useC) (.mul (notE (c hasC)) (.add (c useC) (ZkFormal.Chacha.Table.E.k 1))))] := by decide +kernel
  change ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0
  rw [he]
  simp only [List.forall_mem_cons,List.forall_mem_nil]
  simp only [mul3,notE,sub,c,n,ZkFormal.Chacha.Table.E.k,Expr.evalWith,
    ProcCodecPhysicalRows.rowEnvAt,ProcPriorCells.env,Bool.false_eq_true,ite_false,ite_true,if_pos hnext]
  simp only [List.not_mem_nil,false_implies,forall_const,show Fp.ofNat 1=(1:Fp) from rfl]
  by_cases hterm:f=2 ∧ g=7
  · by_cases hlast:k+1=R.n*R.n
    · rw [hekl,if_pos hlast]
      change _*((1:Fp)+ -1)*_=0 ∧ _*((1:Fp)+ -1)*_=0 ∧ True
      grind only
    · obtain ⟨rfl,rfl⟩:=hterm
      have hk1:k+1<R.n*R.n := by omega
      have hp : out.rows[5+24*(k+1)+8*0+0]![srcC]! =(k+1)/R.n ∧
          out.rows[5+24*(k+1)+8*0+0]![useC]! =(k+1)%R.n := by
        apply ProcCodecGeneratedRecordPosition.property I R present vidV gb fwd out h (k+1) 0 0 hk1 (by decide) (by decide)
          (fun a=>a[srcC]! =(k+1)/R.n ∧ a[useC]! =(k+1)%R.n)
        intro before after hs
        obtain ⟨a,ha,hsrc,huse,_⟩:=ProcPriorCodecStartIndexData.actual I R present gb fwd vidV (k+1) 0 0 before after (by decide) (by decide) hs
        exact ⟨a,ha,hsrc,huse⟩
      have heq:r+1=5+24*(k+1)+8*0+0 := by dsimp [r]; omega
      have hnp:0<R.n := Nat.pos_of_ne_zero (by intro he; simp [he] at hk)
      obtain ⟨hsucc,usucc⟩:=ProcPriorCodecIndexSuccessor.field R.n k hnp
      rw [heq,hp.1,hp.2,hsrc,huse,hhas,hsucc,usucc]
      rw [Lean.Grind.Ring.sub_eq_add_neg]
      grind only
  · rw [hrend,if_neg hterm]
    change (0:Fp)*_*_=0 ∧ (0:Fp)*_*_=0 ∧ True
    grind only

theorem active (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out) (hn:0<R.n)
    (r : Nat) (hr:r<out.rows.size) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  exact ProcCodecPhysicalAdditionGroups.active_of_records I R present vidV gb fwd out h hn equations
    (fun _ he=>List.mem_of_mem_drop (List.mem_of_mem_take he))
    (fun k f g hk hf hg=>record I R present vidV gb fwd out h k f g hk hf hg) r hr

theorem physical (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out) (hn1:0<R.n) (hn:R.n≤64)
    (t r : Nat) (hr:r<2^22) (pub : List Fp) :
    ∀e∈equations,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  obtain ⟨hne,hcap⟩:=ProcCodecGeneratedBits.capacity I R present vidV gb fwd out h hn
  intro e he
  by_cases ha:r<out.rows.size
  · have hp:e.pubBound=0 := (by decide +kernel : ∀e∈equations,e.pubBound=0) e he
    rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t r ha pub e hp]
    exact active I R present vidV gb fwd out h hn1 r ha e he
  · apply (ProcCodecPhysicalPadding.physical_local out.rows hne t r (by omega) hr pub).1 e
    unfold ProcPriorCodecActual.table ProcPriorCodecActual.constraints
    exact List.mem_append_right _ (List.mem_of_mem_drop (List.mem_of_mem_take he))
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedIndexTransition
