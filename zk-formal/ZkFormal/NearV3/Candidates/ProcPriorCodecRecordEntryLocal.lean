import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeMultiplicity
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordByteCells
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordEntryLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecStepRows ProcPriorCodecRecordStep ProcPriorCodecExtra ProcPriorCodecNativeHash

open ZkFormal.Chacha.Table.E in
def equations : List Expr :=
  [.mul (c dgg) (notE (c kZ)),.mul (c dgg) (c sj),
   .mul (.add (c fS) (c fR)) (sub (c bpre) (.mul (c pres) (c bpost)))]

theorem equations_eq : equations=(cRec.drop 17).take 3 := by decide +kernel

theorem evaluate (cur nxt : Nat→Fp) (first last trans : Fp) (hd:cur dgg=0)
    (hi:(cur fS+cur fR)*(cur bpre-cur pres*cur bpost)=0) :
    ∀e∈equations,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  intro e hm
  simp only [equations,List.mem_cons,List.mem_nil_iff,or_false] at hm
  rcases hm with rfl|rfl|rfl
  all_goals simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,notE,
    Bool.false_eq_true,ite_false,hd]
  all_goals grind only

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f gg : Nat) (s out : State)
    (hf:f<3) (hg:gg<8)
    (h:step I R present gb fwd (instanceCells I R present vidV) k f gg s=.ok (.yield out)) :
    ∃a,out.1=s.1.push a ∧ ∀(nxt : Nat→Fp) (first last trans : Fp),
      ∀e∈equations,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨tail,ht,hr⟩:=successful_row I R present gb fwd (instanceCells I R present vidV) k f gg s out hf hg h
  let a:=record I R present (instanceCells I R present vidV)
    (baseExtra R.n k f gg (b2n I.allowed[k]!) gb[k]!++tail) k f gg
  have hd:a[dgg]! = 0 := by
    dsimp only [a,record]
    apply ZkFormal.NearV3.Assembly.CodecDigest.record_digest_gate
    exact ProcPriorCodecExtraColumns.extra_avoids_dgg _ _ _ _ _ _ tail ht
  let bpo := if f<2 then idByte I.ids k (8*f+gg) else if gg<3 then (R.segs.getD k default).vfin/256^gg%256 else 0
  let bpr := if ¬present then 0 else if f<2 then bpo else (Array.replicate (R.n*R.n) 0)[k]!/256^gg%256
  have hflags:=ProcPriorCodecRecordKind.flags I R present vidV k f gg
    (5+24*k+8*f+gg) bpo bpr (b2n I.allowed[k]!) gb[k]! tail ht
  have hbytes:=ProcPriorCodecRecordByteCells.cells I R present vidV k f gg
    (5+24*k+8*f+gg) bpo bpr (b2n I.allowed[k]!) gb[k]! tail ht
  have hS:a[fS]! =(if f=0 then 1 else 0) := hflags.2.2.2.2.2.2.2.1
  have hR:a[fR]! =(if f=1 then 1 else 0) := hflags.2.2.2.2.2.2.2.2.1
  have hpr:a[pres]! =b2n present := hbytes.1
  have hpost:a[bpost]! =(if f<2 then idByte I.ids k (8*f+gg) else if gg<3 then (R.segs.getD k default).vfin/256^gg%256 else 0) := hbytes.2.1
  have hpre:a[bpre]! =(if ¬present then 0 else if f<2 then (if f<2 then idByte I.ids k (8*f+gg) else if gg<3 then (R.segs.getD k default).vfin/256^gg%256 else 0) else (Array.replicate (R.n*R.n) 0)[k]!/256^gg%256) := hbytes.2.2.1
  refine ⟨a,hr,?_⟩
  intro nxt first last trans
  apply evaluate
  · rw [hd]; rfl
  · rw [hS,hR,hpr,hpost,hpre]
    have hff:f=0∨f=1∨f=2 := by omega
    rcases hff with rfl|rfl|rfl
    all_goals cases present
    all_goals simp only [b2n,Bool.false_eq_true,Bool.true_eq_false,not_false_eq_true,not_true_eq_false,
      ite_true,ite_false,show (0:Nat)<2 by decide,show (1:Nat)<2 by decide,show ¬(2:Nat)<2 by decide,
      show (0:Nat)≠1 by decide,show (1:Nat)≠0 by decide,show (2:Nat)≠0 by decide,show (2:Nat)≠1 by decide]
    all_goals try simp only [show Fp.ofNat 0=0 by rfl,show Fp.ofNat 1=1 by rfl]
    all_goals grind only

end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordEntryLocal
