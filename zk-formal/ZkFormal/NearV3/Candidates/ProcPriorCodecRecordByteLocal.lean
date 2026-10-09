import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordByteCells
import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordBoolCells
import ZkFormal.NearV3.Candidates.ProcPriorCodecSideBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecRecordByteLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash ProcPriorCodecStepRows ProcPriorCodecExtra
open ProcPriorCodecSideBytes

def post (I : Input) (R : Run) (k f g : Nat) : Nat :=
  if f<2 then idByte I.ids k (8*f+g) else if g<3 then (R.segs.getD k default).vfin/256^g%256 else 0

theorem post_bound (I : Input) (R : Run) (k f g : Nat) : post I R k f g<256 := by
  unfold post
  split
  · exact Nat.mod_lt _ (by decide)
  · split
    · exact Nat.mod_lt _ (by decide)
    · decide

theorem actual (I : Input) (R : Run) (present : Bool) (gb : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f g : Nat) (s out : State) (hf:f<3) (hg:g<8)
    (h : step I R present gb fwd (instanceCells I R present vidV) k f g s=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=s.1.push a ∧ ∀e∈byteGroup,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  obtain ⟨tail,ht,ha⟩ := successful_row I R present gb fwd (instanceCells I R present vidV) k f g s out hf hg h
  let a:=record I R present (instanceCells I R present vidV)
    (baseExtra R.n k f g (b2n I.allowed[k]!) gb[k]!++tail) k f g
  have hcells : a[pres]! =b2n present ∧ a[bpost]! =post I R k f g ∧
      a[bpre]! =(if ¬present then 0 else if f<2 then post I R k f g else (Array.replicate (R.n*R.n) 0)[k]!/256^g%256) ∧
      a[vbg]! =b2n present ∧ a[kH]! =0 ∧ a[kR]! =1 ∧ a[kZ]! =0 :=
    ProcPriorCodecRecordByteCells.cells I R present vidV k f g _ _ _ _ _ tail ht
  obtain ⟨hpres,hpost,hpre,hv,hH,hR,hZ⟩ := hcells
  have hb : ∀i,i<8→a[pbit i]! =bit (post I R k f g) i := by
    intro i hi
    dsimp only [a,record,post]
    apply ProcPriorCodecRecordBoolCells.post_bit
    · exact hi
    · intro x hx heq
      have hm:∀c∈[rs,al,Codec.gb,srcC,hasC,useC]++ProcPriorCodecExtraColumns.tailColumns,
          ∀i:Fin 8,c≠pbit i.val := by decide +kernel
      apply hm x.1 _ ⟨i,hi⟩ heq
      rcases List.mem_append.mp hx with hx|hx
      · simp only [baseExtra,List.mem_cons,List.mem_nil_iff,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> simp
      · exact List.mem_append_right _ (ht x hx)
  have hbits := bits_value a (post I R k f g) (post_bound I R k f g) hb nxt first last trans
  refine ⟨a,ha,?_⟩
  intro e he
  simp only [byteGroup,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|rfl|rfl
  · change encG.evalWith _*(Fp.ofNat a[bpost]! + -pbitsE.evalWith _)=0
    rw [hpost,hbits]; grind only
  · simp only [ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.c,notE,Expr.evalWith,ProcPriorCells.env,
      Bool.false_eq_true,ite_false,hpres,hpre]
    cases present <;> simp only [b2n,Bool.false_eq_true,ite_false,ite_true]
    all_goals try simp only [←Fp.ofNat_def]
    all_goals grind only
  · simp only [ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,encG,Expr.evalWith,
      ProcPriorCells.env,Bool.false_eq_true,ite_false,hv,hpres,hH,hR,hZ]
    cases present <;> decide +kernel
end ZkFormal.NearV3.Candidates.ProcPriorCodecRecordByteLocal
