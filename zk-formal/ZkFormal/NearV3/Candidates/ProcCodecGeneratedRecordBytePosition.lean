import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordPositionCell
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordPosition
import ZkFormal.NearV3.Candidates.ProcPriorCodecSideZero
import ZkFormal.NearV3.Candidates.ProcPriorCodecEndArithmetic
namespace ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordBytePosition
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash ProcPriorCodecStepRows

theorem record (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (k f g : Nat) (hk : k<R.n*R.n) (hf : f<3) (hg : g<8) :
    out.rows[5+24*k+8*f+g]![pos]! =5+24*k+8*f+g := by
  apply ProcCodecGeneratedRecordPosition.property I R present vidV gb fwd out h k f g hk hf hg
    (fun a=>a[pos]! =5+24*k+8*f+g)
  intro before after he
  obtain ⟨tail,ht,ha⟩ := successful_row I R present gb fwd (instanceCells I R present vidV) k f g before after hf hg he
  exact ⟨_,ha,ProcPriorCodecRecordPositionCell.cell I R present vidV k f g _ _ _ _ _ tail ht⟩

theorem region (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (r : Nat) (hl : 5≤r) (hr : r<5+24*(R.n*R.n)) : out.rows[r]![pos]! =r := by
  let k := (r-5)/24
  let f := ((r-5)%24)/8
  let g := (r-5)%8
  have hk : k<R.n*R.n := by dsimp [k]; omega
  have hf : f<3 := by dsimp [f]; omega
  have hg : g<8 := by dsimp [g]; omega
  have he : 5+24*k+8*f+g=r := by dsimp [k,f,g]; omega
  simpa only [he] using record I R present vidV gb fwd out h k f g hk hf hg

theorem hash_position (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) :
    (ProcPriorCodecAssignments.hashRow (instanceCells I R present vidV) digest hpre present base0 j)[pos]! =base0+j := by
  rw [ProcPriorCodecSideZero.hash_scalar I R present vidV digest hpre base0 j pos (by simp [ProcPriorCodecSideZero.zeroColumns])]
  simp [SchedSetAll.lookup,SchedSetAll.append,instanceCells,ProcPriorCodecHashReads.hashScalars,
    act,tau,pres,vid,nn,NN,base,fair,itz,zt,kZ,pos,sj,bpost,bpre,bsha,vbg,dgg,isj,esj]

/-- Includes byte7→next field, final field→next record, and the final
record→first hash row. The next row is selected from the actual generator. -/
theorem next (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (r : Nat) (hl : 5≤r) (hr : r<5+24*(R.n*R.n)) :
    out.rows[r+1]![pos]! =r+1 := by
  by_cases hn : r+1<5+24*(R.n*R.n)
  · exact region I R present vidV gb fwd out h (r+1) (by omega) hn
  · have he : r+1=5+24*(R.n*R.n)+0 := by omega
    rw [he,ProcCodecSuffixCells.hash_cell I R present vidV gb fwd out h 0 (by decide)]
    exact hash_position I R present vidV _ _ _ 0

def positionGroup : List Expr := (cKind.drop 77).take 1

theorem active (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (r : Nat) (hl : 5≤r) (hr : r<5+24*(R.n*R.n)) :
    ∀e∈positionGroup,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows r)=0 := by
  have hc := region I R present vidV gb fwd out h r hl hr
  have hn := next I R present vidV gb fwd out h r hl hr
  have hs : r+1<out.rows.size := by
    rw [ZkFormal.NearV3.Assembly.CodecDigest.generated_length I R present vidV gb fwd out h]
    omega
  have he : positionGroup=[.mul encG (ZkFormal.Chacha.Table.E.sub (ZkFormal.Chacha.Table.E.n pos)
      (.add (ZkFormal.Chacha.Table.E.c pos) (ZkFormal.Chacha.Table.E.k 1)))] := by decide +kernel
  rw [he]
  intro e he
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at he
  subst e
  simp only [ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcCodecPhysicalRows.rowEnvAt,ProcPriorCells.env,
    Bool.false_eq_true,ite_true,ite_false,if_pos hs,hc,hn]
  rw [ProcPriorCodecEndArithmetic.cast_add]
  grind only

theorem physical (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out) (hn : R.n≤64)
    (t r : Nat) (hl : 5≤r) (hr : r<5+24*(R.n*R.n)) (pub : List Fp) :
    ∀e∈positionGroup,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  have hcap := (ProcCodecGeneratedBits.capacity I R present vidV gb fwd out h hn).2
  have hrr : r<out.rows.size := by
    rw [ZkFormal.NearV3.Assembly.CodecDigest.generated_length I R present vidV gb fwd out h]
    omega
  intro e he
  have hp : e.pubBound=0 := (by decide +kernel : ∀e∈positionGroup,e.pubBound=0) e he
  rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t r hrr pub e hp]
  exact active I R present vidV gb fwd out h r hl hr e he
end ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordBytePosition
