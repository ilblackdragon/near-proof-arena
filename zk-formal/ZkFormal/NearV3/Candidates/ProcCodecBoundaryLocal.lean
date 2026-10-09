import ZkFormal.NearV3.Candidates.ProcPriorCodecSideFullKind
import ZkFormal.NearV3.Candidates.ProcPriorCodecSideRecord
namespace ZkFormal.NearV3.Candidates.ProcCodecBoundaryLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash

def withoutFirst : Expr→Bool
  | .isFirst=>false
  | .add a b | .mul a b=>withoutFirst a && withoutFirst b
  | .neg a=>withoutFirst a
  | _=>true

theorem eval_withoutFirst (e : Expr) (he:withoutFirst e=true) (cur nxt : Nat→Fp)
    (first first' last trans : Fp) :
    e.evalWith (ProcPriorCells.env cur nxt first last trans)=
    e.evalWith (ProcPriorCells.env cur nxt first' last trans) := by
  induction e with
  | const n | col c nx | pub i | isLast | isTransition => rfl
  | isFirst => cases he
  | add a b ia ib =>
    have hh : withoutFirst a=true ∧ withoutFirst b=true := by simpa [withoutFirst] using he
    change _+_=_+_
    rw [ia hh.1,ib hh.2]
  | mul a b ia ib =>
    have hh : withoutFirst a=true ∧ withoutFirst b=true := by simpa [withoutFirst] using he
    change _*_= _*_
    rw [ia hh.1,ib hh.2]
  | neg a ia =>
    change -(_)= -(_)
    rw [ia he]


open ZkFormal.Chacha.Table.E in
def firstEquation : Expr := .mul .isFirst (.mul (c act) (notE (c kF)))

theorem constraints_first : ∀e∈ProcPriorCodecActual.constraints,e=firstEquation ∨ withoutFirst e=true := by
  decide +kernel

/-- Relocating an otherwise unchanged block away from global row zero clears
its first selector. The unique first-selector equation then vanishes. -/
theorem erase_first (cur nxt : Nat→Fp) (first last trans : Fp)
    (h:∀e∈ProcPriorCodecActual.constraints,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0) :
    ∀e∈ProcPriorCodecActual.constraints,e.evalWith (ProcPriorCells.env cur nxt 0 last trans)=0 := by
  intro e he
  rcases constraints_first e he with rfl|hh
  · change 0*_=0
    grind only
  · rw [eval_withoutFirst e hh cur nxt 0 first last trans]
    exact h e he

/-- The final ash byte admits a next header (or padding), even when the next
header has unrelated instance constants. All corrected constraints hold. -/
theorem ash_final (I : Input) (R : Run) (present : Bool) (vid base0 : Nat)
    (ht:R.tau<P) (nxt : Nat→Fp) (hn:nxt act=0 ∨ nxt kF=1) (trans : Fp) :
    ∀e∈ProcPriorCodecActual.constraints,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (ashRow (instanceCells I R present vid) I base0 31)[c]!) nxt 0 0 trans)=0 := by
  intro e he
  simp only [ProcPriorCodecActual.constraints,List.mem_append] at he
  rcases he with ((he|he)|he)|he
  · exact ProcPriorCodecSideFullKind.ash_final I R present vid base0 ht nxt hn trans e he
  · exact ProcPriorCodecSideRecord.ash_record I R present vid base0 31 nxt 0 0 trans e (List.mem_filter.mp he).1
  · exact ProcPriorCodecSideTrailer.ash_trailer I R present vid base0 31 nxt 0 0 trans (by simp) e he
  · exact ProcPriorCodecNativeSides.ash_additions I R present vid base0 31 nxt 0 0 trans e he

theorem ash_to_header (I : Input) (R : Run) (present : Bool) (vid base0 : Nat)
    (I' : Input) (R' : Run) (present' : Bool) (vid' : Nat)
    (ht:R.tau<P) (trans : Fp) :
    ∀e∈ProcPriorCodecActual.constraints,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (ashRow (instanceCells I R present vid) I base0 31)[c]!)
      (fun c=>Fp.ofNat (headerRow (instanceCells I' R' present' vid')
        (ProcPriorCodecNativeBytes.parameters I' R') (ProcPriorCodecNativeBytes.header R') present' 0)[c]!) 0 0 trans)=0 := by
  apply ash_final I R present vid base0 ht
  right
  rw [(ProcPriorCodecSideMultiplicity.header_flags I' R' present' vid'
    (ProcPriorCodecNativeBytes.parameters I' R') (ProcPriorCodecNativeBytes.header R') 0).2.2.2.2.1]
  rfl
end ZkFormal.NearV3.Candidates.ProcCodecBoundaryLocal
