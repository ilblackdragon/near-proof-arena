import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordEntryLocal
import ZkFormal.NearV3.Candidates.ProcCodecGeneratedRecordPrefix
import ZkFormal.NearV3.Candidates.ProcCodecRecordTransitionShape
import ZkFormal.NearV3.Candidates.ProcPriorCodecAccumulatorRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecAllowanceData
namespace ZkFormal.NearV3.Candidates.ProcCodecRecordEntry
set_option maxRecDepth 8192
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest
open ZkFormal.Chacha.Table.E in
def resetGroup : List Expr :=
  [mul3 (c e7) (c fR) (n ap),mul3 (c e7) (c fR) (n big),
   mul3 (c e7) (c fR) (n apost),mul3 (c e7) (c fR) (sub (n wt) (k 1)),
   mul3 (c e7) (c fR) (sub (n lowf) (k 1))]
def equations : List Expr := ProcPriorCodecRecordEntryLocal.equations++resetGroup

theorem equations_eq : equations=(cRec.drop 17).take 8 := by decide +kernel

theorem reset_cells (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gbA fwd=.ok out)
    (k : Nat) (hk:k<R.n*R.n) :
    let a:=out.rows[5+24*k+8*2+0]!
    a[ap]! =0 ∧ a[big]! =0 ∧ a[apost]! =0 ∧ a[wt]! =1 ∧ a[lowf]! =1 := by
  obtain ⟨rows,cmps,before,after,hprefix,hs,_,ha⟩:=
    ProcCodecGeneratedRecordPrefix.cell I R present vid gbA fwd out h k 2 0 hk (by decide) (by decide)
  have hb:before=(rows,cmps,0,0,0,0) := by simpa [pure,Except.pure] using hprefix.symm
  obtain ⟨a,hpush,hap,hapost,hbig⟩:=ProcPriorCodecAccumulatorRows.cells I R present gbA fwd
    (ProcPriorCodecNativeHash.instanceCells I R present vid) k 0 before after (by decide) hs
  have he:a=out.rows[5+24*k+8*2+0]! := Array.push_inj_right.mp (hpush.symm.trans ha)
  subst a
  obtain ⟨a,hpush,_,_,_,hlow,hwt,_⟩:=ProcPriorCodecAllowanceData.cells I R present gbA fwd
    (ProcPriorCodecNativeHash.instanceCells I R present vid) k 0 before after (by decide) hk hs
  have he:a=out.rows[5+24*k+8*2+0]! := Array.push_inj_right.mp (hpush.symm.trans ha)
  subst a
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [hb] using hap
  · simpa [hb] using hbig
  · simpa [hb] using hapost
  · simpa [P] using hwt
  · simpa using hlow

theorem reset_active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gbA fwd=.ok out)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) :
    ∀e∈resetGroup,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  have hl:=generated_length I R present vid gbA fwd out h
  have hn:5+24*k+8*f+g+1<out.rows.size := by omega
  have sh:=ProcCodecRecordTransitionShape.record I R present vid gbA fwd out h k f g hk hf hg
  have h7:=sh.2.2.1
  have hR:=sh.2.2.2.2.1
  have hz : (Fp.ofNat out.rows[5+24*k+8*f+g]![e7]!)*(Fp.ofNat out.rows[5+24*k+8*f+g]![fR]!)=0 ∨
      (out.rows[5+24*k+8*f+g+1]![ap]! =0 ∧ out.rows[5+24*k+8*f+g+1]![big]! =0 ∧
       out.rows[5+24*k+8*f+g+1]![apost]! =0 ∧ out.rows[5+24*k+8*f+g+1]![wt]! =1 ∧
       out.rows[5+24*k+8*f+g+1]![lowf]! =1) := by
    by_cases he:g=7 ∧ f=1
    · right
      obtain ⟨rfl,rfl⟩:=he
      have hi:5+24*k+8*1+7+1=5+24*k+8*2+0 := by omega
      rw [hi]
      exact reset_cells I R present vid gbA fwd out h k hk
    · left
      rw [h7,hR]
      by_cases hg7:g=7
      · have hf1:f≠1 := by omega
        rw [ite_eq_left hg7,ite_eq_right hf1]
        change 1*0=0
        decide +kernel
      · rw [ite_eq_right hg7]
        change 0*_=0
        grind only
  intro e hm
  simp only [resetGroup,List.mem_cons,List.mem_nil_iff,or_false] at hm
  unfold ProcCodecPhysicalRows.rowEnvAt
  rw [ite_eq_left hn]
  rcases hz with hz|⟨ha,hb,hap,hw,hlow⟩
  · rcases hm with rfl|rfl|rfl|rfl|rfl
    all_goals change (Fp.ofNat _)*(Fp.ofNat _)*_=0
    all_goals rw [hz]
    all_goals grind only
  · rcases hm with rfl|rfl|rfl|rfl|rfl
    all_goals simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,mul3,
      Bool.false_eq_true,ite_false,ite_true,ha,hb,hap,hw,hlow,
      show Fp.ofNat 0=0 by rfl,show Fp.ofNat 1=1 by rfl]
    all_goals grind only

theorem active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gbA fwd=.ok out)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  simp only [equations,List.forall_mem_append]
  refine ⟨?_,reset_active I R present vid gbA fwd out h k f g hk hf hg⟩
  have hp:=ProcCodecGeneratedRecordPosition.property I R present vid gbA fwd out h k f g hk hf hg
    (fun a=>∀(nxt:Nat→Fp) (first last trans:Fp),∀e∈ProcPriorCodecRecordEntryLocal.equations,
      e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0)
    (fun before after hs=>ProcPriorCodecRecordEntryLocal.actual I R present gbA fwd vid k f g before after hf hg hs)
  exact hp _ _ _ _

theorem physical (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) (hn:R.n≤64)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) (t : Nat) (pub : List Fp) :
    ∀e∈equations,e.eval
      (SchedHeight.trace out.rows codecPad) t (5+24*k+8*f+g) pub=0 := by
  obtain ⟨hne,hcap⟩:=ProcCodecGeneratedBits.capacity I R present vid gb fwd out h hn
  have hl:=generated_length I R present vid gb fwd out h
  intro e he
  have hb:e.pubBound=0 := (by decide +kernel : ∀e∈equations,e.pubBound=0) e he
  rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t _ (by omega) pub e hb]
  exact active I R present vid gb fwd out h k f g hk hf hg e he

theorem physical_record_range (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) (hn:R.n≤64)
    (t r : Nat) (hlo:5≤r) (hhi:r<5+24*(R.n*R.n)) (pub : List Fp) :
    ∀e∈equations,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  have he:r=5+24*((r-5)/24)+8*((r-5)%24/8)+(r-5)%24%8 := by omega
  rw [he]
  exact physical I R present vid gb fwd out h hn ((r-5)/24) ((r-5)%24/8) ((r-5)%24%8)
    (by omega) (by omega) (by omega) t pub

end ZkFormal.NearV3.Candidates.ProcCodecRecordEntry
