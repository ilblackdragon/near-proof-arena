import ZkFormal.NearV3.Candidates.ProcPriorCodecRecordCarryFields
namespace ZkFormal.NearV3.Candidates.ProcCodecRecordCarry
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecRecordCarryFields

open ZkFormal.Chacha.Table.E in
def carryGroup : List Expr := carryColumns.map (fun c0=> .mul (sub (c kR) (c rend)) (sub (n c0) (c c0)))
open ZkFormal.Chacha.Table.E in
def startGroup : List Expr := [mul3 (c rend) (notE (c ekl)) (notE (n rs))]
def equations : List Expr := startGroup++carryGroup

theorem equations_eq : equations=(cRec.drop 35).take 6 := by decide +kernel

theorem carry_equal (cur nxt : Nat→Fp) (first last trans : Fp)
    (he:∀c∈carryColumns,nxt c=cur c) :
    ∀e∈carryGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  intro e hm
  obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hm
  change (cur kR+ -cur rend)*(nxt c+ -cur c)=0
  rw [he c hc]
  grind only

theorem carry_end (cur nxt : Nat→Fp) (first last trans : Fp) (he:cur kR=cur rend) :
    ∀e∈carryGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  intro e hm
  obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hm
  change (cur kR+ -cur rend)*(nxt c+ -cur c)=0
  rw [he]
  grind only

theorem same_record (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gbA fwd=.ok out)
    (k f g f' g' : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) (hf':f'<3) (hg':g'<8) :
    ∀c∈carryColumns,out.rows[5+24*k+8*f'+g']![c]! = out.rows[5+24*k+8*f+g]![c]! := by
  intro c hc
  have hm:c∈columns := List.mem_cons_of_mem rs hc
  rw [position I R present vid gbA fwd out h k f g hk hf hg c hm,
    position I R present vid gbA fwd out h k f' g' hk hf' hg' c hm]
  exact carry_same _ _ _ _ _ _ _ _ c hc

theorem carry_active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gbA fwd=.ok out)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) :
    ∀e∈carryGroup,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  have hl:=generated_length I R present vid gbA fwd out h
  have hn:5+24*k+8*f+g+1<out.rows.size := by omega
  obtain ⟨hR,hend,hekl⟩:=gates I R present vid gbA fwd out h k f g hk hf hg
  unfold ProcCodecPhysicalRows.rowEnvAt
  rw [if_pos hn]
  by_cases he:f=2 ∧ g=7
  · apply carry_end
    rw [hR,hend,if_pos he]
  · apply carry_equal
    intro c hc
    by_cases hg7:g<7
    · rw [show 5+24*k+8*f+g+1=5+24*k+8*f+(g+1) by omega,
        same_record I R present vid gbA fwd out h k f g f (g+1) hk hf hg hf (by omega) c hc]
    · have hgg:g=7 := by omega
      have hff:f+1<3 := by omega
      rw [show 5+24*k+8*f+g+1=5+24*k+8*(f+1)+0 by omega,
        same_record I R present vid gbA fwd out h k f g (f+1) 0 hk hf hg hff (by decide) c hc]

theorem start_active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gbA fwd=.ok out)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) :
    ∀e∈startGroup,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  have hl:=generated_length I R present vid gbA fwd out h
  have hn:5+24*k+8*f+g+1<out.rows.size := by omega
  obtain ⟨hR,hend,hekl⟩:=gates I R present vid gbA fwd out h k f g hk hf hg
  intro e hm
  simp only [startGroup,List.mem_cons,List.mem_nil_iff,or_false] at hm
  subst e
  unfold ProcCodecPhysicalRows.rowEnvAt
  rw [if_pos hn]
  simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,mul3,notE,
    Bool.false_eq_true,ite_false,ite_true,hend,hekl]
  by_cases he:f=2 ∧ g=7
  · rw [if_pos he]
    by_cases hlast:k+1=R.n*R.n
    · rw [if_pos hlast]
      change 1*(1+ -1)*_=0
      grind only
    · rw [if_neg hlast]
      obtain ⟨rfl,rfl⟩:=he
      rw [show 5+24*k+8*2+7+1=5+24*(k+1) by omega,start I R present vid gbA fwd out h (k+1) (by omega)]
      change 1*(1+ -0)*(1+ -1)=0
      decide +kernel
  · rw [if_neg he]
    change 0*_*_=0
    grind only

theorem active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gbA fwd=.ok out)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  simp only [equations,List.forall_mem_append]
  exact ⟨start_active I R present vid gbA fwd out h k f g hk hf hg,
    carry_active I R present vid gbA fwd out h k f g hk hf hg⟩

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

end ZkFormal.NearV3.Candidates.ProcCodecRecordCarry
