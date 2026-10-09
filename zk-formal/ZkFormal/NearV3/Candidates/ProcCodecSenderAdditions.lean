import ZkFormal.NearV3.Candidates.ProcPriorCodecSenderCells
import ZkFormal.NearV3.Candidates.ProcCodecRecordEntry
namespace ZkFormal.NearV3.Candidates.ProcCodecSenderAdditions
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcPriorCodecSenderCells
open ZkFormal.Chacha.Table.E in
def equations : List Expr :=
  [.mul (c fS) (sub (c bpost) (c (prbit 0)))]++
  (List.range 7).map (fun i=>mul3 (c fS) (notE (c e7)) (sub (n (prbit i)) (c (prbit (i+1)))))

theorem equations_eq : equations=ProcPriorCodecActual.additions.drop 11 := by decide +kernel

theorem evaluate (cur nxt : Nat→Fp) (first last trans : Fp)
    (hbyte:cur fS=0 ∨ cur bpost=cur (prbit 0))
    (hshift:cur fS=0 ∨ cur e7=1 ∨ ∀i<7,nxt (prbit i)=cur (prbit (i+1))) :
    ∀e∈equations,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  intro e hm
  simp only [equations,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,List.mem_map] at hm
  rcases hm with rfl|⟨i,hi,rfl⟩
  · change cur fS*(cur bpost+ -cur (prbit 0))=0
    rcases hbyte with hbyte|hbyte
    all_goals rw [hbyte]
    all_goals grind only
  · change cur fS*(1+ -cur e7)*(nxt (prbit i)+ -cur (prbit (i+1)))=0
    rcases hshift with hs|hs|hs
    · rw [hs]; grind only
    · rw [hs]; grind only
    · rw [hs i (List.mem_range.mp hi)]; grind only

theorem active (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gbA fwd=.ok out) (hnIds:R.n=I.ids.length)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) :
    ∀e∈equations,e.evalWith (ProcCodecPhysicalRows.rowEnvAt out.rows (5+24*k+8*f+g))=0 := by
  have hl:=generated_length I R present vid gbA fwd out h
  have hn:5+24*k+8*f+g+1<out.rows.size := by omega
  have sh:=ProcCodecRecordTransitionShape.record I R present vid gbA fwd out h k f g hk hf hg
  have hS:=sh.2.2.2.1
  have h7:=sh.2.2.1
  unfold ProcCodecPhysicalRows.rowEnvAt
  rw [ite_eq_left hn]
  apply evaluate
  · by_cases hf0:f=0
    · right
      subst f
      obtain ⟨hpost,hr⟩:=position I R present vid gbA fwd out h k g hk hg
      rw [hpost,hr 0 (by decide)]
      congr 1
      rw [Nat.add_zero,bytes_get _ g hg,hnIds]
      simp [Sched.idByte,hg,Nat.mod_eq_of_lt hg]
    · left
      rw [hS,ite_eq_right hf0]
      rfl
  · by_cases hf0:f=0
    · right
      by_cases hg7:g=7
      · left
        rw [h7,ite_eq_left hg7]
        rfl
      · right
        subst f
        intro i hi
        have hi':i<8 := by omega
        have hii:i+1<8 := by omega
        have hg':g+1<8 := by omega
        have he:5+24*k+8*0+g+1=5+24*k+8*0+(g+1) := by omega
        rw [he,(position I R present vid gbA fwd out h k (g+1) hk hg').2 i hi',
          (position I R present vid gbA fwd out h k g hk hg).2 (i+1) hii]
        congr 2
        omega
    · left
      rw [hS,ite_eq_right hf0]
      rfl

theorem physical (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) (hn:R.n≤64) (hnIds:R.n=I.ids.length)
    (k f g : Nat) (hk:k<R.n*R.n) (hf:f<3) (hg:g<8) (t : Nat) (pub : List Fp) :
    ∀e∈equations,e.eval
      (SchedHeight.trace out.rows codecPad) t (5+24*k+8*f+g) pub=0 := by
  obtain ⟨hne,hcap⟩:=ProcCodecGeneratedBits.capacity I R present vid gb fwd out h hn
  have hl:=generated_length I R present vid gb fwd out h
  intro e he
  have hb:e.pubBound=0 := (by decide +kernel : ∀e∈equations,e.pubBound=0) e he
  rw [ProcCodecPhysicalRows.generated_eval out.rows hcap t _ (by omega) pub e hb]
  exact active I R present vid gb fwd out h hnIds k f g hk hf hg e he

theorem physical_record_range (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) (hn:R.n≤64) (hnIds:R.n=I.ids.length)
    (t r : Nat) (hlo:5≤r) (hhi:r<5+24*(R.n*R.n)) (pub : List Fp) :
    ∀e∈equations,e.eval (SchedHeight.trace out.rows codecPad) t r pub=0 := by
  have he:r=5+24*((r-5)/24)+8*((r-5)%24/8)+(r-5)%24%8 := by omega
  rw [he]
  exact physical I R present vid gb fwd out h hn hnIds ((r-5)/24) ((r-5)%24/8) ((r-5)%24%8)
    (by omega) (by omega) (by omega) t pub

end ZkFormal.NearV3.Candidates.ProcCodecSenderAdditions
