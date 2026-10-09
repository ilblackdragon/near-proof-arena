import ZkFormal.NearV3.Candidates.UniqueSourceRender
import ZkFormal.NearV3.Rcpt.Candidates.DedupLayoutFacts
namespace ZkFormal.NearV3.Candidates.UniqueSourceCounter
open ZkFormal.Near Rcpt.Candidates Render.SrcpGen

def amount (B : SrcpB) (before : Nat) : Kind→Nat
  | .root => before+if B.dup then 0 else B.L+44
  | .leaf _ => before+B.L+44
  | .path i _ => before+B.L+44+33*(i+1)

def increment (B : SrcpB) : Kind→Nat
  | .root => if B.dup then 0 else B.L+44
  | .leaf _ => 0
  | .path _ o => if o=0 then 33 else 0

theorem active (bs : List SrcpB) (r : Nat) (hr : r<DedupRender.R bs) :
    UniqueSourceRender.counter bs r=
      let p:=(DedupRender.recs bs).getD r default
      amount (bs.getD p.1 default) (UniqueSourceCharge.size (bs.take p.1)) p.2 := by
  simp only [UniqueSourceRender.counter,hr,ite_true]
  split <;> simp_all [amount]

theorem last_amount (B : SrcpB) (before : Nat) :
    amount B before (DedupRender.lastKind B)=before+UniqueSourceCharge.sizeStep B := by
  cases hd : B.dup
  · by_cases hp : B.path.length=0
    · simp [DedupRender.lastKind,lastKind,hd,hp,amount,UniqueSourceCharge.sizeStep,Nat.add_assoc]
    · have he : B.path.length-1+1=B.path.length := by omega
      simp [DedupRender.lastKind,lastKind,hd,hp,amount,UniqueSourceCharge.sizeStep,he,Nat.add_assoc]
  · simp [DedupRender.lastKind,hd,amount,UniqueSourceCharge.sizeStep]

theorem take_next (bs : List SrcpB) (i : Nat) (hi : i<bs.length) :
    UniqueSourceCharge.size (bs.take (i+1))=UniqueSourceCharge.size (bs.take i)+
      UniqueSourceCharge.sizeStep (bs.getD i default) := by
  have hh : bs.take (i+1)=bs.take i++[bs[i]] := by
    induction bs generalizing i with
    | nil => simp at hi
    | cons b bs ih =>
      cases i with
      | zero => simp
      | succ i => simpa using congrArg (List.cons b) (ih i (by simpa using hi))
  rw [hh]
  simp only [UniqueSourceCharge.size,List.map_append,List.map_cons,List.map_nil,List.sum_append,
    List.sum_cons,List.sum_nil,Nat.add_zero,List.getD,List.getElem?_eq_getElem hi,Option.getD_some]

theorem last_counter (bs : List SrcpB) (hn : bs≠[]) :
    UniqueSourceRender.counter bs (DedupRender.R bs-1)=UniqueSourceCharge.size bs := by
  have hR:=DedupRender.R_pos hn
  have hp : 0<bs.length := by cases bs <;> simp_all
  have hi : bs.length-1<bs.length := by omega
  have he : bs.length-1+1=bs.length := by omega
  rw [active bs _ (by omega),DedupRender.lastAt hn]
  dsimp only
  rw [last_amount,←take_next bs _ hi,he]
  simp

/-- An internal successor increments only at the first byte of a path item. -/
theorem internal (B : SrcpB) (before : Nat) (k next : Kind)
    (hk : k∈DedupRender.kinds B) (hn : DedupRender.nextKind B k=some next) :
    amount B before next=amount B before k+increment B next := by
  have hd : B.dup=false := by cases h : B.dup <;> simp_all [DedupRender.nextKind]
  simp only [DedupRender.nextKind,hd,Bool.false_eq_true,ite_false] at hn
  cases k with
  | root => simp [nextKind] at hn;subst next;simp [amount,increment,hd,Nat.add_assoc]
  | leaf p =>
    simp only [nextKind] at hn
    split at hn
    · cases hn;simp [amount,increment]
    · split at hn
      · cases hn;simp [amount,increment] <;> omega
      · cases hn
  | path i o =>
    simp only [nextKind] at hn
    split at hn
    · cases hn;simp [amount,increment]
    · split at hn
      · cases hn;simp [amount,increment] <;> omega
      · cases hn
/-- Actual consecutive generated rows, including cross-block transitions,
obey the corrected natural accumulator recurrence. -/
theorem active_step (bs : List SrcpB) (r : Nat) (hr : r+1<DedupRender.R bs) :
    UniqueSourceRender.counter bs (r+1)=UniqueSourceRender.counter bs r+
      let p:=(DedupRender.recs bs).getD (r+1) default
      increment (bs.getD p.1 default) p.2 := by
  have hc : r<DedupRender.R bs := by omega
  have hm:=DedupRender.mem_recs (DedupRender.descriptor_mem hc)
  rw [active bs r hc,active bs (r+1) hr]
  dsimp only
  rcases DedupRender.adjAt hr with ⟨hn,hi⟩|⟨hn,hi⟩
  · rw [hi]
    exact internal _ _ _ _ hm.2 hn
  · have hk:=DedupRender.none_last _ _ hm.2 hn
    rw [hi,hk]
    dsimp only
    rw [last_amount,take_next bs _ hm.1]
    rfl

end ZkFormal.NearV3.Candidates.UniqueSourceCounter
