import ZkFormal.NearV3.Candidates.SourceDictionaryBudget
import ZkFormal.Size.V3Synth
namespace ZkFormal.NearV3.Candidates.UniqueSourceCharge
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl Rcpt.Candidates SrcpV3

def sizeStep (B : SrcpB) : Nat := if B.dup then 0 else B.L+44+33*B.path.length
def size (bs : List SrcpB) : Nat := (bs.map sizeStep).sum

def initial : Expr := .mul .isFirst
  (sub (c sz) (.mul (sub (c rt) (c dup)) (.add (c L) (k 44))))
def step : Expr := .mul .isTransition
  (sub (n sz) (sum [c sz,.mul (sub (n rt) (n dup)) (.add (n L) (k 44)),
    smul 33 (mul3 (n sf) (n sg) (not (n lf)))]))

def constraints : List Expr := DedupTable.constraints.take 51++[initial,step]++DedupTable.constraints.drop 53

def table (cap : Nat) : Air.Table := {DedupTable.table cap with constraints:=constraints}

set_option maxRecDepth 32768 in
theorem replaced_indices : DedupTable.constraints[51]?=some (.mul .isFirst (sub (c sz) (c L))) ∧
    DedupTable.constraints[52]?=some (.mul .isTransition (sub (n sz) (sum [c sz,.mul (n rt) (n L),
      smul 33 (mul3 (n sf) (n sg) (not (n lf)))]))) := by decide +kernel

set_option maxRecDepth 32768 in
theorem shape : ZkFormal.Size.shapeOf 2 (table 22)=ZkFormal.Size.shapeOf 2 (DedupTable.table 22) := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem wf : (table 22).wf ⟨[table 22],67,202⟩ 8=true := by decide +kernel

/-- Duplicate references carry no serialized dictionary entry; computed entries
pay their full encoding apart from the outer four-byte vector prefix. -/
theorem computed_sum (bs : List SrcpB) :
    size bs=((bs.filter fun B=>!B.dup).map fun B=>B.L+33*B.path.length).sum+
      44*(bs.filter fun B=>!B.dup).length := by
  induction bs with
  | nil => rfl
  | cons B bs ih => cases h : B.dup <;> simp [size,sizeStep,h] at * <;> omega

/-- Compare to old accounting without assuming unused witness byte margin. -/
theorem old_delta (bs : List SrcpB) (h : ∀B∈bs,B.dup=true→B.L=12) :
    size bs+56*(bs.filter fun B=>B.dup).length=DedupRender.size bs+44*bs.length := by
  induction bs with
  | nil => rfl
  | cons B bs ih =>
    have hh:=h B (by simp)
    have ht:=ih (fun B hB=>h B (by simp [hB]))
    cases hd : B.dup <;> simp [size,sizeStep,DedupRender.size,DedupRender.sizeStep,hd,hh] at * <;> omega

theorem repeated_accounting_fixed :
    size [SourceDictionaryBudget.emptySource false,SourceDictionaryBudget.emptySource true]+4=
      (NearSpecV3.encList ZkFormal.V3.encodeEntry [SourceDictionaryBudget.emptyEntry]).length := by
  decide +kernel
end ZkFormal.NearV3.Candidates.UniqueSourceCharge
