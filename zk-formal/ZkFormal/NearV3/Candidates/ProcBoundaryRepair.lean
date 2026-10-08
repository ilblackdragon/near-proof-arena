import ZkFormal.NearV3.Candidates.ProcKeyInterior
import ZkFormal.Size.V3Synth
namespace ZkFormal.NearV3.Candidates.ProcBoundaryRepair
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched
open ZkFormal.Chacha.Table.E

def rotation (i : Nat) : Expr :=
  .mul (sub (c Proc.kK) (.mul (c Proc.kl) (n Proc.kK)))
    (sub (n (Proc.colL i)) (c (Proc.colL ((i+1)%16))))

def cKey : List Expr := Proc.cKey.take 13 ++ (List.range 16).map rotation ++ Proc.cKey.drop 29

def table : Air.Table := { Proc.table with constraints := Proc.cKind ++ cKey ++ Proc.cHdr ++ Proc.cEnt }

theorem shape : ZkFormal.Size.shapeOf 2 table=ZkFormal.Size.shapeOf 2 Proc.table := by decide +kernel

theorem wf : table.wf ⟨[table],67,202⟩ 8=true := by decide +kernel

theorem degree : table.allConstraints.foldl (fun d e=>max d e.degree) 0=
    Proc.table.allConstraints.foldl (fun d e=>max d e.degree) 0 := by decide +kernel

/-- Within a key block or on entry to its header, the original seed rotation is unchanged. -/
theorem rotation_agrees (tr : Trace Fp) (t r i : Nat) (pub : List Fp)
    (h : tr.cell t r Proc.kl=0 ∨ tr.cell t ((r+1)%tr.height t) Proc.kK=0) :
    (rotation i).eval tr t r pub=
      (Expr.mul (c Proc.kK) (sub (n (Proc.colL i)) (c (Proc.colL ((i+1)%16))))).eval tr t r pub := by
  change (tr.cell t r Proc.kK + -(tr.cell t r Proc.kl*tr.cell t ((r+1)%tr.height t) Proc.kK))*_=
    tr.cell t r Proc.kK*_
  rcases h with h | h <;> rw [h] <;> grind

/-- The boundary between native instances does not tie their independently bound keys. -/
theorem boundary_zero (tr : Trace Fp) (t r i : Nat) (pub : List Fp)
    (hk : tr.cell t r Proc.kK=1) (hl : tr.cell t r Proc.kl=1)
    (hn : tr.cell t ((r+1)%tr.height t) Proc.kK=1) :
    (rotation i).eval tr t r pub=0 := by
  change (tr.cell t r Proc.kK + -(tr.cell t r Proc.kl*tr.cell t ((r+1)%tr.height t) Proc.kK))*_=0
  rw [hk,hl,hn]
  grind

theorem rotation_of_old (tr : Trace Fp) (t r i : Nat) (pub : List Fp)
    (hkl : (Expr.mul (c Proc.kl) (Proc.notE (c Proc.kK))).eval tr t r pub=0)
    (hold : (Expr.mul (c Proc.kK) (sub (n (Proc.colL i)) (c (Proc.colL ((i+1)%16))))).eval tr t r pub=0) :
    (rotation i).eval tr t r pub=0 := by
  change tr.cell t r Proc.kl*(1 + -tr.cell t r Proc.kK)=0 at hkl
  change tr.cell t r Proc.kK * (tr.cell t ((r+1)%tr.height t) (Proc.colL i) +
    -tr.cell t r (Proc.colL ((i+1)%16)))=0 at hold
  change (tr.cell t r Proc.kK + -(tr.cell t r Proc.kl*tr.cell t ((r+1)%tr.height t) Proc.kK))*
    (tr.cell t ((r+1)%tr.height t) (Proc.colL i) + -tr.cell t r (Proc.colL ((i+1)%16)))=0
  grind
end ZkFormal.NearV3.Candidates.ProcBoundaryRepair
