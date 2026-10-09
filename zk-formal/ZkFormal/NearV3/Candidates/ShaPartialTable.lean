import ZkFormal.NearV3.Candidates.ShaPartialBytes
import ZkFormal.NearV3.Candidates.ShaPartialLayout

namespace ZkFormal.NearV3.Candidates.ShaPartialTable
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Layout ZkFormal.Sha.Table.E
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

def expr (e : Expr) := ShaPartialLayout.expression (ShaCarryPairs.expression e)
def raw (bb bd : Nat) : Air.Table :=
  {width:=416,constraints:=(ShaCarryPairs.table bb bd).constraints.map ShaPartialLayout.expression,
   interactions:=(ShaCarryPairs.table bb bd).interactions.map (fun i =>
     {i with
       mult:=i.mult.map ShaPartialLayout.expression,
       msg:=i.msg.map ShaPartialLayout.expression}),maxLog:=22}
def inputStart (q : Nat) := 256+32*(q/4)+8*(3-q%4)
def outputStart (p : Nat) := colSt (p/4) (8*(3-p%4))

def interactions (bb bd : Nat) : List Interaction :=
  ((List.range 16).map fun q =>
    {bus:=bb,mult:=[expr (c (colF q))],
     msg:=[expr (c colId),expr (ZkFormal.Sha.Table.posE q),ShaPartialBytes.byteE (inputStart q)],send:=false}) ++
  [{bus:=bd,mult:=[expr (c colDmult)],
    msg:=[expr (c colId),expr (c colNd)] ++
      (List.range 32).map (fun p => ShaPartialBytes.byteE (outputStart p)),send:=true}]

def table (bb bd : Nat) : Air.Table := {raw bb bd with interactions:=interactions bb bd}

theorem input_syntax : ∀q:Fin 16,
    ShaCarryPairs.expression (ZkFormal.Sha.Table.byteE q.val)=
      bits (fun i => Expr.col i false) (inputStart q.val) 8 ∧
    inputStart q.val<384 ∧ inputStart q.val%8=0 := by decide +kernel

theorem output_syntax : ∀p:Fin 32,
    ShaCarryPairs.expression (ZkFormal.Sha.Table.digestByteE p.val)=
      bits (fun i => Expr.col i false) (outputStart p.val) 8 ∧
    outputStart p.val<384 ∧ outputStart p.val%8=0 := by decide +kernel

theorem byte_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) (start : Nat)
    (hs : start<384) (hm : start%8=0) :
    (ShaPartialLayout.expression (bits (fun i => Expr.col i false) start 8)).eval tr t r pub =
      (ShaPartialBytes.byteE start).eval tr t r pub := by
  have he : 8*(start/8)=start := by omega
  have hb : ∀q:Fin 48,(bits (fun i => Expr.col i false) (8*q.val) 8).colBound≤520 := by decide +kernel
  have hb' : (bits (fun i => Expr.col i false) start 8).colBound≤520 := by
    simpa only [he] using hb ⟨start/8,by omega⟩
  rw [ShaPartialLayout.expression_eq _ hb']
  simpa only [he,ShaPartialBytes.expr] using ShaPartialBytes.byte_eval tr t r pub ⟨start/8,by omega⟩

theorem input_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) (q : Fin 16) :
    (expr (ZkFormal.Sha.Table.byteE q.val)).eval tr t r pub =
      (ShaPartialBytes.byteE (inputStart q.val)).eval tr t r pub := by
  unfold expr
  rw [(input_syntax q).1]
  exact byte_eval tr t r pub _ (input_syntax q).2.1 (input_syntax q).2.2

theorem output_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) (p : Fin 32) :
    (expr (ZkFormal.Sha.Table.digestByteE p.val)).eval tr t r pub =
      (ShaPartialBytes.byteE (outputStart p.val)).eval tr t r pub := by
  unfold expr
  rw [(output_syntax p).1]
  exact byte_eval tr t r pub _ (output_syntax p).2.1 (output_syntax p).2.2

theorem shape : ZkFormal.Size.shapeOf 2 (table 0 1)=⟨416,9,7,9,22⟩ := by decide +kernel

theorem table_wf : (table 0 1).wf ⟨[table 0 1],2,0⟩ 8=true := by decide +kernel
end ZkFormal.NearV3.Candidates.ShaPartialTable
