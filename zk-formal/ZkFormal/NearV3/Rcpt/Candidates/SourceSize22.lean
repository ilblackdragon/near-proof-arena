import ZkFormal.NearV3.Rcpt.Candidates.SourceSize

/-! Alternative isolated model respecting the active protocol's hard maxLog22.
Two log23 partitions are not admitted by V2.AirP.wf: it reuses Air.Table.wf. -/
namespace ZkFormal.NearV3.Rcpt.Candidates
open ZkFormal.Size ZkFormal.Size.V3 ZkFormal.Stark

def partition22Shapes (g : Nat) : List TShape :=
  let sha := { shapeOf g shaT with maxLog := 22 }
  let src := { (rcptS g)[4]! with maxLog := 22 }
  [sha, sha, sha, sha] ++ trieS g ++ chachaT.map (shapeOf g) ++ schedS g ++
    (rcptS g).set 4 src ++ [src, src, src] ++ v1S g

def partition22Size (g : Nat) : Nat :=
  sizeOfWeq (ZkFormal.V2.G.pg g) (partition22Shapes g)

/-- The current protocol rejects any source/SHA partition with maxLog23, regardless
of increasing a separate Stark Params.maxLogLde model input. -/
theorem log23_not_wf (A : ZkFormal.Air.Air) (degree : Nat) (T : ZkFormal.Air.Table)
    (h : T.maxLog = 23) : T.wf A degree = false := by
  simp [ZkFormal.Air.Table.wf, h]

end ZkFormal.NearV3.Rcpt.Candidates
