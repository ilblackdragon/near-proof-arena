import ZkFormal.NearV3.Assembly.RcptCandidateRepairedTable
import ZkFormal.Size.Model
namespace ZkFormal.NearV3.Candidates.ReceiptRepairedProfile
open ZkFormal.Air ZkFormal.NearV3.Assembly
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem shape : ZkFormal.Size.shapeOf 2 ReceiptCandidateRouting.candidateTable=
    ⟨263,9,5,9,22⟩ := by decide +kernel

theorem same_shape : ZkFormal.Size.shapeOf 2 ReceiptCandidateRouting.candidateTable=
    ZkFormal.Size.shapeOf 2 RcptV3.table := by decide +kernel

theorem degree : ReceiptCandidateRouting.candidateTable.degree 2=6 := by decide +kernel

theorem columns : ReceiptCandidateRouting.candidateTable.exprs.all
    (fun e=>decide (e.colBound≤ReceiptCandidateRouting.candidateTable.width))=true := by decide +kernel

/-- Replacing the receipt table preserves the complete static shape list used
by proof-size accounting. This does not install the candidate or assert soundness. -/
theorem family_shapes (before after : List ZkFormal.Air.Table) :
    ((before++[ReceiptCandidateRouting.candidateTable]++after).map (ZkFormal.Size.shapeOf 2))=
      ((before++[RcptV3.table]++after).map (ZkFormal.Size.shapeOf 2)) := by
  simp only [List.map_append,List.map_cons,List.map_nil,same_shape]

end ZkFormal.NearV3.Candidates.ReceiptRepairedProfile
