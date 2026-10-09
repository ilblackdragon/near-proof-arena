import ZkFormal.NearV3.Rcpt.Candidates.Walk22Render
import ZkFormal.NearV3.Render.WalkGen

namespace ZkFormal.NearV3.Candidates.Walk22Render
open ZkFormal.Near

/-- Only the completeness height budget changes; generated cells are identical. -/
theorem cell_original (ws : List WalkR) (height row col : Nat) :
    WalkGen.cell ws height row col=Render.WalkGen.cell ws height row col := rfl

theorem rows_original (ws : List WalkR) : rows ws=Render.rows ws := rfl

theorem recs_original (ws : List WalkR) : WalkGen.recs ws=Render.WalkGen.recs ws := rfl

theorem old_ok (ws : List WalkR) (h : Render.WalkOk ws) : WalkOk ws := by
  refine ⟨h.wf,h.pos,?_⟩
  have hh:=h.cap
  change rows ws≤2097152 at hh
  change rows ws≤4194304
  omega

end ZkFormal.NearV3.Candidates.Walk22Render
