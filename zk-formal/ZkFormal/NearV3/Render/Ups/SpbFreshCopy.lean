import ZkFormal.NearV3.Render.Ups.CopyFields

namespace ZkFormal.NearV3.Render.UpsGen

theorem spb_fresh_copy (I : UpsInst) (Q : UpsPartI) (hk : Q.kind=10)
    (hi : I.ci=5 ∨ I.ci=6 ∨ I.ci=7 ∨ I.ci=9) : CopyFields I Q := by
  constructor
  intro pre post st width he hc
  rcases hi with hi|hi|hi|hi <;>
    simp [CpB,VcpB,WfrB,XcpB,hk,hi] at hc

end ZkFormal.NearV3.Render.UpsGen
