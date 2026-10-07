import ZkFormal.NearV3.Render.Ups.FieldInput

/-! Additional semantic facts about split nodes and upper-path source child ids. -/
namespace ZkFormal.NearV3.Render.UpsGen

structure WindowOk (I : UpsInst) (Q : UpsPartI) : Prop where
  /-- A split branch has two children precisely when both divergent suffixes survive. -/
  splitCount : Q.kind = 10 → nWin Q.shape = if I.ci = 6 ∨ I.ci = 9 ∨ I.ci = 10 then 2 else 1
  /-- Rewritten upper nodes read the id of the path child from the corresponding source
  digest window; this id is the source record of the preceding bottom-up part. -/
  childId : ∀ p, p < Q.q.length →
    (fieldAt Q.shape p).1 = 7 → (fieldAt Q.shape p).2.1 = 0 →
    TgtB I Q 7 (fieldAt Q.shape p).2.2.2 = true →
    (Q.kind = 0 ∨ Q.kind = 1 ∨ Q.kind = 11) →
    Q.pcid.getD (sposV I Q 7 0 (fieldAt Q.shape p).2.2.2 p).toNat 0 = Q.cN

end ZkFormal.NearV3.Render.UpsGen
