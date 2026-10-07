import ZkFormal.NearV3.Render.Ups.Gen

/-! Explicit arithmetic and serialization obligations for honest memory rows.
These must be derived from the actual trie update; they do not assert AIR equations. -/
namespace ZkFormal.NearV3.Render.UpsGen

structure MemOk (I : UpsInst) (Q : UpsPartI) : Prop where
  /-- Each computed carry fits the 17-bit signed /16-bit unsigned encoding. -/
  carries : ∀ i, i < 8 → 0 ≤ cbV I Q i ∧ cbV I Q i < 131072 ∧
    0 ≤ co2V I Q i ∧ co2V I Q i < 65536
  /-- The serialized MEM field contains the little-endian result bytes. -/
  bytes : ∀ p, p < Q.q.length → (fieldAt Q.shape p).1 = 8 →
    (Q.q.getD p 0 : Int) = RV I Q / 256 ^ (fieldAt Q.shape p).2.1 % 256

end ZkFormal.NearV3.Render.UpsGen
