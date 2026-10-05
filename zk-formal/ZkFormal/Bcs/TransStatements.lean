import ZkFormal.Bcs.TransDefs

/-!
# ZkFormal.Bcs.TransStatements — sublemmas of the RBR transport (frozen)
-/

namespace ZkFormal.Bcs.Transport

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

/-- An undecodable transcript stays undecodable. -/
def DecNoneStmt : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]
    (V : Stark.IopSpec F K) (τ : PT mmcs) (e : Entry mmcs),
    decodePT (F := F) V τ = none → decodePT (F := F) V (τ.push e) = none

/-- A decodable message push extends the decoding by a prover message at a prover slot. -/
def DecMsgStmt : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]
    (V : Stark.IopSpec F K), Adapter.SchedOk V →
    ∀ (τ : PT mmcs) roots raw os σ', decodePT (F := F) V (τ.push (.msg roots raw os)) = some σ' →
      ∃ σ m, decodePT (F := F) V τ = some σ ∧ V.NextIsProver σ ∧ σ' = σ.push m

/-- A decodable challenge push extends the decoding by the decoded challenge at a challenge
slot, whose kind (`ood`) depends only on the prefix. -/
def DecChalStmt : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]
    (V : Stark.IopSpec F K), Adapter.SchedOk V →
    ∀ (τ : PT mmcs) σ, decodePT (F := F) V τ = some σ →
      ∃ ood, ∀ y σ', decodePT (F := F) V (τ.push (.chal y)) = some σ' →
        V.NextIsChal σ ∧ σ' = σ.pushChal (decChal (F := F) ood y)

/-- A complete view the verifier decodes comes from a decodable, complete, shaped transcript
whose true openings are what the verifier reads. -/
def DecQueryStmt : Prop :=
  ∀ (F K : Type) [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]
    (V : Stark.IopSpec F K), Adapter.SchedOk V →
    ∀ (τ : PT mmcs) hdr σu, Adapter.decodeView (F := F) V τ.view = some (hdr, σu) →
      ∃ σ, decodePT (F := F) V τ = some σ ∧ σ.erase = σu ∧ V.AtQuery σ ∧ Udr.Shaped V σ ∧
        V.domSize σ = 2 ^ V.queryLog hdr ∧
        ∀ x vals, Forall2 (fun q v => τ.oracle q.1 q.2.1 q.2.2 = some v) (Adapter.opensA V τ.view x) vals →
          Adapter.rowsAll (F := F) (Stark.schedOracles (V.schedule hdr)) vals = V.trueOpenings σ x

/-- Query positions of one oracle answer are close to independent uniform draws. -/
def PosCountStmt : Prop :=
  ∀ (p bits n0 : Nat) (A : Nat → Prop) (a : Nat), p * bits ≤ 256 → n0 ≤ bits →
    count (List.range (2 ^ n0)) A ≤ a →
    count (List.range roRange) (fun v =>
      ∀ x ∈ (List.range p).map (fun i => (Bytes.beToNat (LazyRO.answer v) >>> (bits * i)) % 2 ^ n0), A x)
      ≤ a ^ p * 2 ^ (256 - p * n0)

end ZkFormal.Bcs.Transport
