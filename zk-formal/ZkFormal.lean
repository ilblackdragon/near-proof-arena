-- Design-phase proofs of concept (docs/zk-formal/DESIGN.md §10).
import ZkFormal.Potential
import ZkFormal.BadQuery
import ZkFormal.Product
import ZkFormal.Collision
import ZkFormal.Game
import ZkFormal.LineLemma
import ZkFormal.Params
import ZkFormal.Air.Basic
import ZkFormal.Air.Export
import ZkFormal.Stark.Field
import ZkFormal.Stark.Params
import ZkFormal.Stark.Iop
import ZkFormal.Stark.Bcs
import ZkFormal.Stark.Protocol
import ZkFormal.Stark.Verifier
import ZkFormal.Stark.Instance
import ZkFormal.Stark.Statements
import ZkFormal.Stark.Compose
import ZkFormal.Stark.Laws
import ZkFormal.Stark.ParseLemmas
import ZkFormal.Algebra.Transport
import ZkFormal.Algebra.NatPrime
import ZkFormal.Algebra.Fp
import ZkFormal.Algebra.QuadExt
import ZkFormal.Algebra.Fp8
import ZkFormal.Algebra.Poly
import ZkFormal.Algebra.RS
import ZkFormal.Algebra.Decode
import ZkFormal.Algebra.Statements
import ZkFormal.Algebra.PolyLemmas
import ZkFormal.Algebra.PolyRoots
import ZkFormal.Algebra.DecodeCount
import ZkFormal.Algebra.Compose
import ZkFormal.Algebra.RSProofs
import ZkFormal.Algebra.Main
-- Lane L4: AIR DSL and protocol/verifier model.
-- Lane L1 (algebra): BabyBear, its degree-8 extension, polynomials, RS codes.
import ZkFormal.Stark.NpBounds
import ZkFormal.Stark.QueryBound
-- Lane L5: SHA-256 block table (statements, composition, generator).
import ZkFormal.Sha.Compose
import ZkFormal.Near.Compose
-- Lane L6 sub-lane L6-sound: relational spec ⇒ NearRelation (good_sound).
import ZkFormal.Near.Spec.Sound
import ZkFormal.Near.BudgetCheck
