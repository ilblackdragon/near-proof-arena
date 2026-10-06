import ZkFormal.V2.Air

/-!
# `KindReg`: the SHA kind registry (shared, discharged at assembly)

SHA message ids are `kind + 16·x` with `kind < 16` (design §12 registry: 1–10 v1, 11 SCH,
12 VUPS, 13 SRC, 14 VAK). `KindReg AP pub tr val bytes kinds pubKinds` (with `val` the field-to-`Nat` map) says that every message a table
`t` sends on the `BYTES` bus has an id whose kind is in `kinds t`, and every public `BYTES` message
has its kind in `pubKinds`.

At assembly it is **proved** table by table from each table's view, and for the public segments
from the prepared-statement encoding. It is never assumed. Lanes state their "no one else sends my
kind" facts as consequences:
* `KindReg.avoid`: a kind `k` registered only to table `tc` is never the kind of a `BYTES` send
  by another table, nor of a public `BYTES` message. The scheduler's `ShaKind` is an instance,
  and so is the trie lane's `othersId` (`a % 16 ∉ {K_NPRE, K_NPOST, K_VPRE}`).
-/

namespace ZkFormal.V2

open ZkFormal.Air

section
variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F] [PubVal F]

/-- **The kind registry** for the `BYTES` bus `bytes`. -/
structure KindReg (AP : AirP) (pub : List F) (tr : Trace F) (val : F → Nat) (bytes : Nat)
    (kinds : Nat → List Nat) (pubKinds : List Nat) : Prop where
  tabs : ∀ t, t < AP.tables.length → ∀ r, r < tr.height t → ∀ i ∈ AP.tables[t]!.interactions,
    i.bus = bytes → i.send = true → i.multNat tr t r pub ≠ 0 →
    ∀ a, (i.msgVal tr t r pub).head? = some a → val a % 16 ∈ kinds t
  pubs : ∀ M, pubCount AP pub bytes true M ≠ 0 → ∀ a, M.head? = some a → val a % 16 ∈ pubKinds

/-- **A kind owned by one table** is not used by any other sender. -/
theorem KindReg.avoid {AP : AirP} {pub : List F} {tr : Trace F} {val : F → Nat} {bytes : Nat}
    {kinds : Nat → List Nat} {pubKinds : List Nat} (R : KindReg AP pub tr val bytes kinds pubKinds)
    {tc k : Nat} (hown : ∀ t, t ≠ tc → k ∉ kinds t) (hpub : k ∉ pubKinds) :
    (∀ t, t < AP.tables.length → t ≠ tc → ∀ r, r < tr.height t → ∀ i ∈ AP.tables[t]!.interactions,
      i.bus = bytes → i.send = true → i.multNat tr t r pub ≠ 0 →
      ∀ a, (i.msgVal tr t r pub).head? = some a → val a % 16 ≠ k) ∧
    (∀ M, pubCount AP pub bytes true M ≠ 0 → ∀ a, M.head? = some a → val a % 16 ≠ k) := by
  refine ⟨fun t ht hne r hr i hi hb hs hm a ha e => ?_, fun M hM a ha e => ?_⟩
  · exact hown t hne (e ▸ R.tabs t ht r hr i hi hb hs hm a ha)
  · exact hpub (e ▸ R.pubs M hM a ha)

end

end ZkFormal.V2
