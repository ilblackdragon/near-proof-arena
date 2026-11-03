import StateM5a.StepsT2
import NearSpec.TrieUpsertProofs

/-!
# StateM5a.Walk — walk composition: a chain of row steps is the spec function on the witness trie

A walk's rows see one node each, its off-path children as hash stubs (`.hash h`, the 32 bytes the
row holds) and its on-path child as the next row's node (the `DOWN` / `UP` link: the child row
hashes to the stub's bytes).  The trie those rows *reveal* is a `PTrie` `t₁` whose path nodes are the
rows' nodes and whose other subtrees are stubs; `t₁.hashOf` is the root the first row hashes to
(`PTrie.hashOf (.hash h) = h`).  The chain relations below are the rows' step rules (one
constructor per row op, `Steps` / `StepsT2`):

* `FChain t key a` (INTAKE find: `oLF/oLA/oEF/oEA/oFD/oFA/oFV`) → `t.findRef key = some a`;
* `UChain t key v t'` (FINAL upsert: `oLR/oLX/oEU/oEX/oUD/oUN`) → `t.upsert key v = some t'`;
* `DChain t key r` (FINAL delete: `oLD/oLZ/oEZ/oES/oEB/oED/oDA/oDS/oDH/oDN`) → `t.del key = some r`.

**Witness trie.**  The spec runs on the witness trie `t₂` (`revealTrie`), which the rows' trie
refines (`t₁.refinedBy t₂`: same nodes on the path, stubs elsewhere whose bytes are the subtree
hashes).  Then `fchain_witness` / `uchain_witness` give the spec's answer on `t₂` (the value slot
up to `SlotRefines`) and an upsert result with the same root hash.  The refinement itself is where
collision resistance enters: two nodes with the same SHA-256 hash and well-formed serializations
are equal (`refinedBy_of_hash`, from the named hypotheses `Sha256CR` and `NodeSerInj`).
`Sha256CR` is the cryptographic assumption (never an axiom: a premise of the theorems that use
it); `NodeSerInj` (the node serialization is injective on well-formed nodes) is a statement about
the spec's encoder, stated here and proved in `StateM5a.SerInj` (`nodeSerInj`).  The lift to
the whole rows' trie and the delete refinement are in `StateM5a.Refine`.
-/

namespace StateM5a.Walk

open NearSpec NearSpecV3.D2 StateM5a.Steps

/-! ## Named hypotheses -/

/-- SHA-256 collision resistance, idealized: equal digests mean equal messages. -/
def Sha256CR : Prop := ∀ a b : Bytes, sha256 a = sha256 b → a = b

/-- SHA-384 collision resistance (the working-set tree, `Merkle.write_access_sound`'s `H`). -/
def Sha384CR (sha384 : Bytes → Bytes) : Prop := ∀ a b : Bytes, sha384 a = sha384 b → a = b

/-- The node preimage of `PTrie.hashOf` (`RawTrieNodeWithSize`) of a revealed node. -/
def ser : PTrie → Bytes
  | .hash _ => []
  | .leaf k v mem => [0] ++ u32 (hexPrefix k true).length ++ hexPrefix k true ++ v.valueRef ++ u64 mem
  | .ext k c mem => [3] ++ u32 (hexPrefix k false).length ++ hexPrefix k false ++ c.hashOf ++ u64 mem
  | .branch none cs mem => [1] ++ u16 (kidsBitmap cs 0) ++ Kids.hashes cs ++ u64 mem
  | .branch (some v) cs mem => [2] ++ v.valueRef ++ u16 (kidsBitmap cs 0) ++ Kids.hashes cs ++ u64 mem

theorem hashOf_ser (n : PTrie) (hn : ∀ h, n ≠ .hash h) : n.hashOf = sha256 (ser n) := by
  cases n with
  | hash h => exact absurd rfl (hn h)
  | leaf => rfl
  | ext => rfl
  | branch v cs m => cases v <;> rfl

/-- A row's node: its children are hash stubs and its value slot is a `ValueRef` (the row holds
`(len, sha256 value)`, never the value bytes). -/
def Shallow : PTrie → Prop
  | .hash _ => True
  | .leaf _ s _ => ∃ len h, s = .ref len h
  | .ext _ c _ => ∃ h, c = .hash h
  | .branch v cs _ => (∀ s, v = some s → ∃ len h, s = .ref len h) ∧
      ∀ n c, Kids.at cs n = some c → ∃ h, c = .hash h

/-- Node serialization injectivity on well-formed revealed nodes, up to refinement of the
children and value slots (`refinedBy` one level deep): the statement lane B needs from the spec's
encoder.  Proved: `SerInj.nodeSerInj`. -/
def NodeSerInj : Prop :=
  ∀ n₁ n₂ : PTrie, n₁.wf = true → n₂.wf = true → (∀ h, n₁ ≠ .hash h) → (∀ h, n₂ ≠ .hash h) →
    Shallow n₁ → ser n₁ = ser n₂ → n₁.refinedBy n₂

/-! ## Kids refinement, slot by slot -/

theorem kids_at_refinedBy : ∀ (cs₁ cs₂ : Kids) (n : Nat), Kids.refinedBy cs₁ cs₂ →
    (Kids.at cs₁ n = none → Kids.at cs₂ n = none) ∧
    (∀ c₁, Kids.at cs₁ n = some c₁ → ∃ c₂, Kids.at cs₂ n = some c₂ ∧ c₁.refinedBy c₂)
  | .nil, cs₂, n, hr => by
    cases cs₂ <;> simp [Kids.refinedBy] at hr
    cases n <;> simp [Kids.at]
  | .none r, cs₂, 0, hr => by
    cases cs₂ <;> simp [Kids.refinedBy] at hr
    simp [Kids.at]
  | .some c r, cs₂, 0, hr => by
    cases cs₂ with
    | some c₂ r₂ =>
      simp only [Kids.refinedBy] at hr
      simp only [Kids.at, reduceCtorEq, false_implies, Option.some.injEq, true_and]
      intro c₁ h; subst h; exact ⟨c₂, rfl, hr.1⟩
    | _ => simp [Kids.refinedBy] at hr
  | .none r, cs₂, n + 1, hr => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    all_goals first | contradiction | (simp only [Kids.at]; exact kids_at_refinedBy r _ n hr)
  | .some c r, cs₂, n + 1, hr => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    all_goals first | contradiction | (simp only [Kids.at]; exact kids_at_refinedBy r _ n hr.2)

/-! ## Find chains (INTAKE) -/

/-- The rows of one find walk, as the trie they reveal. -/
inductive FChain : PTrie → List Nat → Option Slot → Prop
  /-- `SN.oLF` -/
  | leafHit (k : List Nat) (s : Slot) (m : Nat) : FChain (.leaf k s m) k (some s)
  /-- `SN.oLA` (mismatch witness at `jm`) -/
  | leafMiss (k key : List Nat) (s : Slot) (m jm : Nat) (h : k[jm]? ≠ key[jm]?) :
      FChain (.leaf k s m) key none
  /-- `SN.oEF` -/
  | extDesc (k rest : List Nat) (c : PTrie) (m : Nat) (a : Option Slot) (hc : FChain c rest a) :
      FChain (.ext k c m) (k ++ rest) a
  /-- `SN.oEA` -/
  | extMiss (k key : List Nat) (c : PTrie) (m jm : Nat) (hj : jm < k.length) (h : k[jm]? ≠ key[jm]?) :
      FChain (.ext k c m) key none
  /-- `BR.oFD` -/
  | brDesc (v : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat) (c : PTrie) (a : Option Slot)
      (hat : Kids.at cs n = some c) (hc : FChain c rest a) : FChain (.branch v cs m) (n :: rest) a
  /-- `BR.oFA` -/
  | brEmpty (v : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat) (hat : Kids.at cs n = none) :
      FChain (.branch v cs m) (n :: rest) none
  /-- `BR.oFV` -/
  | brVal (v : Option Slot) (cs : Kids) (m : Nat) : FChain (.branch v cs m) [] v

theorem fchain_sound {t : PTrie} {key : List Nat} {a : Option Slot} (h : FChain t key a) :
    t.findRef key = some a := by
  induction h with
  | leafHit k s m => exact leaf_findRef k s m
  | leafMiss k key s m jm h => exact leaf_findRef_absent k key s m (ne_of_mismatch k key jm h)
  | extDesc k rest c m a _ ih => rw [ext_findRef]; exact ih
  | extMiss k key c m jm hj h => exact ext_findRef_absent k key c m (not_isPrefix_of_mismatch k key jm hj h)
  | brDesc v cs m n rest c a hat _ ih => rw [br_findRef, hat]; exact ih
  | brEmpty v cs m n rest hat => rw [br_findRef, hat]
  | brVal v cs m => exact br_findValue v cs m

/-- **Find walk on the witness trie.**  The rows' answer is the spec's `findRef` on any trie the
rows' trie refines, up to the value slot's refinement (a revealed value against its `ValueRef`). -/
theorem fchain_witness {t₁ : PTrie} {key : List Nat} {a : Option Slot} (h : FChain t₁ key a) :
    ∀ t₂, t₁.refinedBy t₂ → ∃ a₂, t₂.findRef key = some a₂ ∧ OptSlotRefines a a₂ := by
  induction h with
  | leafHit k s m =>
    intro t₂ hr
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    exact ⟨_, leaf_findRef _ _ _, hs⟩
  | leafMiss k key s m jm h =>
    intro t₂ hr
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, -⟩ := hr
    exact ⟨none, leaf_findRef_absent _ _ _ _ (ne_of_mismatch k key jm h), trivial⟩
  | extDesc k rest c m a _ ih =>
    intro t₂ hr
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hc⟩ := hr
    obtain ⟨a₂, h₂, ha⟩ := ih _ hc
    exact ⟨a₂, by rw [ext_findRef]; exact h₂, ha⟩
  | extMiss k key c m jm hj h =>
    intro t₂ hr
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, -⟩ := hr
    exact ⟨none, ext_findRef_absent _ _ _ _ (not_isPrefix_of_mismatch k key jm hj h), trivial⟩
  | brDesc v cs m n rest c a hat _ ih =>
    intro t₂ hr
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    rename_i v₂ cs₂ m₂
    obtain ⟨-, -, hcs⟩ := hr
    obtain ⟨c₂, hat₂, hc⟩ := (kids_at_refinedBy cs cs₂ n hcs).2 c hat
    obtain ⟨a₂, h₂, ha⟩ := ih _ hc
    exact ⟨a₂, by rw [br_findRef, hat₂]; exact h₂, ha⟩
  | brEmpty v cs m n rest hat =>
    intro t₂ hr
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    rename_i v₂ cs₂ m₂
    obtain ⟨-, -, hcs⟩ := hr
    exact ⟨none, by rw [br_findRef, (kids_at_refinedBy cs cs₂ n hcs).1 hat], trivial⟩
  | brVal v cs m =>
    intro t₂ hr
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    rename_i v₂ cs₂ m₂
    obtain ⟨-, hv, -⟩ := hr
    exact ⟨v₂, br_findValue _ _ _, hv⟩

/-! ## Upsert chains (FINAL, present final value) -/

inductive UChain : PTrie → List Nat → Bytes → PTrie → Prop
  /-- `SN.oLR` -/
  | leafRep (k : List Nat) (s : Slot) (m : Nat) (v : Bytes) : UChain (.leaf k s m) k v (newLeaf k v)
  /-- `SN.oLX` + `BR.oSL` + `SN.oLM` ×2 + `SN.oEP` -/
  | leafSplit (p xs ys : List Nat) (x y : Nat) (hxy : x ≠ y) (s : Slot) (m : Nat) (v : Bytes) :
      UChain (.leaf (p ++ x :: xs) s m) (p ++ y :: ys) v
        (wrapExt p (.branch none (kids2 x (.leaf xs s (leafMem xs s.len)) y (newLeaf ys v))
          (50 + leafMem xs s.len + leafMem ys v.length)))
  /-- `SN.oEU` -/
  | extDesc (k rest : List Nat) (c c' : PTrie) (m cm : Nat) (v : Bytes) (hm : c.mem? = some cm)
      (hc : UChain c rest v c') : UChain (.ext k c m) (k ++ rest) v (.ext k c' (m + c'.memD - cm))
  /-- `BR.oUD` -/
  | brDesc (bv : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat) (c c' : PTrie) (cm : Nat)
      (v : Bytes) (hat : Kids.at cs n = some c) (hm : c.mem? = some cm) (hc : UChain c rest v c') :
      UChain (.branch bv cs m) (n :: rest) v (.branch bv (Kids.put cs n (some c')) (m + c'.memD - cm))
  /-- `BR.oUN` (+ `SN.oLM`) -/
  | brNew (bv : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat) (v : Bytes)
      (hat : Kids.at cs n = none) (hn : n < kidsLen cs) :
      UChain (.branch bv cs m) (n :: rest) v
        (.branch bv (Kids.put cs n (some (newLeaf rest v))) (m + leafMem rest v.length - 0))

theorem uchain_sound {t : PTrie} {key : List Nat} {v : Bytes} {t' : PTrie} (h : UChain t key v t') :
    t.upsert key v = some t' := by
  induction h with
  | leafRep k s m v => exact leaf_upsert k s m v
  | leafSplit p xs ys x y hxy s m v => exact leaf_split p xs ys x y hxy s m v
  | extDesc k rest c c' m cm v hm _ ih => exact ext_upsert k c c' m cm rest v hm ih
  | brDesc bv cs m n rest c c' cm v hat hm _ ih => exact br_upsert_descend bv cs m n rest v c c' cm hat hm ih
  | brNew bv cs m n rest v hat hn => exact br_upsert_new bv cs m n rest v hat hn

/-- **Upsert walk on the witness trie.**  On any trie the rows' trie refines, the spec's upsert
succeeds and its result has the root hash the rows compute (`PTrie.upsert_refinedBy`,
`hashOf_refinedBy`). -/
theorem uchain_witness {t₁ t₁' : PTrie} {key : List Nat} {v : Bytes} (h : UChain t₁ key v t₁')
    (t₂ : PTrie) (hr : t₁.refinedBy t₂) :
    ∃ t₂', t₂.upsert key v = some t₂' ∧ t₂'.hashOf = t₁'.hashOf := by
  obtain ⟨t₂', hu, hr'⟩ := PTrie.upsert_refinedBy t₁ t₂ key v t₁' hr (uchain_sound h)
  exact ⟨t₂', hu, (PTrie.hashOf_refinedBy _ _ hr').symm⟩

/-! ## Delete chains (FINAL, absent final value) -/

inductive DChain : PTrie → List Nat → Bool × Option PTrie → Prop
  /-- `SN.oLD` -/
  | leafDel (k : List Nat) (s : Slot) (m : Nat) : DChain (.leaf k s m) k (true, none)
  /-- `SN.oLZ` -/
  | leafAbs (k key : List Nat) (s : Slot) (m jm : Nat) (h : k[jm]? ≠ key[jm]?) :
      DChain (.leaf k s m) key (false, some (.leaf k s m))
  /-- `SN.oEZ` -/
  | extAbs (k key : List Nat) (c : PTrie) (m jm : Nat) (hj : jm < k.length) (h : k[jm]? ≠ key[jm]?) :
      DChain (.ext k c m) key (false, some (.ext k c m))
  /-- `SN.oES` -/
  | extSame (k rest : List Nat) (c : PTrie) (m cm : Nat) (c'' : Option PTrie) (hm : c.mem? = some cm)
      (hc : DChain c rest (false, c'')) : DChain (.ext k c m) (k ++ rest) (false, some (.ext k c m))
  /-- `SN.oED` -/
  | extLeaf (k rest k2 : List Nat) (c : PTrie) (m cm m2 : Nat) (s : Slot) (hm : c.mem? = some cm)
      (hc : DChain c rest (true, some (.leaf k2 s m2))) :
      DChain (.ext k c m) (k ++ rest) (true, some (.leaf (k ++ k2) s (leafMem (k ++ k2) s.len)))
  /-- `SN.oEB` -/
  | extBranch (k rest : List Nat) (c : PTrie) (m cm : Nat) (bv : Option Slot) (cs : Kids) (m' : Nat)
      (hm : c.mem? = some cm) (hc : DChain c rest (true, some (.branch bv cs m'))) :
      DChain (.ext k c m) (k ++ rest) (true, some (.ext k (.branch bv cs m') (extOwnMem k + m')))
  /-- `BR.oDA` -/
  | brAbs (v : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat) (hat : Kids.at cs n = none) :
      DChain (.branch v cs m) (n :: rest) (false, some (.branch v cs m))
  /-- `BR.oDS` -/
  | brSame (v : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat) (c : PTrie) (cm : Nat)
      (c'' : Option PTrie) (hat : Kids.at cs n = some c) (hm : c.mem? = some cm)
      (hc : DChain c rest (false, c'')) : DChain (.branch v cs m) (n :: rest) (false, some (.branch v cs m))
  /-- `BR.oDH` / `oDL` / `oDN` (the kept branch, `squashBranch_keep`) -/
  | brKeep (v : Option Slot) (cs : Kids) (m n : Nat) (rest : List Nat) (c : PTrie) (c' : Option PTrie)
      (cm : Nat) (hat : Kids.at cs n = some c) (hm : c.mem? = some cm) (hc : DChain c rest (true, c'))
      (h0 : Kids.present (Kids.put cs n c') 0 ≠ [])
      (h1 : v = none → (Kids.present (Kids.put cs n c') 0).length ≠ 1) :
      DChain (.branch v cs m) (n :: rest) (true, some (.branch v (Kids.put cs n c') (m - cm + delMem c')))
  /-- `BR.oD1` (+ `SN.oLS`) -/
  | brOne (cs : Kids) (m n i : Nat) (rest k2 : List Nat) (c : PTrie) (cm : Nat) (s : Slot) (m2 : Nat)
      (hat : Kids.at cs n = some c) (hm : c.mem? = some cm) (hc : DChain c rest (true, none))
      (hp : Kids.present (Kids.put cs n none) 0 = [(i, .leaf k2 s m2)]) :
      DChain (.branch none cs m) (n :: rest) (true, some (.leaf ([i] ++ k2) s (leafMem ([i] ++ k2) s.len)))

theorem dchain_sound {t : PTrie} {key : List Nat} {r : Bool × Option PTrie} (h : DChain t key r) :
    t.del key = some r := by
  induction h with
  | leafDel k s m => exact leaf_del k s m
  | leafAbs k key s m jm h => exact leaf_del_absent k key s m (ne_of_mismatch k key jm h)
  | extAbs k key c m jm hj h => exact ext_del_absent k key c m (not_isPrefix_of_mismatch k key jm hj h)
  | extSame k rest c m cm c'' hm _ ih => exact ext_del_same k c m cm rest c'' hm ih
  | extLeaf k rest k2 c m cm m2 s hm _ ih => exact ext_del_leaf k c m cm rest k2 s m2 hm ih
  | extBranch k rest c m cm bv cs m' hm _ ih => exact ext_del_branch k c m cm rest bv cs m' hm ih
  | brAbs v cs m n rest hat => exact br_del_absent v cs m n rest hat
  | brSame v cs m n rest c cm c'' hat hm _ ih => exact br_del_same v cs m n rest c cm c'' hat hm ih
  | brKeep v cs m n rest c c' cm hat hm _ h0 h1 ih => exact br_del_keep v cs m n rest c c' cm hat hm ih h0 h1
  | brOne cs m n i rest k2 c cm s m2 hat hm _ hp ih => exact br_del_one cs m n i rest k2 c cm s m2 hat hm ih hp

/-! ## One committed change (`applyChange`) -/

theorem change_upsert {t t' : PTrie} {k x : Bytes} (h : UChain t (nibbles k) x t') :
    applyChange (some t) k (some x) = some (some t') := applyChange_upsert t k x t' (uchain_sound h)

theorem change_del {t t' : PTrie} {k : Bytes} {b : Bool} (h : DChain t (nibbles k) (b, some t')) :
    applyChange (some t) k none = some (some t') := by
  simp [applyChange, dchain_sound h]

/-! ## Where collision resistance enters -/

/-- A stub whose bytes are a revealed node's hash is refined by that node. -/
theorem stub_refinedBy (t : PTrie) : (PTrie.hash t.hashOf).refinedBy t := by
  simp [PTrie.refinedBy]

/-- **Row node = witness node.**  A row's revealed node `n₁` (children stubs) and the witness
trie's node `n₂` at the same position hash to the same digest (the `DOWN` link); under
`Sha256CR` their serializations are equal, and under `NodeSerInj` the row node refines the witness
node. -/
theorem refinedBy_of_hash (hCR : Sha256CR) (hInj : NodeSerInj) {n₁ n₂ : PTrie}
    (hw₁ : n₁.wf = true) (hw₂ : n₂.wf = true) (h₁ : ∀ h, n₁ ≠ .hash h) (h₂ : ∀ h, n₂ ≠ .hash h)
    (hs : Shallow n₁) (hh : n₁.hashOf = n₂.hashOf) : n₁.refinedBy n₂ :=
  hInj n₁ n₂ hw₁ hw₂ h₁ h₂ hs (hCR _ _ (by rw [← hashOf_ser n₁ h₁, ← hashOf_ser n₂ h₂]; exact hh))

end StateM5a.Walk
