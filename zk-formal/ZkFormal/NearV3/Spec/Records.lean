import ZkFormal.NearV3.Spec.StoreBuild

/-!
# ZkFormal.NearV3.Spec.Records — v3 trie records, hash-indexed stores (`StoreBuildStmt`)

The relational model of a v3 partial trie (V3-D0-DESIGN §3.2–3.3, §6.2):

* `NodeRec3` — a revealed node of instance `τ` (main transition `τ = 0`, then
  the implicit transitions).  Children are `Kid3.node c` (a revealed record, by
  id; records may be *shared*, so the records form a DAG), `Kid3.hash h`
  (unrevealed) or `Kid3.none`; a value slot is an unrevealed `ValueRef` or
  `VSlot3.val vid`, a revealed value record of variable length.
* `ValRec3` — a revealed value (`τ`, bytes); values are records of their own so
  that equal values in different slots are one store entry.
* `fullTree ns vs n` — the partial trie of record `n` (the DAG unfolded);
* `storeOf ns vs τ` — the witness store (`base_state` entries) of instance `τ`:
  the preimage of every `τ` node record, then every `τ` value;
* `HashFunctional l` — entries with equal SHA-256 digests are equal
  (`hashFunctional_of_nodup`: pairwise-distinct digests suffice);
* `RootedDag ns vs τ root` — the root is a `τ` record, and children / values of
  `τ` records are `τ` records with **larger ids** (`cid > n`: id-order
  acyclicity);
* `PathsRevealed` — every read key's lookup is determined within `trieFuel`.

`storeBuild` (**`StoreBuildStmt`**): under these, NearSpecV3's
`partialTrie (storeOf ns vs τ) (digest root) keys` refines `fullTree ns vs root`,
has root hash `digest root`, and answers `find` on every read key exactly as
`fullTree ns vs root`.
-/

namespace ZkFormal.NearV3

open NearSpec NearSpecV3

/-- Value slot of a v3 record. -/
inductive VSlot3 where
  /-- unrevealed value: `ValueRef { length, hash }` -/
  | ref (len : Nat) (h : Bytes)
  /-- revealed value: value record `vid` -/
  | val (vid : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Child slot. -/
inductive Kid3 where
  | none
  | hash (h : Bytes)
  | node (cid : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- The node part of a record (v1 `NodeRec` with value records). -/
inductive Rec3 where
  | leaf (key : List Nat) (v : VSlot3) (mem : Nat)
  | ext (key : List Nat) (kid : Kid3) (mem : Nat)
  | branch (v : Option VSlot3) (kids : List Kid3) (mem : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- A revealed node of instance `tau`. -/
structure NodeRec3 where
  tau : Nat
  node : Rec3
  deriving Repr, DecidableEq, Inhabited

/-- A revealed value of instance `tau`. -/
structure ValRec3 where
  tau : Nat
  bytes : Bytes
  deriving Repr, DecidableEq, Inhabited

/-! ## Unfolding -/

def Rec3.kids : Rec3 → List Kid3
  | .leaf .. => []
  | .ext _ kid _ => [kid]
  | .branch _ kids _ => kids

/-- Value records referenced by a record. -/
def Rec3.vids : Rec3 → List Nat
  | .leaf _ (.val i) _ => [i]
  | .branch (some (.val i)) _ _ => [i]
  | _ => []

def valOf (vs : List ValRec3) (i : Nat) : Bytes := (vs[i]?.map ValRec3.bytes).getD []

def slot3 (vs : List ValRec3) : VSlot3 → Slot
  | .ref len h => .ref len h
  | .val i => .val (valOf vs i)

def kidTree3 (g : Nat → PTrie) : Kid3 → PTrie
  | .none => .hash []
  | .hash h => .hash h
  | .node c => g c

def kidsOf3 (g : Nat → PTrie) : List Kid3 → Kids
  | [] => .nil
  | .none :: r => .none (kidsOf3 g r)
  | .hash h :: r => .some (.hash h) (kidsOf3 g r)
  | .node c :: r => .some (g c) (kidsOf3 g r)

/-- One record, children built by `g`. -/
def nodeTree3 (vs : List ValRec3) (g : Nat → PTrie) : Rec3 → PTrie
  | .leaf k v mem => .leaf k (slot3 vs v) mem
  | .ext k kid mem => .ext k (kidTree3 g kid) mem
  | .branch v kids mem => .branch (v.map (slot3 vs)) (kidsOf3 g kids) mem

/-- The partial trie of record `n` with fuel `f`. -/
def treeOf3 (ns : List NodeRec3) (vs : List ValRec3) : Nat → Nat → PTrie
  | 0, _ => .hash []
  | f + 1, n =>
    match ns[n]? with
    | none => .hash []
    | some nr => nodeTree3 vs (treeOf3 ns vs f) nr.node

/-- The partial trie of record `n` (fuel `ns.length` suffices under `RootedDag`). -/
def fullTree (ns : List NodeRec3) (vs : List ValRec3) (n : Nat) : PTrie := treeOf3 ns vs ns.length n

/-- Digest of record `n`. -/
def digest (ns : List NodeRec3) (vs : List ValRec3) (n : Nat) : Bytes := (fullTree ns vs n).hashOf

/-! ## The store -/

/-- Record `n` belongs to instance `τ`. -/
def InInst (ns : List NodeRec3) (τ n : Nat) : Prop := ∃ nr, ns[n]? = some nr ∧ nr.tau = τ

/-- Node entries of instance `τ`: the preimage of every `τ` record, id order. -/
def nodeEntries (ns : List NodeRec3) (vs : List ValRec3) (τ : Nat) : List Bytes :=
  (List.range ns.length).filterMap fun n =>
    match ns[n]? with
    | some nr => if nr.tau = τ then some (nodeEnc (fullTree ns vs n)) else none
    | none => none

/-- Value entries of instance `τ`. -/
def valEntries (vs : List ValRec3) (τ : Nat) : List Bytes :=
  (vs.filter fun v => v.tau == τ).map ValRec3.bytes

/-- **The witness store of instance `τ`** (`base_state` values). -/
def storeOf (ns : List NodeRec3) (vs : List ValRec3) (τ : Nat) : List Bytes :=
  nodeEntries ns vs τ ++ valEntries vs τ

/-- Revealed bytes of instance `τ` (what `w.size` counts for its store). -/
def storeBytes (ns : List NodeRec3) (vs : List ValRec3) (τ : Nat) : Nat :=
  ((storeOf ns vs τ).map List.length).sum

/-- Entries with equal digests are equal. -/
def HashFunctional (l : List Bytes) : Prop :=
  ∀ a ∈ l, ∀ b ∈ l, sha256 a = sha256 b → a = b

/-- Pairwise-distinct digests (what the `uniq` table proves). -/
def DigestsDistinct (l : List Bytes) : Prop := (l.map sha256).Nodup

theorem hashFunctional_of_nodup {l : List Bytes} (h : DigestsDistinct l) : HashFunctional l := by
  induction l with
  | nil => intro a ha; simp at ha
  | cons x xs ih =>
    simp only [DigestsDistinct, List.map_cons, List.nodup_cons, List.mem_map] at h
    obtain ⟨hx, hxs⟩ := h
    intro a ha b hb he
    simp only [List.mem_cons] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · rfl
    · exact absurd ⟨b, hb, he.symm⟩ hx
    · exact absurd ⟨a, ha, he⟩ hx
    · exact ih hxs a ha b hb he

/-- In a hash-functional store, every entry is what `storeGet` returns for its digest. -/
theorem found_of_mem {l : List Bytes} (hf : HashFunctional l) {b : Bytes} (hb : b ∈ l) :
    Found (mkStore l) b := by
  unfold Found storeGet mkStore
  have hex : ∃ p ∈ l.map (fun v => (sha256 v, v)), (p.1 == sha256 b) = true :=
    ⟨(sha256 b, b), List.mem_map.2 ⟨b, hb, rfl⟩, by simp⟩
  cases hfind : (l.map (fun v => (sha256 v, v))).find? (fun p => p.1 == sha256 b) with
  | none =>
    obtain ⟨p, hp, hpe⟩ := hex
    exact absurd hpe (by simpa using List.find?_eq_none.1 hfind p hp)
  | some p =>
    have hp := List.mem_of_find?_eq_some hfind
    have hpe := List.find?_some hfind
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hp
    simp only [beq_iff_eq] at hpe
    simp [hf v hv b hb hpe]

/-! ## Shape -/

def VSlot3.wf (vs : List ValRec3) : VSlot3 → Prop
  | .ref len h => len < 4294967296 ∧ h.length = 32
  | .val i => (valOf vs i).length < 4294967296

def Kid3.wf : Kid3 → Prop
  | .none => True
  | .hash h => h.length = 32
  | .node _ => True

/-- Field widths (mirrors `PTrie.wf`). -/
def Rec3.wf (vs : List ValRec3) : Rec3 → Prop
  | .leaf k v mem => nibblesOk k = true ∧ (hexPrefix k true).length < 4294967296 ∧ v.wf vs ∧
      mem < 18446744073709551616
  | .ext k kid mem => nibblesOk k = true ∧ (hexPrefix k false).length < 4294967296 ∧
      kid ≠ .none ∧ kid.wf ∧ mem < 18446744073709551616
  | .branch v kids mem => kids.length = 16 ∧ (∀ s, v = some s → s.wf vs) ∧
      (∀ kid ∈ kids, kid.wf) ∧ mem < 18446744073709551616

/-- Rooted DAG of instance `τ`, acyclic by id order. -/
structure RootedDag (ns : List NodeRec3) (vs : List ValRec3) (τ root : Nat) : Prop where
  root_inst : InInst ns τ root
  child : ∀ (n : Nat) (nr : NodeRec3), ns[n]? = some nr → nr.tau = τ → ∀ c, Kid3.node c ∈ nr.node.kids →
    n < c ∧ InInst ns τ c
  vals : ∀ (n : Nat) (nr : NodeRec3), ns[n]? = some nr → nr.tau = τ → ∀ i ∈ nr.node.vids,
    ∃ vr : ValRec3, vs[i]? = some vr ∧ vr.tau = τ
  wf : ∀ (n : Nat) (nr : NodeRec3), ns[n]? = some nr → nr.tau = τ → nr.node.wf vs

/-- Every read key's lookup is determined, within `buildFor`'s fuel. -/
def PathsRevealed (ns : List NodeRec3) (vs : List ValRec3) (root : Nat) (keys : List (List Nat)) : Prop :=
  ∀ k ∈ keys, (fullTree ns vs root).find k ≠ none ∧ fdepth (fullTree ns vs root) k ≤ trieFuel

end ZkFormal.NearV3
