import StateM5a.BusWalk

/-!
# StateM5a.BusSplit — row-local steps of the split / squash ops (request / response buses)

`BusWalk` proves the row-local steps of the walk ops that need no request / response bus (and
`oUN` with `MATQ`/`MATR`).  This file adds the remaining walk ops whose answer comes through a
request / response bus.  Each responder's guarantee is a relation between the request it receives
and the response it sends, proved from the responder row's decoded facts; `Traffic.reqresp`
carries it to the requester; the requester's step takes the relation as a premise.

* **Relations** (one per response bus):
  - `MATR` — `MatRel` (`BusWalk`), responder `SN.oLM`: `matRel_oLM`;
  - `SIBA` — `SibRel`, responder `SN.oLS`: `sibRel_oLS` (the sibling read under the requested ref is
    a leaf `K_kid[d..] ↦ (len, vh)`);
  - `SXR` — `SxRel` (`ExtOver`), responder `SN.oEM`: `sxRel_oEM` (the re-keyed extension
    `K_kid[e..end) ↦ child`, memory `extOwnMem + cm`);
  - `SPR` — answers two request buses, `SPQ` (responder `BR.oSL`: `SplitRel`, `splitRel_oSL`, the
    split branch with the old-side child and the walk's new leaf) and `EPQ` (responder `SN.oEP`:
    `EpRel`, `epRel_oEP`, the extension over the common prefix above the `SPR` answer it received);
    `SprRel` is their union keyed by `(w, depth)`.
* **Bus instantiations** of `Traffic.reqresp`: `mat_reqresp`, `sib_reqresp`, `sx_reqresp`,
  `spr_reqresp`; `splitAns_of_spr` composes the `SPR` answers a split requester receives
  (directly from `oSL`, or from `oEP` over `oSL`) into `SplitAns`: the `SPR` answer at the
  requester's depth is `wrapExt p (branch …)` of the spec's `splitLeaf` / `splitExt`.
* **Steps**: upsert `SN.oLX` `step_leafSplit` (`UChain.leafSplit`); delete `BR.oDL`
  `step_brLeaf` (the kept branch over a materialized leaf descriptor: not covered by
  `step_brKeep`, which takes the child's own ref), `BR.oD1` `step_brOne` (`DChain.brOne`, with the
  sibling through `SIBQ`/`SIBA`).  `SN.oEX` needs a chain constructor `UChain` lacks: it is in
  `StateM5a.BusSplit2` (spec-equation walk semantics).
* **`LocalOK`** wrappers: `localOK_leafSplit`, `localOK_brLeaf`, `localOK_brOne`.
-/

namespace StateM5a.BusWalk

open StateM5a NearSpec NearSpecV3.D2 StateM5a.Steps StateM5a.Walk StateM5a.Store StateM5a.Traffic

/-! ## List / kids helpers -/

theorem drop_app {l p r : List Nat} {d : Nat} (h : l.drop d = p ++ r) : l.drop (d + p.length) = r := by
  rw [← List.drop_drop, h]; simp

theorem take_app {l p r : List Nat} {d : Nat} (h : l.drop d = p ++ r) :
    (l.drop d).take p.length = p := by
  rw [h]; simp

/-- Record children: `n` slots from index `i`, slot `j` holding `f j`. -/
def rkidsFrom : Nat → Nat → (Nat → Option Ref) → RKids
  | 0, _, _ => .nil
  | n + 1, i, f =>
    match f i with
    | some c => .some c (rkidsFrom n (i + 1) f)
    | none => .none (rkidsFrom n (i + 1) f)

/-- The split branch's record children (`kids2` on refs). -/
def rkids2 (x : Nat) (c : Ref) (y : Nat) (d : Ref) : RKids :=
  rkidsFrom 16 0 fun i => if i = x then some c else if i = y then some d else none

theorem kcl_from {σ : Store} (f : Nat → Option Ref) (g : Nat → Option PTrie)
    (h : ∀ j, (f j = none ∧ g j = none) ∨
      ∃ r t, f j = some r ∧ g j = some t ∧ ∃ P, Exp σ (.inl r) (.inl P) ∧ Cl (.inl P) (.inl t)) :
    ∀ n i, KCl σ (rkidsFrom n i f) (kidsFrom n i g)
  | 0, _ => .nil
  | n + 1, i => by
    rcases h i with ⟨h1, h2⟩ | ⟨r, t, h1, h2, h3⟩
    · simp only [rkidsFrom, kidsFrom, h1, h2]; exact .none _ _ (kcl_from f g h n (i + 1))
    · simp only [rkidsFrom, kidsFrom, h1, h2]; exact .some _ _ _ _ h3 (kcl_from f g h n (i + 1))

theorem kcl_rkids2 {σ : Store} {x y : Nat} {r1 r2 : Ref} {c d : PTrie}
    (h1 : ∃ P, Exp σ (.inl r1) (.inl P) ∧ Cl (.inl P) (.inl c))
    (h2 : ∃ P, Exp σ (.inl r2) (.inl P) ∧ Cl (.inl P) (.inl d)) :
    KCl σ (rkids2 x r1 y r2) (kids2 x c y d) := by
  unfold rkids2 kids2
  refine kcl_from _ _ (fun j => ?_) 16 0
  by_cases hx : j = x
  · subst hx; exact Or.inr ⟨r1, c, by simp, by simp, h1⟩
  · by_cases hy : j = y
    · subst hy; exact Or.inr ⟨r2, d, by simp [hx], by simp [hx], h2⟩
    · exact Or.inl ⟨by simp [hx, hy], by simp [hx, hy]⟩

theorem kidsFrom_wf (g : Nat → Option PTrie) (h : ∀ j c, g j = some c → c.wf = true) :
    ∀ n i, Kids.wf (kidsFrom n i g) n = true
  | 0, _ => rfl
  | n + 1, i => by
    cases hg : g i with
    | none =>
      simp only [kidsFrom, hg, Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq]
      exact ⟨by omega, by simpa using kidsFrom_wf g h n (i + 1)⟩
    | some c =>
      simp only [kidsFrom, hg, Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq]
      exact ⟨⟨by omega, h i c hg⟩, by simpa using kidsFrom_wf g h n (i + 1)⟩

theorem kids2_wf {x y : Nat} {c d : PTrie} (hc : c.wf = true) (hd : d.wf = true) :
    Kids.wf (kids2 x c y d) 16 = true := by
  unfold kids2
  refine kidsFrom_wf _ (fun j t ht => ?_) 16 0
  by_cases hx : j = x
  · subst hx; simp at ht; exact ht ▸ hc
  · by_cases hy : j = y
    · subst hy; simp [hx] at ht; exact ht ▸ hd
    · simp [hx, hy] at ht

/-! ## Responses of the materializer and the sibling reader -/

/-- **`SN.oLM`** answers `MATQ(w, d, kid, st2, len, vh)` with `MATR(w, d, kid, ref, mem)`: the leaf
`K_kid[st2..] ↦ (len, vh)` (key: its nibble lookups + `KLEN`) with its spec memory, published under
`ref`. -/
theorem matRel_oLM {σ : Store} {keyOf : Nat → List Nat} {kid st2 len mem : Nat} {vh : Bytes}
    {ref : Ref} {k : List Nat} (hK : (keyOf kid).drop st2 = k)
    (hnew : NewOK σ ref (.leaf k (.ref len vh) (leafMem k len))) (hmem : mem = leafMem k len) :
    MatRel σ keyOf kid st2 len vh ref mem := by
  subst hK; exact ⟨hmem, hnew⟩

/-- What a sibling reader (`SN.oLS`) establishes between a `SIBQ(w, d, ref)` request and its
`SIBA(w, d, kid, len, vh)` answer: the node under `ref` is (`OldOK`) the leaf `K_kid[d..] ↦ (len, vh)`. -/
def SibRel (σ : Store) (keyOf : Nat → List Nat) (d : Nat) (ref : Ref) (kid len : Nat) (vh : Bytes) :
    Prop :=
  ∃ m2, OldOK σ ref (.leaf ((keyOf kid).drop d) (.ref len vh) m2)

/-- **`SN.oLS`**: its old record (read under the requested ref, from `VER` or hashed) is the leaf
`K_kid[d .. d + klen)` (nibble lookups + `KLEN`) with value ref `(len, vh)`. -/
theorem sibRel_oLS {σ : Store} {keyOf : Nat → List Nat} {d kid len m : Nat} {vh : Bytes} {ref : Ref}
    {k : List Nat} (hold : OldOK σ ref (.leaf k (.ref len vh) m)) (hK : (keyOf kid).drop d = k) :
    SibRel σ keyOf d ref kid len vh := by
  subst hK; exact ⟨m, hold⟩

/-! ## Extensions built for a split (`SN.oEP`, `SN.oEM`) -/

/-- An extension `p` over the node under `cref` (memory `cmem`), published under `ref` with memory
`mem = extOwnMem p + cmem`: for any collapse `b` of the child's expansion, `ref` expands to a node
collapsing to `ext p b mem` (well-formed when `b` is). -/
def ExtOver (σ : Store) (p : List Nat) (cref : Ref) (cmem : Nat) (ref : Ref) (mem : Nat) : Prop :=
  mem = extOwnMem p + cmem ∧ ∀ b, (∃ P, Exp σ (.inl cref) (.inl P) ∧ Cl (.inl P) (.inl b)) →
    ∃ P', Exp σ (.inl ref) (.inl P') ∧ Cl (.inl P') (.inl (.ext p b mem)) ∧
      (b.wf = true → (PTrie.ext p b mem).wf = true)

/-- Key `K_kid[d..e)`. -/
def epKey (keyOf : Nat → List Nat) (d e kid : Nat) : List Nat := ((keyOf kid).drop d).take (e - d)

theorem epKey_eq {keyOf : Nat → List Nat} {d kid : Nat} {k r : List Nat}
    (hK : (keyOf kid).drop d = k ++ r) : epKey keyOf d (d + k.length) kid = k := by
  unfold epKey; rw [Nat.add_sub_cancel_left]; exact take_app hK

/-- The row bounds of a new extension: nibbles, hex-prefix length, memory. -/
def ExtBounds (k : List Nat) (mem : Nat) : Prop :=
  nibblesOk k = true ∧ mem < 18446744073709551616 ∧ (hexPrefix k false).length < 4294967296

theorem extOver_of_new {σ : Store} {k : List Nat} {cref ref : Ref} {cmem mem : Nat}
    (hnew : NewOK σ ref (.ext k cref mem)) (hmem : mem = extOwnMem k + cmem) (hw : ExtBounds k mem) :
    ExtOver σ k cref cmem ref mem := by
  refine ⟨hmem, fun b ⟨P, hP, hcl⟩ => ?_⟩
  obtain ⟨P', hP', hcl'⟩ := out_view hnew (N := .ext k b mem) ⟨b, rfl, P, hP, hcl⟩
  refine ⟨P', hP', hcl', fun hb => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hw
  simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨h1, hb⟩, h2⟩, h3⟩

/-- What a re-keying row (`SN.oEM`) establishes between `SXQ(w, e, kid, end, cref, cm)` and its
`SXR(w, e, kid, ref, mem)`: the extension `K_kid[e..end)` over `cref`. -/
def SxRel (σ : Store) (keyOf : Nat → List Nat) (e kid fin : Nat) (cref : Ref) (cm : Nat) (ref : Ref)
    (mem : Nat) : Prop :=
  ExtOver σ (epKey keyOf e fin kid) cref cm ref mem

/-- **`SN.oEM`** (a split's re-keyed extension): key `k = K_kid[d .. d + klen)` (nibble lookups),
`end = d + klen`; it publishes `ext k cref (extOwnMem k + cm)` under `ref`. -/
theorem sxRel_oEM {σ : Store} {keyOf : Nat → List Nat} {d kid fin cm mem : Nat} {cref ref : Ref}
    {k : List Nat} (hK : (keyOf kid).drop d = k ++ (keyOf kid).drop (d + k.length))
    (hfin : fin = d + k.length) (hnew : NewOK σ ref (.ext k cref mem)) (hmem : mem = extOwnMem k + cm)
    (hw : ExtBounds k mem) : SxRel σ keyOf d kid fin cref cm ref mem := by
  unfold SxRel; rw [hfin, epKey_eq hK]; exact extOver_of_new hnew hmem hw

/-- What `SN.oEP` establishes between `EPQ(w, d, e, kid)` and its `SPR(w, d, ref, mem)`: it received
an `SPR(w, e, cref, cmem)` (`sprR`: the `SPR` receives) and published the extension `K_kid[d..e)`
over `cref`. -/
def EpRel (σ : Store) (keyOf : Nat → List Nat) (sprR : List ((Nat × Nat) × (Ref × Nat)))
    (w d e kid : Nat) (ref : Ref) (mem : Nat) : Prop :=
  ∃ cref cmem, ((w, e), (cref, cmem)) ∈ sprR ∧ ExtOver σ (epKey keyOf d e kid) cref cmem ref mem

/-- **`SN.oEP`** (the extension over a split's common prefix): key `k = K_kid[d .. d + klen)`,
`e = d + klen`; it received `SPR(w, e, cref, cmem)` and publishes `ext k cref (extOwnMem k + cmem)`. -/
theorem epRel_oEP {σ : Store} {keyOf : Nat → List Nat} {sprR : List ((Nat × Nat) × (Ref × Nat))}
    {w d e kid cmem mem : Nat} {cref ref : Ref} {k : List Nat}
    (hK : (keyOf kid).drop d = k ++ (keyOf kid).drop (d + k.length)) (he : e = d + k.length)
    (hrecv : ((w, e), (cref, cmem)) ∈ sprR) (hnew : NewOK σ ref (.ext k cref mem))
    (hmem : mem = extOwnMem k + cmem) (hw : ExtBounds k mem) : EpRel σ keyOf sprR w d e kid ref mem := by
  refine ⟨cref, cmem, hrecv, ?_⟩
  rw [he, epKey_eq hK]; exact extOver_of_new hnew hmem hw

/-! ## The split branch (`BR.oSL`) -/

/-- The old-side child of a split as requested on `SPQ`: a leaf to re-key (`xl = 1`: value ref
`(len, vh)`, key the rest of the old key) or a given node (`xl = 0`: ref, memory). -/
inductive OldSide
  | leaf (len : Nat) (vh : Bytes)
  | node (ref : Ref) (mem : Nat)

/-- The old-side child's memory (`xs`: the rest of the old key after the split nibble). -/
def OldSide.mem (xs : List Nat) : OldSide → Nat
  | .leaf len _ => leafMem xs len
  | .node _ m => m

/-- `o` is the old-side child: the re-keyed leaf, or a collapse of the node's expansion. -/
def OldSideOK (σ : Store) (xs : List Nat) : OldSide → PTrie → Prop
  | .leaf len vh, o => o = .leaf xs (.ref len vh) (leafMem xs len)
  | .node r _, o => ∃ P, Exp σ (.inl r) (.inl P) ∧ Cl (.inl P) (.inl o)

/-- Well-formedness the requester provides for the old-side child (a given node's). -/
def OldSide.WF : OldSide → PTrie → Prop
  | .leaf .., _ => True
  | .node .., o => o.wf = true

/-- How `oSL` obtains the old-side child's ref and memory: a re-keyed leaf through `MATQ`/`MATR`
(well-formed: its row bounds), or the given node. -/
def OldSideRow (σ : Store) (keyOf : Nat → List Nat) (xk st : Nat) : OldSide → Ref → Nat → Prop
  | .leaf len vh, r1, m1 => MatRel σ keyOf xk st len vh r1 m1 ∧
      (PTrie.leaf ((keyOf xk).drop st) (.ref len vh) (leafMem ((keyOf xk).drop st) len)).wf = true
  | .node r mm, r1, m1 => r1 = r ∧ m1 = mm

/-- `SPQ(w, e, kid, xk, old side, vlen, vh)` (decoded). -/
structure SpQ where
  kid : Nat
  xk : Nat
  os : OldSide
  vlen : Nat
  vh : Bytes

/-- The split branch: old-side child `o` at `io`, the walk's new leaf `ys ↦ x` at `iy`. -/
def splitBr (io : Nat) (o : PTrie) (iy : Nat) (ys : List Nat) (x : Bytes) (mem : Nat) : PTrie :=
  .branch none (kids2 io o iy (newLeaf ys x)) mem

/-- What `BR.oSL` establishes between `SPQ(w, e, q)` and its `SPR(w, e, ref, mem)`: for the old
key's nibble `io` and the walk key's nibble `iy` at `e`, the old-side child `o` and the written
value `x`, `ref` expands to (a node collapsing to) the split branch, memory `50 + old + new leaf`. -/
def SplitRel (σ : Store) (keyOf : Nat → List Nat) (e : Nat) (q : SpQ) (ref : Ref) (mem : Nat) : Prop :=
  ∀ io iy xs ys o (x : Bytes), (keyOf q.xk).drop e = io :: xs → (keyOf q.kid).drop e = iy :: ys →
    OldSideOK σ xs q.os o → q.vlen = x.length → q.vh = sha256 x →
    mem = 50 + q.os.mem xs + leafMem ys x.length ∧
    ∃ P', Exp σ (.inl ref) (.inl P') ∧ Cl (.inl P') (.inl (splitBr io o iy ys x mem)) ∧
      (q.os.WF o → (splitBr io o iy ys x mem).wf = true)

theorem oldSide_cl {σ : Store} {keyOf : Nat → List Nat} {xk st : Nat} {os : OldSide} {r1 : Ref}
    {m1 : Nat} {o : PTrie} (hrow : OldSideRow σ keyOf xk st os r1 m1)
    (hos : OldSideOK σ ((keyOf xk).drop st) os o) :
    (∃ P, Exp σ (.inl r1) (.inl P) ∧ Cl (.inl P) (.inl o)) ∧ m1 = os.mem ((keyOf xk).drop st) ∧
      (os.WF o → o.wf = true) := by
  cases os with
  | leaf len vh =>
    obtain ⟨⟨hm, hnew⟩, hw⟩ := hrow
    simp only [OldSideOK] at hos; subst hos
    exact ⟨out_view hnew (Or.inl rfl), hm, fun _ => hw⟩
  | node r mm =>
    obtain ⟨rfl, rfl⟩ := hrow
    exact ⟨hos, rfl, id⟩

/-- **`BR.oSL`** (the new branch of a split, at depth `e`): its slot `sib` (= nibble `e` of the old
key `xk`, a `NIB` lookup) holds the old-side child (`OldSideRow`), its slot `nib` (= nibble `e` of
the walk key) the new leaf `K_kid[e+1..] ↦ (vlen, vh)` materialized through `MATQ`/`MATR`
(`MatRel`); no value; memory `50 + m1 + lmem` (`< 2^64`); published under `ref`.  Row bounds: the
new leaf is well-formed. -/
theorem splitRel_oSL {σ : Store} {keyOf : Nat → List Nat} {e : Nat} {q : SpQ} {ref r1 lref : Ref}
    {mem m1 lmem sib nib : Nat}
    (hsib : (keyOf q.xk).drop e = sib :: (keyOf q.xk).drop (e + 1))
    (hnib : (keyOf q.kid).drop e = nib :: (keyOf q.kid).drop (e + 1))
    (hside : OldSideRow σ keyOf q.xk (e + 1) q.os r1 m1)
    (hmat : MatRel σ keyOf q.kid (e + 1) q.vlen q.vh lref lmem)
    (hlw : ∀ x : Bytes, q.vlen = x.length → (newLeaf ((keyOf q.kid).drop (e + 1)) x).wf = true)
    (hnew : NewOK σ ref (.branch none (rkids2 sib r1 nib lref) mem))
    (hmem : mem = 50 + m1 + lmem) (hnb : mem < 18446744073709551616) :
    SplitRel σ keyOf e q ref mem := by
  intro io iy xs ys o x h1 h2 hos hvl hvh
  rw [hsib] at h1; rw [hnib] at h2
  obtain ⟨rfl, rfl⟩ := List.cons.inj h1
  obtain ⟨rfl, rfl⟩ := List.cons.inj h2
  obtain ⟨hcl1, hm1, hw1⟩ := oldSide_cl hside hos
  obtain ⟨hlm, hlnew⟩ := hmat
  rw [hvl, hvh] at hlnew; rw [hvl] at hlm
  have hcl2 := out_view hlnew (N := newLeaf ((keyOf q.kid).drop (e + 1)) x) (Or.inr ⟨x, rfl, rfl⟩)
  refine ⟨by rw [hmem, hm1, hlm], ?_⟩
  obtain ⟨P', hP', hcl'⟩ := out_view hnew (N := splitBr sib o nib ((keyOf q.kid).drop (e + 1)) x mem)
    ⟨_, Or.inl rfl, kcl_rkids2 hcl1 hcl2⟩
  refine ⟨P', hP', hcl', fun hw => ?_⟩
  simp only [splitBr, PTrie.wf, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨trivial, kids2_wf (hw1 hw) (hlw x hvl)⟩, hnb⟩

/-! ## `SPR`: the two request buses it answers, and the composed split answer -/

/-- A request answered on `SPR`: a split (`SPQ`) or a prefix extension (`EPQ(w, d, e, kid)`). -/
inductive SReq
  | spq (q : SpQ)
  | epq (e kid : Nat)

/-- The `SPR` responders' relation, keyed by `(w, depth)`. -/
def SprRel (σ : Store) (keyOf : Nat → List Nat) (sprR : List ((Nat × Nat) × (Ref × Nat))) :
    (Nat × Nat) → SReq → (Ref × Nat) → Prop :=
  fun k r y => match r with
    | .spq q => SplitRel σ keyOf k.2 q y.1 y.2
    | .epq e kid => EpRel σ keyOf sprR k.1 k.2 e kid y.1 y.2

/-- The subtree a split builds: the split branch under the common-prefix extension. -/
def splitTree (p : List Nat) (io : Nat) (o : PTrie) (iy : Nat) (ys : List Nat) (x : Bytes)
    (bm : Nat) : PTrie :=
  wrapExt p (splitBr io o iy ys x bm)

/-- **The split answer at the requester's depth `d`** (split nibble at `e = d + |p|`): the `SPR`
answer `(ref, mem)` is the spec's split subtree `wrapExt p (branch none (kids2 io o iy (newLeaf ys
x)) (50 + old + leafMem))` (up to collapse), its memory `mem`. -/
def SplitAns (σ : Store) (keyOf : Nat → List Nat) (d e : Nat) (q : SpQ) (ref : Ref) (mem : Nat) :
    Prop :=
  ∀ io iy p xs ys o (x : Bytes), d + p.length = e → (keyOf q.xk).drop e = io :: xs →
    (keyOf q.kid).drop d = p ++ iy :: ys → OldSideOK σ xs q.os o → q.vlen = x.length →
    q.vh = sha256 x →
    mem = (splitTree p io o iy ys x (50 + q.os.mem xs + leafMem ys x.length)).memD ∧
    ∃ P', Exp σ (.inl ref) (.inl P') ∧
      Cl (.inl P') (.inl (splitTree p io o iy ys x (50 + q.os.mem xs + leafMem ys x.length))) ∧
      (q.os.WF o → (splitTree p io o iy ys x (50 + q.os.mem xs + leafMem ys x.length)).wf = true)

/-- No common prefix: the `SPR` answer is `oSL`'s. -/
theorem splitAns_direct {σ : Store} {keyOf : Nat → List Nat} {d : Nat} {q : SpQ} {ref : Ref}
    {mem : Nat} (h : SplitRel σ keyOf d q ref mem) : SplitAns σ keyOf d d q ref mem := by
  intro io iy p xs ys o x hpl h1 h2 hos hvl hvh
  have hp : p = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hp
  obtain ⟨hm, hr⟩ := h io iy xs ys o x h1 (by simpa using h2) hos hvl hvh
  subst hm
  exact ⟨rfl, hr⟩

/-- A common prefix: the `SPR` answer is `oEP`'s, over the `SPR` answer it received from `oSL`. -/
theorem splitAns_ext {σ : Store} {keyOf : Nat → List Nat} {sprR : List ((Nat × Nat) × (Ref × Nat))}
    {w d e : Nat} {q : SpQ} {ref : Ref} {mem : Nat} (hde : d < e)
    (hep : EpRel σ keyOf sprR w d e q.kid ref mem)
    (hin : ∀ cref cmem, ((w, e), (cref, cmem)) ∈ sprR → SplitRel σ keyOf e q cref cmem) :
    SplitAns σ keyOf d e q ref mem := by
  intro io iy p xs ys o x hpl h1 h2 hos hvl hvh
  obtain ⟨cref, cmem, hr, hmem, hext⟩ := hep
  have h2' : (keyOf q.kid).drop e = iy :: ys := by rw [← hpl]; exact drop_app h2
  obtain ⟨hcm, Pc, hPc, hclc, hwc⟩ := hin cref cmem hr io iy xs ys o x h1 h2' hos hvl hvh
  have hk : epKey keyOf d e q.kid = p := by
    have := epKey_eq (kid := q.kid) (keyOf := keyOf) h2; rwa [hpl] at this
  rw [hk] at hmem hext
  obtain ⟨P', hP', hcl', hw'⟩ := hext _ ⟨Pc, hPc, hclc⟩
  obtain ⟨a, p', rfl⟩ : ∃ a p', p = a :: p' := by
    cases p with
    | nil => simp at hpl; omega
    | cons a p' => exact ⟨a, p', rfl⟩
  subst hcm
  have hmd : (splitBr io o iy ys x (50 + q.os.mem xs + leafMem ys x.length)).memD =
      50 + q.os.mem xs + leafMem ys x.length := rfl
  subst hmem
  exact ⟨rfl, P', hP', hcl', fun h => hw' (hwc h)⟩

/-! ## The bus instantiations of `Traffic.reqresp` -/

/-- **`SPQ`/`EPQ` → `SPR`.**  Every `SPR` send belongs to an `oSL` (`SPQ` received) or `oEP`
(`EPQ` received) row whose relation holds (`splitRel_oSL`, `epRel_oEP`); at most one request per
`(w, depth)`.  Then every `SPR` received answers the request sent under its key. -/
theorem spr_reqresp {σ : Store} {keyOf : Nat → List Nat} {reqS : List ((Nat × Nat) × SReq)}
    {sprR : List ((Nat × Nat) × (Ref × Nat))} (resp : List ((Nat × Nat) × SReq × (Ref × Nat)))
    (key : Nat × Nat → Nat) (hreq : reqS.Perm (resp.map fun r => (r.1, r.2.1)))
    (hresp : (resp.map fun r => (r.1, r.2.2)).Perm sprR)
    (huniq : ∀ k, reqS.countP (fun p => decide (key p.1 = key k)) ≤ 1)
    (hkey : ∀ k k', key k = key k' → k = k')
    (hrel : ∀ r ∈ resp, SprRel σ keyOf sprR r.1 r.2.1 r.2.2) :
    ∀ k x y, (k, x) ∈ reqS → (k, y) ∈ sprR → SprRel σ keyOf sprR k x y :=
  reqresp (SprRel σ keyOf sprR) resp key hreq hresp huniq hkey hrel

/-- **`MATQ` → `MATR`** (key `(w, depth, kid)`, request `(st2, len, vh)`, answer `(ref, mem)`;
responders `SN.oLM`, `matRel_oLM`). -/
theorem mat_reqresp {σ : Store} {keyOf : Nat → List Nat}
    {reqS : List ((Nat × Nat × Nat) × (Nat × Nat × Bytes))}
    {respR : List ((Nat × Nat × Nat) × (Ref × Nat))}
    (resp : List ((Nat × Nat × Nat) × (Nat × Nat × Bytes) × (Ref × Nat)))
    (key : Nat × Nat × Nat → Nat) (hreq : reqS.Perm (resp.map fun r => (r.1, r.2.1)))
    (hresp : (resp.map fun r => (r.1, r.2.2)).Perm respR)
    (huniq : ∀ k, reqS.countP (fun p => decide (key p.1 = key k)) ≤ 1)
    (hkey : ∀ k k', key k = key k' → k = k')
    (hrel : ∀ r ∈ resp, MatRel σ keyOf r.1.2.2 r.2.1.1 r.2.1.2.1 r.2.1.2.2 r.2.2.1 r.2.2.2) :
    ∀ k x y, (k, x) ∈ reqS → (k, y) ∈ respR → MatRel σ keyOf k.2.2 x.1 x.2.1 x.2.2 y.1 y.2 :=
  reqresp (fun k x y => MatRel σ keyOf k.2.2 x.1 x.2.1 x.2.2 y.1 y.2) resp key hreq hresp huniq hkey hrel

/-- **`SIBQ` → `SIBA`** (key `(w, depth)`, request the sibling's ref, answer `(kid, len, vh)`;
responders `SN.oLS`, `sibRel_oLS`). -/
theorem sib_reqresp {σ : Store} {keyOf : Nat → List Nat} {reqS : List ((Nat × Nat) × Ref)}
    {respR : List ((Nat × Nat) × (Nat × Nat × Bytes))}
    (resp : List ((Nat × Nat) × Ref × (Nat × Nat × Bytes)))
    (key : Nat × Nat → Nat) (hreq : reqS.Perm (resp.map fun r => (r.1, r.2.1)))
    (hresp : (resp.map fun r => (r.1, r.2.2)).Perm respR)
    (huniq : ∀ k, reqS.countP (fun p => decide (key p.1 = key k)) ≤ 1)
    (hkey : ∀ k k', key k = key k' → k = k')
    (hrel : ∀ r ∈ resp, SibRel σ keyOf r.1.2 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2) :
    ∀ k x y, (k, x) ∈ reqS → (k, y) ∈ respR → SibRel σ keyOf k.2 x y.1 y.2.1 y.2.2 :=
  reqresp (fun k x y => SibRel σ keyOf k.2 x y.1 y.2.1 y.2.2) resp key hreq hresp huniq hkey hrel

/-- **`SXQ` → `SXR`** (key `(w, depth, kid)`, request `(end, cref, cm)`, answer `(ref, mem)`;
responders `SN.oEM`, `sxRel_oEM`). -/
theorem sx_reqresp {σ : Store} {keyOf : Nat → List Nat}
    {reqS : List ((Nat × Nat × Nat) × (Nat × Ref × Nat))}
    {respR : List ((Nat × Nat × Nat) × (Ref × Nat))}
    (resp : List ((Nat × Nat × Nat) × (Nat × Ref × Nat) × (Ref × Nat)))
    (key : Nat × Nat × Nat → Nat) (hreq : reqS.Perm (resp.map fun r => (r.1, r.2.1)))
    (hresp : (resp.map fun r => (r.1, r.2.2)).Perm respR)
    (huniq : ∀ k, reqS.countP (fun p => decide (key p.1 = key k)) ≤ 1)
    (hkey : ∀ k k', key k = key k' → k = k')
    (hrel : ∀ r ∈ resp, SxRel σ keyOf r.1.2.1 r.1.2.2 r.2.1.1 r.2.1.2.1 r.2.1.2.2 r.2.2.1 r.2.2.2) :
    ∀ k x y, (k, x) ∈ reqS → (k, y) ∈ respR → SxRel σ keyOf k.2.1 k.2.2 x.1 x.2.1 x.2.2 y.1 y.2 :=
  reqresp (fun k x y => SxRel σ keyOf k.2.1 k.2.2 x.1 x.2.1 x.2.2 y.1 y.2) resp key hreq hresp huniq
    hkey hrel

/-- **The split requester's answer from the `SPR` traffic.**  A split row at `(w, d)` sent
`SPQ(w, e, q)`, and `EPQ(w, d, e, kid)` when `d < e`, and received `SPR(w, d, ref, mem)`: with the
`SPR` relation on every (request sent, answer received) pair (`spr_reqresp`), `(ref, mem)` is the
split answer. -/
theorem splitAns_of_spr {σ : Store} {keyOf : Nat → List Nat} {reqS : List ((Nat × Nat) × SReq)}
    {sprR : List ((Nat × Nat) × (Ref × Nat))}
    (hall : ∀ k x y, (k, x) ∈ reqS → (k, y) ∈ sprR → SprRel σ keyOf sprR k x y)
    {w d e : Nat} {q : SpQ} {ref : Ref} {mem : Nat} (hde : d ≤ e)
    (hq : ((w, e), SReq.spq q) ∈ reqS) (hep : d < e → ((w, d), SReq.epq e q.kid) ∈ reqS)
    (hr : ((w, d), (ref, mem)) ∈ sprR) : SplitAns σ keyOf d e q ref mem := by
  rcases Nat.lt_or_eq_of_le hde with h | rfl
  · exact splitAns_ext h (hall _ _ _ (hep h) hr) (fun cref cmem hc => hall _ _ _ hq hc)
  · exact splitAns_direct (hall _ _ _ hq hr)

/-! ## Upsert: `SN.oLX` (leaf split) -/

/-- **`SN.oLX`** (upsert at a leaf whose key `p ++ x0 :: xs` — `= K_kid2[d..]`, nibble lookups
against `kid2` + `KLEN` — leaves the walk key `K[d..] = p ++ y :: ys` at `x0 ≠ y`, `jm = |p|`): it
requests the split branch at `e = d + jm` (`SPQ`, old side the re-keyed leaf `(L, A)`, the walk's
value `(vlen, vh)`), the prefix extension when `jm ≠ 0` (`EPQ`), and receives the subtree on `SPR`
(`SplitAns`, from `splitAns_of_spr`); its result is that subtree, memory the answer's. -/
theorem step_leafSplit {σ : Store} {keyOf : Nat → List Nat} {K : List Nat} {x : Bytes} {d : Nat}
    {a : Ref} {res : Res} {kid kid2 L m vlen : Nat} {A vh : Bytes} {p xs ys : List Nat} {x0 y : Nat}
    (hold : OldOK σ a (.leaf (p ++ x0 :: xs) (.ref L A) m)) (hKk : keyOf kid = K)
    (hK : K.drop d = p ++ y :: ys) (hxy : x0 ≠ y) (hk2 : (keyOf kid2).drop d = p ++ x0 :: xs)
    (hans : SplitAns σ keyOf d (d + p.length) ⟨kid, kid2, .leaf L A, vlen, vh⟩ res.ref res.nm)
    (hvl : vlen = x.length) (hvh : vh = sha256 x) (hom : res.om = m) : SemU σ K x d a res := by
  intro P hP hPw
  obtain ⟨N, hN, -, hrv⟩ := in_view_wf hold hP hPw
  simp only [RecExp] at hN; subst hN
  have h1 : (keyOf kid2).drop (d + p.length) = x0 :: xs := drop_app hk2
  have h2 : (keyOf kid).drop d = p ++ y :: ys := by rw [hKk]; exact hK
  obtain ⟨hmem, P', hP', hcl, hw⟩ :=
    hans x0 y p xs ys (.leaf xs (.ref L A) (leafMem xs L)) x rfl h1 h2 rfl hvl hvh
  have hu : UChain (.leaf (p ++ x0 :: xs) (.ref L A) m) (K.drop d) x
      (splitTree p x0 (.leaf xs (.ref L A) (leafMem xs L)) y ys x
        (50 + OldSide.mem xs (.leaf L A) + leafMem ys x.length)) := by
    rw [hK]; exact UChain.leafSplit p xs ys x0 y hxy (.ref L A) m x
  exact ⟨_, _, P', hrv _ (.refl _), hu, hP', hcl, by simp [PTrie.mem?, hom], hmem.symm, hw trivial⟩

/-- `SN.oLX` as a `LocalOK` walk row (no `DOWN` child). -/
theorem localOK_leafSplit {σ : Store} {keyOf : Nat → List Nat} (r : WRow Ref Pay Res)
    (hmode : r.din.pay.mode = 1) (hdo : r.dout = none) {kid2 L m : Nat} {A : Bytes}
    {p xs ys : List Nat} {x0 y : Nat}
    (hold : OldOK σ r.din.ref (.leaf (p ++ x0 :: xs) (.ref L A) m))
    (hK : (keyOf r.din.pay.kid).drop r.din.d = p ++ y :: ys) (hxy : x0 ≠ y)
    (hk2 : (keyOf kid2).drop r.din.d = p ++ x0 :: xs)
    (hans : SplitAns σ keyOf r.din.d (r.din.d + p.length)
      ⟨r.din.pay.kid, kid2, .leaf L A, r.din.pay.vlen, r.din.pay.vh⟩ r.uout.ref r.uout.nm)
    (hom : r.uout.om = m) : LocalOK (Sem σ keyOf) r := by
  refine localOK_upsert r hmode ?_
  rw [hdo]
  exact fun x h1 h2 => step_leafSplit hold rfl hK hxy hk2 hans h1 h2 hom

/-! ## Kids lemmas for the squash -/

theorem kids_at_put_ne : ∀ (ks : Kids) {j j' : Nat} (o : Option PTrie), j ≠ j' →
    Kids.at (Kids.put ks j o) j' = Kids.at ks j'
  | .nil, _, _, _, _ => rfl
  | .none r, 0, 0, _, h => absurd rfl h
  | .some _ r, 0, 0, _, h => absurd rfl h
  | .none r, 0, _ + 1, o, _ => by cases o <;> rfl
  | .some _ r, 0, _ + 1, o, _ => by cases o <;> rfl
  | .none r, _ + 1, 0, _, _ => rfl
  | .some _ r, _ + 1, 0, _, _ => rfl
  | .none r, j + 1, j' + 1, o, h => by
    simp only [Kids.put, Kids.at]; exact kids_at_put_ne r o (fun e => h (by rw [e]))
  | .some _ r, j + 1, j' + 1, o, h => by
    simp only [Kids.put, Kids.at]; exact kids_at_put_ne r o (fun e => h (by rw [e]))

theorem kids_at_put_none : ∀ {ks : Kids} {j : Nat} {c : PTrie}, Kids.at ks j = some c →
    Kids.at (Kids.put ks j none) j = none
  | .nil, j, _, h => by cases j <;> simp [Kids.at] at h
  | .none r, 0, _, _ => rfl
  | .some _ r, 0, _, _ => rfl
  | .none r, j + 1, _, h => by simp only [Kids.put, Kids.at] at h ⊢; exact kids_at_put_none h
  | .some _ r, j + 1, _, h => by simp only [Kids.put, Kids.at] at h ⊢; exact kids_at_put_none h

theorem present_nil : ∀ {ks : Kids} {b : Nat}, (∀ j, Kids.at ks j = none) → Kids.present ks b = []
  | .nil, _, _ => rfl
  | .none r, _, h => by simp only [Kids.present]; exact present_nil (fun j => h (j + 1))
  | .some c r, _, h => by have := h 0; simp [Kids.at] at this

theorem present_single : ∀ {ks : Kids} {b i : Nat} {c : PTrie},
    (∀ j, Kids.at ks j = if j = i then some c else none) → Kids.present ks b = [(b + i, c)]
  | .nil, _, i, _, h => by have := h i; simp [Kids.at] at this
  | .none r, _, 0, _, h => by have := h 0; simp [Kids.at] at this
  | .none r, b, i + 1, c, h => by
    simp only [Kids.present]
    rw [present_single (i := i) (fun j => by have := h (j + 1); simpa [Kids.at] using this)]
    congr 2; omega
  | .some c' r, b, 0, c, h => by
    have h0 := h 0
    simp only [Kids.at, ite_true, Option.some.injEq] at h0
    subst h0
    simp only [Kids.present, Nat.add_zero]
    rw [present_nil (fun j => by have := h (j + 1); simpa [Kids.at] using this)]
  | .some c' r, _, _ + 1, _, h => by have := h 0; simp [Kids.at] at this

/-- Revealing two different children. -/
theorem rv_kids_put2 : ∀ {ks : Kids} {n i : Nat} {P Q t u : PTrie}, n ≠ i → Kids.at ks n = some P →
    Kids.at ks i = some Q → Rv (.inl P) (.inl t) → Rv (.inl Q) (.inl u) →
    Rv (.inr ks) (.inr (Kids.put (Kids.put ks n (some t)) i (some u)))
  | .nil, n, _, _, _, _, _, _, h, _, _, _ => by cases n <;> simp [Kids.at] at h
  | .none r, 0, _, _, _, _, _, _, h, _, _, _ => by simp [Kids.at] at h
  | .none r, _ + 1, 0, _, _, _, _, _, _, h, _, _ => by simp [Kids.at] at h
  | .some c r, 0, 0, _, _, _, _, hn, _, _, _, _ => absurd rfl hn
  | .none r, n + 1, i + 1, _, _, _, _, hn, hP, hQ, ht, hu => by
    simp only [Kids.at] at hP hQ; simp only [Kids.put]
    exact .knone _ _ (rv_kids_put2 (fun e => hn (by rw [e])) hP hQ ht hu)
  | .some c r, 0, i + 1, _, _, _, _, _, hP, hQ, ht, hu => by
    simp only [Kids.at, Option.some.injEq] at hP hQ; subst hP; simp only [Kids.put]
    exact .ksome _ _ _ _ ht (rv_kids_put hQ hu)
  | .some c r, n + 1, 0, _, _, _, _, _, hP, hQ, ht, hu => by
    simp only [Kids.at, Option.some.injEq] at hP hQ; subst hQ; simp only [Kids.put]
    exact .ksome _ _ _ _ hu (rv_kids_put hP ht)
  | .some c r, n + 1, i + 1, _, _, _, _, hn, hP, hQ, ht, hu => by
    simp only [Kids.at] at hP hQ; simp only [Kids.put]
    exact .ksome _ _ _ _ (.refl _) (rv_kids_put2 (fun e => hn (by rw [e])) hP hQ ht hu)

/-- A delete chain's leaf result (`oED` / `oD1`: a leaf descriptor) carries its spec memory. -/
theorem dchain_leaf_mem {t : PTrie} {key k : List Nat} {s : Slot} {m2 : Nat}
    (h : DChain t key (true, some (.leaf k s m2))) : m2 = leafMem k s.len := by
  cases h <;> rfl

/-! ## Delete: `BR.oDL` (kept branch over a materialized leaf descriptor) -/

/-- **`BR.oDL`** (delete below a branch that is kept, the child's result a leaf descriptor `LD`):
the descriptor `K_kid2[st2..] ↦ (alen, avh)` is materialized (`MATQ(w, d+1, kid2, st2, alen, avh)`,
answered on `MATR` by an `SN.oLM` row: `MatRel`) and its ref replaces slot `n`; the branch keeps
`≥ 1` child and (a value or `≥ 2` children); memory `m − om + lmem` (`< 2^64`); result `HB`.
(`step_brKeep` does not cover it: it puts the child's own result ref, which a descriptor lacks.) -/
theorem step_brLeaf {σ : Store} {keyOf : Nat → List Nat} {K : List Nat} {d : Nat} {a c lref : Ref}
    {res cres : Res} {v : Option Slot} {rcs : RKids} {m n lmem : Nat}
    (hold : OldOK σ a (.branch v rcs m)) (hat : rcs.at n = some c) (hK : K.drop d = n :: K.drop (d + 1))
    (hrkc : cres.rk = RK_LD) (hrk : res.rk = RK_HB)
    (hmat : MatRel σ keyOf cres.kid2 cres.st2 cres.alen cres.avh lref lmem)
    (hnew : NewOK σ res.ref (.branch v (rcs.put n (some lref)) (m - cres.om + lmem)))
    (hcnt : (rcs.put n (some lref)).count ≠ 0)
    (hcnt1 : v = none → (rcs.put n (some lref)).count ≠ 1)
    (hom : res.om = m) (hnm : res.nm = m - cres.om + lmem) (hnb : res.nm < 18446744073709551616)
    (hc : SemD σ keyOf K (d + 1) c cres) : SemD σ keyOf K d a res := by
  intro P hP hPw
  obtain ⟨N, ⟨ks, rfl, hks⟩, hNw, hrv⟩ := in_view_wf hold hP hPw
  obtain ⟨Pc, hat', hPc⟩ := kexp_at hks hat
  simp only [PTrie.wf, Bool.and_eq_true] at hNw
  obtain ⟨tc, bc, oc, hrc, hdc, hmc, hresc, hwc⟩ := hc Pc hPc (kids_wf_at hNw.1.2 hat')
  obtain ⟨m2, rfl, rfl⟩ : ∃ m2, oc = some (.leaf ((keyOf cres.kid2).drop cres.st2)
      (.ref cres.alen cres.avh) m2) ∧ bc = true := by
    cases oc with
    | none => simp only [DRes] at hresc; rw [hresc.1] at hrkc; simp [RK_NONE, RK_LD] at hrkc
    | some t' =>
      simp only [DRes] at hresc
      rcases hresc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hb, m2, rfl⟩
      · rw [h] at hrkc; simp [RK_LD, RK_SAME] at hrkc
      · rcases h with h | h | h <;> rw [h] at hrkc <;> simp [RK_H, RK_HB, RK_HE, RK_LD] at hrkc
      · exact ⟨m2, rfl, hb⟩
  have hm2 := dchain_leaf_mem hdc
  simp only [Slot.len] at hm2
  subst hm2
  obtain ⟨hlm, hlnew⟩ := hmat
  subst hlm
  obtain ⟨Pl, hPl, hcll⟩ := out_view hlnew (Or.inl rfl)
  have hcl := kcl_put (kcl_of_exp hks) hat ⟨Pl, hPl, hcll⟩
  have hr : Rv (.inl P) (.inl (.branch v (Kids.put ks n (some tc)) m)) :=
    hrv _ (.branch _ _ _ _ (rv_kids_put hat' hrc))
  have hpp := kids_put_put ks n (some tc) (some (.leaf ((keyOf cres.kid2).drop cres.st2)
    (.ref cres.alen cres.avh) (leafMem ((keyOf cres.kid2).drop cres.st2) cres.alen)))
  have hlen := kcl_present_length hcl 0
  refine ⟨_, true, some (.branch v (Kids.put (Kids.put ks n (some tc)) n (some (.leaf
    ((keyOf cres.kid2).drop cres.st2) (.ref cres.alen cres.avh)
    (leafMem ((keyOf cres.kid2).drop cres.st2) cres.alen))))
    (m - cres.om + leafMem ((keyOf cres.kid2).drop cres.st2) cres.alen)), hr, ?_,
    by simp [PTrie.mem?, hom], ?_, ?_⟩
  · rw [hK]
    refine DChain.brKeep v _ m n _ tc _ cres.om (kids_put_at tc hat') hmc hdc ?_ ?_
    · rw [hpp]; intro e; rw [e] at hlen; exact hcnt hlen.symm
    · rw [hpp]; intro hv e; rw [e] at hlen; exact hcnt1 hv hlen.symm
  · obtain ⟨P', hP', hcl'⟩ := out_view hnew (N := .branch v (Kids.put ks n (some (.leaf
      ((keyOf cres.kid2).drop cres.st2) (.ref cres.alen cres.avh)
      (leafMem ((keyOf cres.kid2).drop cres.st2) cres.alen))))
      (m - cres.om + leafMem ((keyOf cres.kid2).drop cres.st2) cres.alen)) ⟨_, Or.inl rfl, hcl⟩
    refine Or.inr (Or.inl ⟨Or.inr (Or.inl hrk), rfl, P', hP', ?_, ?_, fun _ => ⟨_, _, _, rfl⟩⟩)
    · rw [hpp]; exact hcl'
    · exact hnm.symm
  · intro t' e; cases e
    simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq]
    rw [hpp]
    refine ⟨⟨hNw.1.1, kids_wf_put hNw.1.2 hat' (hwc _ rfl)⟩, ?_⟩
    rw [← hnm]; exact hnb

/-- `BR.oDL` as a `LocalOK` walk row (child at depth `d + 1`). -/
theorem localOK_brLeaf {σ : Store} {keyOf : Nat → List Nat} (r : WRow Ref Pay Res)
    (hmode : r.din.pay.mode = 2) {cd : Down Ref Pay} (hdo : r.dout = some cd)
    (hpay : cd.pay = r.din.pay) (hcd : cd.d = r.din.d + 1) {lref : Ref} {v : Option Slot}
    {rcs : RKids} {m n lmem : Nat} (hold : OldOK σ r.din.ref (.branch v rcs m))
    (hat : rcs.at n = some cd.ref)
    (hK : (keyOf r.din.pay.kid).drop r.din.d = n :: (keyOf r.din.pay.kid).drop (r.din.d + 1))
    (hrkc : r.uin.rk = RK_LD) (hrk : r.uout.rk = RK_HB)
    (hmat : MatRel σ keyOf r.uin.kid2 r.uin.st2 r.uin.alen r.uin.avh lref lmem)
    (hnew : NewOK σ r.uout.ref (.branch v (rcs.put n (some lref)) (m - r.uin.om + lmem)))
    (hcnt : (rcs.put n (some lref)).count ≠ 0)
    (hcnt1 : v = none → (rcs.put n (some lref)).count ≠ 1)
    (hom : r.uout.om = m) (hnm : r.uout.nm = m - r.uin.om + lmem)
    (hnb : r.uout.nm < 18446744073709551616) : LocalOK (Sem σ keyOf) r := by
  refine localOK_delete r hmode ?_
  rw [hdo]
  refine ⟨hpay, fun hc => ?_⟩
  rw [hcd] at hc
  exact step_brLeaf hold hat hK hrkc hrk hmat hnew hcnt hcnt1 hom hnm hnb hc

/-! ## Delete: `BR.oD1` (squash onto the one remaining leaf sibling) -/

/-- The squashed slots: after the deleted child (slot `n`) is removed, only the sibling (slot `i`)
is left. -/
theorem present_squash {ks : Kids} {n i : Nat} {Pc Ps tc ts : PTrie} (hni : n ≠ i)
    (hat : Kids.at ks n = some Pc) (hsat : Kids.at ks i = some Ps)
    (hoth : ∀ j, j ≠ n → j ≠ i → Kids.at ks j = none) :
    Kids.present (Kids.put (Kids.put (Kids.put ks n (some tc)) i (some ts)) n none) 0 = [(i, ts)] := by
  have := present_single (b := 0) (i := i) (c := ts)
    (ks := Kids.put (Kids.put (Kids.put ks n (some tc)) i (some ts)) n none) (fun j => by
      by_cases hjn : j = n
      · subst hjn
        simp only [hni, ↓reduceIte]
        refine kids_at_put_none (c := tc) ?_
        rw [kids_at_put_ne _ _ (Ne.symm hni)]; exact kids_put_at tc hat
      · rw [kids_at_put_ne _ _ (Ne.symm hjn)]
        by_cases hji : j = i
        · subst hji
          simp only [↓reduceIte]
          exact kids_put_at _ (by rw [kids_at_put_ne _ _ hni]; exact hsat)
        · simp only [hji, ↓reduceIte]
          rw [kids_at_put_ne _ _ (Ne.symm hji), kids_at_put_ne _ _ (Ne.symm hjn)]
          exact hoth j hjn hji)
  simpa using this

/-- **`BR.oD1`** (delete below a branch without a value whose child vanished (`NONE`) and whose only
other child, at slot `i`, is a leaf): the sibling's ref is sent on `SIBQ(w, d+1, sref)` and read by
an `SN.oLS` row (`SIBA(w, d+1, kid2, len, vh)`: `SibRel`), its key continuing with nibble `i`
(`NIB(kid2, d, i)`); the result is the leaf descriptor `K_kid2[d..] ↦ (len, vh)` (`LD`,
`squashBranch` → `extendChild [i] leaf`).  Row facts: the two children `n ≠ i`, no other slot; the
descriptor's leaf is well-formed. -/
theorem step_brOne {σ : Store} {keyOf : Nat → List Nat} {K : List Nat} {d : Nat} {a c sref : Ref}
    {res cres : Res} {rcs : RKids} {m n i kid2 len : Nat} {vh : Bytes}
    (hold : OldOK σ a (.branch none rcs m)) (hat : rcs.at n = some c) (hsat : rcs.at i = some sref)
    (hni : n ≠ i) (hoth : ∀ j, j ≠ n → j ≠ i → rcs.at j = none)
    (hK : K.drop d = n :: K.drop (d + 1)) (hrkc : cres.rk = RK_NONE) (hrk : res.rk = RK_LD)
    (hsib : SibRel σ keyOf (d + 1) sref kid2 len vh)
    (hK2 : (keyOf kid2).drop d = i :: (keyOf kid2).drop (d + 1))
    (hk2 : res.kid2 = kid2) (hst : res.st2 = d) (hal : res.alen = len) (hah : res.avh = vh)
    (hom : res.om = m)
    (hdw : (PTrie.leaf ((keyOf kid2).drop d) (.ref len vh) (leafMem ((keyOf kid2).drop d) len)).wf = true)
    (hc : SemD σ keyOf K (d + 1) c cres) : SemD σ keyOf K d a res := by
  intro P hP hPw
  obtain ⟨N, ⟨ks, rfl, hks⟩, hNw, hrv⟩ := in_view_wf hold hP hPw
  obtain ⟨Pc, hat', hPc⟩ := kexp_at hks hat
  obtain ⟨Ps, hsat', hPs⟩ := kexp_at hks hsat
  simp only [PTrie.wf, Bool.and_eq_true] at hNw
  obtain ⟨tc, bc, oc, hrc, hdc, hmc, hresc, -⟩ := hc Pc hPc (kids_wf_at hNw.1.2 hat')
  obtain ⟨rfl, rfl⟩ : oc = none ∧ bc = true := by
    cases oc with
    | none => simp only [DRes] at hresc; exact ⟨rfl, hresc.2⟩
    | some t' =>
      exfalso
      simp only [DRes] at hresc
      rcases hresc with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · rw [h] at hrkc; simp [RK_NONE, RK_SAME] at hrkc
      · rcases h with h | h | h <;> rw [h] at hrkc <;> simp [RK_H, RK_HB, RK_HE, RK_NONE] at hrkc
      · rw [h] at hrkc; simp [RK_LD, RK_NONE] at hrkc
  obtain ⟨m2, hsold⟩ := hsib
  obtain ⟨Ns, hNs, hrvs⟩ := in_view hsold hPs
  simp only [RecExp] at hNs; subst hNs
  have hr : Rv (.inl P) (.inl (.branch none (Kids.put (Kids.put ks n (some tc)) i (some (.leaf
      ((keyOf kid2).drop (d + 1)) (.ref len vh) m2))) m)) :=
    hrv _ (.branch _ _ _ _ (rv_kids_put2 hni hat' hsat' hrc (hrvs _ (.refl _))))
  have hp := present_squash (tc := tc) (ts := .leaf ((keyOf kid2).drop (d + 1)) (.ref len vh) m2)
    hni hat' hsat' (fun j h1 h2 => kexp_at_none hks (hoth j h1 h2))
  have hch := DChain.brOne _ m n i _ _ tc cres.om (.ref len vh) m2
    (by rw [kids_at_put_ne _ _ (Ne.symm hni)]; exact kids_put_at tc hat') hmc hdc hp
  have hkey : [i] ++ (keyOf kid2).drop (d + 1) = (keyOf kid2).drop d := by rw [hK2]; rfl
  simp only [hkey, Slot.len] at hch
  refine ⟨_, true, _, hr, hK ▸ hch, by simp [PTrie.mem?, hom], ?_, ?_⟩
  · refine Or.inr (Or.inr ⟨hrk, rfl, leafMem ((keyOf kid2).drop d) len, ?_⟩)
    rw [hk2, hst, hal, hah]
  · intro t' e; cases e; exact hdw

/-- `BR.oD1` as a `LocalOK` walk row (child at depth `d + 1`). -/
theorem localOK_brOne {σ : Store} {keyOf : Nat → List Nat} (r : WRow Ref Pay Res)
    (hmode : r.din.pay.mode = 2) {cd : Down Ref Pay} (hdo : r.dout = some cd)
    (hpay : cd.pay = r.din.pay) (hcd : cd.d = r.din.d + 1) {sref : Ref} {rcs : RKids}
    {m n i kid2 len : Nat} {vh : Bytes}
    (hold : OldOK σ r.din.ref (.branch none rcs m)) (hat : rcs.at n = some cd.ref)
    (hsat : rcs.at i = some sref) (hni : n ≠ i) (hoth : ∀ j, j ≠ n → j ≠ i → rcs.at j = none)
    (hK : (keyOf r.din.pay.kid).drop r.din.d = n :: (keyOf r.din.pay.kid).drop (r.din.d + 1))
    (hrkc : r.uin.rk = RK_NONE) (hrk : r.uout.rk = RK_LD)
    (hsib : SibRel σ keyOf (r.din.d + 1) sref kid2 len vh)
    (hK2 : (keyOf kid2).drop r.din.d = i :: (keyOf kid2).drop (r.din.d + 1))
    (hk2 : r.uout.kid2 = kid2) (hst : r.uout.st2 = r.din.d) (hal : r.uout.alen = len)
    (hah : r.uout.avh = vh) (hom : r.uout.om = m)
    (hdw : (PTrie.leaf ((keyOf kid2).drop r.din.d) (.ref len vh)
      (leafMem ((keyOf kid2).drop r.din.d) len)).wf = true) : LocalOK (Sem σ keyOf) r := by
  refine localOK_delete r hmode ?_
  rw [hdo]
  refine ⟨hpay, fun hc => ?_⟩
  rw [hcd] at hc
  exact step_brOne hold hat hsat hni hoth hK hrkc hrk hsib hK2 hk2 hst hal hah hom hdw hc

end StateM5a.BusWalk
