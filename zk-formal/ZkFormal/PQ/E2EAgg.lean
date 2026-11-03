import ZkFormal.PQ.E2EBridge
import ZkFormal.PQ.Aggregation.Statement

/-!
# ZkFormal.PQ.E2EAgg — `NodeOK` and `WrapOK` from the pinned aggregation node program

Lane E (E2E M11c), 2026-11-03. `E2EBridge.lean` (M11b) derives obligation 1 of `e2e_sound` from
`NvFaithful` plus three interface facts `NodeOK`, `Extract`, `WrapOK`, all hypotheses. This file
instantiates the node and wrap verifiers with the **pinned aggregation program** and proves the
first and third from it; `Extract` stays a hypothesis, now stated against the backend.

## The pinned node program

`build_agg` in `research/near-compression/native/recursion/patches/openvm-recursion-agg.patch`
(`RangeStmt`, `RangeStmt::compose`, `check_range_statement`):

1. it takes `k ≥ 2` children (`assert!(children.len() >= 2)`);
2. for each child it runs the in-circuit inner verifier (`build_verifier`) on the child's key and
   proof and reads the child's range statement `(ctx, a, e, s_a, s_e)`: for an app child from its
   public values (`of_segment`), for a node child as a loaded preimage whose tag-9 SHA-384 digest
   (`hash_range`) must equal the child's exposed digest;
3. continuity: every child's `ctx` equals child 0's, `a_i = e_{i-1}`, `s_a_i = s_e_{i-1}`;
4. it exposes `[level, D(out)]` with `out = (f.ctx, f.a, l.e, f.s_a, l.s_e)` (first and last
   child), `D` the tag-9 range digest.

Steps 3–4 are exactly `Stmt.compose` of `ZkFormal.PQ.Aggregation.Statement` (the Lean transcription
of `RangeStmt::compose`, with `compose_eq_root` / `chainable_of_composeFrom_some` proved there).
So the native meaning of the node program is `aggNodeV`: every child accepted by its own native
verifier, and `compose (child statements) = some out` with `D(out)` the exposed digest. Its
acceptance is a definition here, not an assumption; what is assumed about it is only
`NvFaithful` (lane `pq-nv-faithful`: an accepting node *trace* means `aggNodeV` accepts).

## What is proved

* `nodeOK_agg` — the node verifier's acceptance gives accepted children whose boundaries chain
  from `out.s_a` to `out.s_e` (this is `NodeOK`, now a theorem about `aggNodeV`);
* `wrapOK_agg` — `WrapOK` from `NvFaithful` of the wrap circuit, the wrap's own extraction, and
  the wrap program `aggWrapV` (verify the root, `ctx` = the claim digest, `InitOK`, `FinalOK`);
* `leaves_of_acc_agg` / `nvFaithfulE2E_of_agg` / `e2e_sound_of_agg` — obligation 1 and the E2E
  statement from `NvFaithful` (node and wrap), `ExtractWG` and the four bad events.

## What remains (stated precisely)

* `NvFaithful A.Pin A.D (aggNodeV …)` and `NvFaithful A.PinW A.DW (aggWrapV …)`: an accepting
  node (wrap) trace means the native node (wrap) program accepts. Five of six sub-obligations
  open (`NvFaithful.lean`), unchanged.
* `ExtractWG`: the WHIR / LogUp-GKR straight-line extractor (below), with the event `BE.Any`.
  Its probability bound is a QROM statement and is not a Lean theorem (no measure theory in this
  library); the bound it must meet is recorded in `BadEvents`.
* `RangeColl`: a tag-9 range-digest collision is one of the bad events (SHA-384 CR).
-/

namespace ZkFormal.PQ.E2EAgg

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.Nv ZkFormal.PQ.E2EBridge
open ZkFormal.PQ.Aggregation.Stmt
open NearSpecV3.E2E

/-! ## The pinned node and wrap programs, natively -/

/-- **The native node program** (`build_agg`). The node's own statement is its exposed digest
`d = D(out)`; the children are `(preimage statement, proof)`. -/
def aggNodeV {α Dg Proof Params : Type} [DecidableEq α] (Acc : Stmt α → Proof → Prop)
    (rdigest : Stmt α → Dg) : NvVerifier Dg (List (Stmt α × Proof)) Params where
  Execution _ _ _ := PUnit
  accepts d kids _ _ := 2 ≤ kids.length ∧ (∀ c ∈ kids, Acc c.1 c.2) ∧
    ∃ out, compose (kids.map Prod.fst) = some out ∧ rdigest out = d
  run _ _ _ := PUnit.unit

/-- **The native wrap program**: verify the root proof against its statement (loaded as a
preimage), check the chunk context against the public statement, and the wrap checks on the root
boundaries. -/
def aggWrapV {Bnd Proof Params : Type} (Acc : Stmt Bnd → Proof → Prop)
    (ctxOf : PublicStmt → Bnd) (InitOK FinalOK : PublicStmt → Bnd → Prop) :
    NvVerifier PublicStmt (Stmt Bnd × Proof) Params where
  Execution _ _ _ := PUnit
  accepts s rp _ _ := Acc rp.1 rp.2 ∧ rp.1.ctx = ctxOf s ∧ InitOK s rp.1.sa ∧ FinalOK s rp.1.se
  run _ _ _ := PUnit.unit

/-! ## `compose` chains the boundaries -/

theorem composeFrom_chain {α : Type} [DecidableEq α] :
    ∀ (l : List (Stmt α)) (acc out : Stmt α), composeFrom acc l = some out →
      out.sa = acc.sa ∧ BndChained acc.se (l.map fun s => (s.sa, s.se)) out.se
  | [], acc, out, h => by
    simp only [composeFrom, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | t :: rest, acc, out, h => by
    simp only [composeFrom] at h
    obtain ⟨c, hc, hrest⟩ := Option.bind_eq_some_iff.mp h
    by_cases hch : Chains acc t
    · rw [compose₂_eq_some hch, Option.some.injEq] at hc
      subst hc
      obtain ⟨h1, h2⟩ := composeFrom_chain rest _ out hrest
      exact ⟨h1, hch.2.2.symm, h2⟩
    · rw [compose₂_eq_none hch] at hc
      cases hc

/-- **`compose` of the children's statements chains their boundaries from the composed start to
the composed end.** -/
theorem compose_chain {α P : Type} [DecidableEq α] (kids : List (Stmt α × P)) (out : Stmt α)
    (h : compose (kids.map Prod.fst) = some out) :
    BndChained out.sa (kids.map fun c => (c.1.sa, c.1.se)) out.se := by
  cases kids with
  | nil => simp [compose] at h
  | cons s rest =>
    simp only [List.map_cons, compose] at h
    obtain ⟨h1, h2⟩ := composeFrom_chain _ s.1 out h
    refine ⟨h1, ?_⟩
    simpa [List.map_map, Function.comp_def] using h2

/-- **`NodeOK`, proved for the pinned node program.** -/
theorem nodeOK_agg {α Dg Proof Params : Type} [DecidableEq α] (Acc : Stmt α → Proof → Prop)
    (rdigest : Stmt α → Dg) (d : Dg) (kids : List (Stmt α × Proof)) (q : Params)
    (e : (aggNodeV (Params := Params) Acc rdigest).Execution d kids q)
    (h : (aggNodeV Acc rdigest).accepts d kids q e) :
    (∀ c ∈ kids, Acc c.1 c.2) ∧
      ∃ out, rdigest out = d ∧ BndChained out.sa (kids.map fun c => (c.1.sa, c.1.se)) out.se := by
  obtain ⟨-, hk, out, hc, hd⟩ := h
  exact ⟨hk, out, hd, compose_chain kids out hc⟩

/-! ## The backend's extractor and its bad events -/

/-- **The bad events** of the WHIR / LogUp-GKR backend over the transcript of one final proof
(each a `Prop`; the QROM bounds they must meet are the soundness budget, not Lean theorems):

* `hashColl` — the adversary's SHA-384 queries (Merkle nodes, transcript, 42-B truncation)
  contain a collision; at `Q` queries the event has probability `≤ Q²/2^337` for 42-B digests;
* `whirBad` — some WHIR challenge (folding randomness, OOD point, the ×15 query sampler) falls in
  the proximity-gap bad set of its round, the round-by-round error `ε_WHIR` of the pinned
  parameters (`WhirConfig`, O-2 table), times `Q`;
* `gkrBad` — some LogUp-GKR challenge (the LogUp `α`, `β`, a GKR sumcheck point) falls in its
  Schwartz–Zippel bad set (`ε_LogUp`, `ε_GKR` of `FAITHFUL.md` §2(f)), times `Q`;
* `rangeColl` — two distinct range statements with equal tag-9 digest (a SHA-384 collision of the
  statement message). -/
structure BadEvents where
  hashColl : Prop
  whirBad : Prop
  gkrBad : Prop
  rangeColl : Prop

/-- The union of the bad events. -/
def BadEvents.Any (BE : BadEvents) : Prop := BE.hashColl ∨ BE.whirBad ∨ BE.gkrBad ∨ BE.rangeColl

/-- The aggregation interface over a segment system, at the pinned node program. -/
structure AggNode (S : SegSystem) where
  Proof : Type
  Params : Type
  /-- The tag-9 range digest type and function (`RangeStmt::digest`). -/
  Dg : Type
  rdigest : Stmt S.Bnd → Dg
  /-- Native acceptance of a proof (leaf template key or node key) for a range statement. -/
  Acc : Stmt S.Bnd → Proof → Prop
  /-- The recursion level of a proof (`pv0`; 0 for leaves). -/
  level : Proof → Nat
  /-- The verifying keys: a leaf template or the node. -/
  isLeaf : Proof → Option S.Template
  /-- The leaf templates' AIRs and public values `[ctx.., j, pre.., post..]` (`of_segment`). -/
  segAir : S.Template → Air
  segPub : Proof → List Fp
  segStmt : List Fp → Stmt S.Bnd
  /-- The node circuit: pinned AIR, decode (`D.stmt` = the exposed digest, `D.proof` = the
  children's `(preimage, proof)` read from the trace). -/
  Pin : NvPinned
  D : NvDecode Dg (List (Stmt S.Bnd × Proof)) Params
  /-- The extracted trace: the committed columns read off the WHIR openings. -/
  ext : Proof → Trace Fp
  pub : Proof → List Fp

/-- **The straight-line extractor of the WHIR / LogUp-GKR backend** (knowledge soundness), per
accepted proof: unless a bad event occurs, the trace `ext π` read off the WHIR openings satisfies
the key's AIR with the LogUp (field) balance, at public values that decode to the proof's
statement. For a leaf template `k` that means `HoldsLogUp (segAir k)` at `segPub π` with
`segStmt (segPub π) = st`; for the node key, `HoldsLogUp Pin.air` at `pub π` with `D.stmt (pub π) =
D(st)` and children of lower level (the level constraint `level = child level + 1`). -/
def ExtractWG {S : SegSystem} (A : AggNode S) (BE : BadEvents) : Prop :=
  ∀ st π, A.Acc st π → BE.Any ∨
    (∃ k, A.isLeaf π = some k ∧ HoldsLogUp (A.segAir k) (A.segPub π) (A.ext π) ∧
      A.segStmt (A.segPub π) = st) ∨
    (A.isLeaf π = none ∧ HoldsLogUp A.Pin.air (A.pub π) (A.ext π) ∧
      A.D.stmt (A.pub π) = A.rdigest st ∧
      ∀ c ∈ A.D.proof (A.ext π), A.level c.2 < A.level π)

/-- **Leaf templates are the segment system's**: a leaf trace satisfying template `k`'s AIR at
public values decoding to `st` is a satisfied segment instance from `st.sa` to `st.se`. This is the
definition of `S.Holds` for the circuit's segment system (a `def`-level identity there). -/
def LeafHolds {S : SegSystem} (A : AggNode S) : Prop :=
  ∀ k (pubv : List Fp) (tr : Trace Fp), HoldsLogUp (A.segAir k) pubv tr →
    ∃ tr', S.Holds k (A.segStmt pubv).sa (A.segStmt pubv).se tr'

/-- The range digest is binding unless `rangeColl`. -/
def RangeBinding {S : SegSystem} (A : AggNode S) (BE : BadEvents) : Prop :=
  ∀ a b, A.rdigest a = A.rdigest b → a = b ∨ BE.rangeColl

/-- **Every accepted proof unfolds to satisfied leaves chaining across its statement**, unless a
bad event occurs. -/
theorem leaves_of_acc_agg {S : SegSystem} [DecidableEq S.Bnd] (A : AggNode S) (BE : BadEvents)
    (hNv : NvFaithful A.Pin A.D (aggNodeV (Params := A.Params) A.Acc A.rdigest))
    (hEx : ExtractWG A BE) (hLeaf : LeafHolds A) (hR : RangeBinding A BE) (hBad : ¬BE.Any) :
    ∀ (n : Nat) (st : Stmt S.Bnd) (π : A.Proof), A.level π < n → A.Acc st π →
      Leaves S st.sa st.se
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, st, π, hn, hacc => by
    rcases hEx st π hacc with hb | ⟨k, -, hl, hst⟩ | ⟨-, hl, hst, hlt⟩
    · exact absurd hb hBad
    · obtain ⟨tr', h⟩ := hLeaf k _ _ hl
      rw [hst] at h
      exact ⟨[(k, st.sa, st.se, tr')], by simpa using h, ⟨rfl, rfl⟩⟩
    · obtain ⟨e, he⟩ := hNv (A.ext π) (A.pub π) hl
      obtain ⟨hkids, out, hd, hchain⟩ :=
        nodeOK_agg A.Acc A.rdigest _ _ _ e he
      rw [hst] at hd
      rcases hR _ _ hd with hout | hc
      · subst hout
        exact leaves_of_kids ((A.D.proof (A.ext π)).map fun c => (c.1.sa, c.1.se, c.2)) _ _
          (fun c hc => by
            obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
            exact leaves_of_acc_agg A BE hNv hEx hLeaf hR hBad n c0.1 c0.2
              (by have := hlt c0 hc0; omega) (hkids c0 hc0))
          (by simpa [List.map_map, Function.comp_def] using hchain)
      · exact absurd (.inr (.inr (.inr hc))) hBad

/-! ## The wrap -/

/-- The wrap circuit (ZK final layer) and its extraction. -/
structure AggWrap {S : SegSystem} (A : AggNode S) where
  ParamsW : Type
  ctxOf : PublicStmt → S.Bnd
  PinW : NvPinned
  DW : NvDecode PublicStmt (Stmt S.Bnd × A.Proof) ParamsW

/-- **The wrap's extraction** (WHIR / LogUp-GKR, as `ExtractWG`, for the wrap key): an accepted
final proof has an extracted trace satisfying the wrap AIR at public values decoding to the public
statement, unless a bad event occurs. `extW π` is the wrap proof's extracted trace, `pubW π` its
public values. -/
def ExtractW {S : SegSystem} {A : AggNode S} (Wr : AggWrap A) {Proof : Type}
    (extW : Proof → Trace Fp) (pubW : Proof → List Fp)
    (FinalVerify : PublicStmt → Proof → Bool) (BE : BadEvents) : Prop :=
  ∀ s π, FinalVerify s π = true → BE.Any ∨
    (HoldsLogUp Wr.PinW.air (pubW π) (extW π) ∧ Wr.DW.stmt (pubW π) = s)

/-- **`WrapOK`, proved for the pinned wrap program**: final acceptance gives an accepted root
statement whose context is the claim's and whose boundaries pass the wrap checks. -/
theorem wrapOK_agg {S : SegSystem} {A : AggNode S} (Wr : AggWrap A) (W : WrapCheck S)
    {Proof : Type} (FinalVerify : PublicStmt → Proof → Bool) (BE : BadEvents)
    (hNvW : NvFaithful Wr.PinW Wr.DW (aggWrapV (Params := Wr.ParamsW) A.Acc Wr.ctxOf W.InitOK W.FinalOK))
    (extW : Proof → Trace Fp) (pubW : Proof → List Fp)
    (hExW : ExtractW Wr extW pubW FinalVerify BE) :
    ∀ s π, FinalVerify s π = true → BE.Any ∨
      ∃ st p, A.Acc st p ∧ st.ctx = Wr.ctxOf s ∧ W.InitOK s st.sa ∧ W.FinalOK s st.se := by
  intro s π hv
  rcases hExW s π hv with hb | ⟨hl, hs⟩
  · exact .inl hb
  obtain ⟨e, he⟩ := hNvW _ _ hl
  rw [hs] at he
  exact .inr ⟨_, _, he⟩

/-- **E2E obligation 1 from the pinned aggregation and wrap programs.** -/
theorem nvFaithfulE2E_of_agg {S : SegSystem} [DecidableEq S.Bnd] (A : AggNode S)
    (Wr : AggWrap A) (W : WrapCheck S) {Proof : Type} (FinalVerify : PublicStmt → Proof → Bool)
    (BE : BadEvents)
    (hNv : NvFaithful A.Pin A.D (aggNodeV (Params := A.Params) A.Acc A.rdigest))
    (hNvW : NvFaithful Wr.PinW Wr.DW (aggWrapV (Params := Wr.ParamsW) A.Acc Wr.ctxOf W.InitOK W.FinalOK))
    (hEx : ExtractWG A BE) (extW : Proof → Trace Fp) (pubW : Proof → List Fp)
    (hExW : ExtractW Wr extW pubW FinalVerify BE)
    (hLeaf : LeafHolds A) (hR : RangeBinding A BE) :
    NvFaithfulE2E S W FinalVerify BE.Any := by
  classical
  intro s π hv
  by_cases hBad : BE.Any
  · exact .inl hBad
  rcases wrapOK_agg Wr W FinalVerify BE hNvW extW pubW hExW s π hv with hb | ⟨st, p, hacc, -, hi, hf⟩
  · exact .inl hb
  obtain ⟨segs, hs, hc⟩ :=
    leaves_of_acc_agg A BE hNv hEx hLeaf hR hBad (A.level p + 1) st p (Nat.lt_succ_self _) hacc
  exact .inr ⟨⟨segs, st.sa, st.se⟩, ⟨hs, hc⟩, hi, hf⟩

/-- **The E2E statement from the pinned aggregation and wrap programs**: `e2e_sound` with
obligation 1 discharged by `nvFaithfulE2E_of_agg`; `Bad` is the backend's bad-event union. -/
theorem e2e_sound_of_agg {S : SegSystem} [DecidableEq S.Bnd] (A : AggNode S)
    (Wr : AggWrap A) (W : WrapCheck S) {Proof : Type} (FinalVerify : PublicStmt → Proof → Bool)
    (BE : BadEvents)
    (hNv : NvFaithful A.Pin A.D (aggNodeV (Params := A.Params) A.Acc A.rdigest))
    (hNvW : NvFaithful Wr.PinW Wr.DW (aggWrapV (Params := Wr.ParamsW) A.Acc Wr.ctxOf W.InitOK W.FinalOK))
    (hEx : ExtractWG A BE) (extW : Proof → Trace Fp) (pubW : Proof → List Fp)
    (hExW : ExtractW Wr extW pubW FinalVerify BE)
    (hLeaf : LeafHolds A) (hR : RangeBinding A BE)
    (ob1b : WrapFinalFaithful S W) (ob2 : SegSound S BE.Any) (ob4 : WitnessExtraction S W BE.Any)
    (s : PublicStmt) (π : Proof) (hv : FinalVerify s π = true) : E2EStmt s ∨ BE.Any :=
  e2e_sound S W FinalVerify BE.Any
    (nvFaithfulE2E_of_agg A Wr W FinalVerify BE hNv hNvW hEx extW pubW hExW hLeaf hR) ob1b ob2 ob4 s π hv

/-! ## Non-vacuity of the node program -/

/-- The node program accepts two chaining children and rejects them swapped when they do not
chain back (here: two boundaries `0 → 1 → 2` over `Nat`). -/
example : (aggNodeV (Params := Unit) (fun (_ : Stmt Nat) (_ : Unit) => True) id).accepts
    ⟨0, 0, 2, 0, 2⟩ [(⟨0, 0, 1, 0, 1⟩, ()), (⟨0, 1, 2, 1, 2⟩, ())] () PUnit.unit :=
  ⟨by decide, by simp, ⟨0, 0, 2, 0, 2⟩, rfl, rfl⟩

example : ¬ (aggNodeV (Params := Unit) (fun (_ : Stmt Nat) (_ : Unit) => True) id).accepts
    ⟨0, 1, 1, 1, 1⟩ [(⟨0, 1, 2, 1, 2⟩, ()), (⟨0, 0, 1, 0, 1⟩, ())] () PUnit.unit := by
  rintro ⟨-, -, out, h, -⟩
  have hn : compose ([(⟨0, 1, 2, 1, 2⟩, ()), (⟨0, 0, 1, 0, 1⟩, ())].map Prod.fst :
    List (Stmt Nat)) = none := rfl
  rw [hn] at h
  cases h

#print axioms compose_chain
#print axioms nodeOK_agg
#print axioms wrapOK_agg
#print axioms leaves_of_acc_agg
#print axioms nvFaithfulE2E_of_agg
#print axioms e2e_sound_of_agg

end ZkFormal.PQ.E2EAgg
