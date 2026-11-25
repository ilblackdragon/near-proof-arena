import ZkFormal.PQ.E2EHold
import NearSpecV3.E2E.TreeM8

/-!
# ZkFormal.PQ.E2ETree8 — obligation 1 for the M8 heterogeneous tree, from the node and wrap programs

Lane E (E2E M11i, item 2), 2026-11-21. `NearSpecV3.E2E.TreeM8` states the M8 tree's E2E theorem
(`e2e_sound_m8`) against `TreeFaithful`: an accepted final proof yields a chain of satisfied leaves
at `ctx = claimDigest s`, chained by boundary equality, with the wrap's phase checks on the root
boundaries. This file proves `TreeFaithful` from the aggregation layer of `E2EAgg` / `E2EHold`
(the transcription of `build_agg`, with node and wrap faithfulness over a trace predicate `Hold`).

## What changes from M11c–M11g

* **Heterogeneous leaves.** `AggNode.isLeaf π = some t` already allows any leaf key `t`. Here each
  leaf key has a **kind** (`kindOf t : Kind`: one of the five T1 templates or PAD; lane D's leaf
  programs `build_seg_leaf` per template and height class, the normaliser, `PAD_L`), and the
  leaf's statement keeps its **context**: the M8 leaf AIRs `circAirs8` hold a leaf at
  `(ctx, b, b')` when the leaf key's AIR holds at public values decoding to a statement with
  context `ctx` and boundaries `b`, `b'` (decoded by `cx` and `lb` from the statement cells).
* **The context is carried down the tree** (`compose_ctx`): `RangeStmt::compose` asserts
  `ctx_i = ctx_0`, so every leaf below an accepted root has the root's context. The M11c chain
  (`leaves_of_acc_aggH`) dropped it; the INIT and FINAL obligations need it.
* **The M8 wrap**: `wrap8C` checks the root statement's context against the public statement
  (`ctxOf`, with `cx (ctxOf s) = claimDigest s`: V_d recomputes `D_wrap(ctx)` from `S`), the start
  phase `init` (0) and the end phase `done`/`doneG` (4/5) — the phase codes of `View.split`, which
  the leaves expose as `s = [phase, h(B)]` (lane D's D-5 placeholder used 1/2).

## Proved (standard axioms only)

* `compose_ctx`: the children of a composed statement all have its context.
* `leaves_of_acc_tree8`: every accepted proof unfolds to a chain of `circAirs8` leaves at the
  decoded context of its statement, from its decoded start to its decoded end boundary, unless a
  bad event occurs.
* **`treeFaithful_of_aggH`**: `TreeFaithful (circAirs8 …)` from node / wrap faithfulness over
  `Hold` / `HoldW`, the extractors (`ExtractWGH`, `ExtractWH`) and range binding.
* **`e2e_sound_of_tree8`**: composed with `e2e_sound_m8`: the E2E statement from the tree layer
  and the per-template obligations `TmplSound8` / `PadSound8` over `circAirs8` (one per lane).
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.PQ.E2ETree8

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.Nv ZkFormal.PQ.E2EBridge ZkFormal.PQ.E2EAgg
open ZkFormal.PQ.E2EHold
open ZkFormal.PQ.Aggregation.Stmt
open NearSpecV3.E2E NearSpecV3.E2E.M8 NearSpecV3.E2E.Bnd

/-! ## The context is carried by `compose` -/

theorem composeFrom_ctx {α : Type} [DecidableEq α] :
    ∀ (l : List (Stmt α)) (acc out : Stmt α), composeFrom acc l = some out →
      out.ctx = acc.ctx ∧ ∀ t ∈ l, t.ctx = acc.ctx
  | [], acc, out, h => by
    simp only [composeFrom, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ h => absurd h (by simp)⟩
  | t :: rest, acc, out, h => by
    simp only [composeFrom] at h
    obtain ⟨c, hc, hrest⟩ := Option.bind_eq_some_iff.mp h
    by_cases hch : Chains acc t
    · rw [compose₂_eq_some hch, Option.some.injEq] at hc
      subst hc
      obtain ⟨h1, h2⟩ := composeFrom_ctx rest _ out hrest
      refine ⟨h1, fun u hu => ?_⟩
      rcases List.mem_cons.1 hu with rfl | hu
      · exact hch.1
      · exact h2 u hu
    · rw [compose₂_eq_none hch] at hc
      cases hc

/-- **The children of a composed statement all carry its context** (`ctx_i = ctx_0`). -/
theorem compose_ctx {α P : Type} [DecidableEq α] (kids : List (Stmt α × P)) (out : Stmt α)
    (h : compose (kids.map Prod.fst) = some out) : ∀ c ∈ kids, c.1.ctx = out.ctx := by
  cases kids with
  | nil => simp [compose] at h
  | cons s rest =>
    simp only [List.map_cons, compose] at h
    obtain ⟨h1, h2⟩ := composeFrom_ctx _ s.1 out h
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h1.symm
    · exact (h2 c.1 (List.mem_map.2 ⟨c, hc, rfl⟩)).trans h1.symm

/-! ## The circuit's M8 leaf AIRs -/

section Tree

variable {S : SegSystem} [DecidableEq S.Bnd] (A : AggNode S)
  (kindOf : S.Template → Kind) (cx : S.Bnd → NearSpec.Bytes) (lb : S.Bnd → LB)

/-- **The M8 leaf AIRs of the circuit**: a leaf of kind `k` at `(ctx, b, b')` is a leaf key `t` of
kind `k` whose AIR holds at public values decoding to a statement with context `ctx` and
boundaries `b`, `b'`. -/
def circAirs8 : Airs8 where
  Tr _ := S.Template × List Fp × Trace Fp
  Holds k ctx b b' x := kindOf x.1 = k ∧ HoldsLogUp (A.segAir x.1) x.2.1 x.2.2 ∧
    cx (A.segStmt x.2.1).ctx = ctx ∧ lb (A.segStmt x.2.1).sa = b ∧ lb (A.segStmt x.2.1).se = b'

/-- A valid leaf chain at `ctx` from `b` to `b'`. -/
def LChain (ctx : NearSpec.Bytes) (b b' : LB) : Prop :=
  ∃ ls : List (Leaf (circAirs8 A kindOf cx lb)),
    (∀ x ∈ ls, (circAirs8 A kindOf cx lb).Holds x.1 ctx x.2.1 x.2.2.1 x.2.2.2) ∧
      BndChained b (ls.map fun x => (x.2.1, x.2.2.1)) b'

variable {A kindOf cx lb}

theorem lchain_append {ctx : NearSpec.Bytes} {a b c : LB} (h1 : LChain A kindOf cx lb ctx a b)
    (h2 : LChain A kindOf cx lb ctx b c) : LChain A kindOf cx lb ctx a c := by
  obtain ⟨s1, hs1, hc1⟩ := h1
  obtain ⟨s2, hs2, hc2⟩ := h2
  refine ⟨s1 ++ s2, fun x hx => ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact hs1 x hx
    · exact hs2 x hx
  · induction s1 generalizing a with
    | nil => cases hc1; simpa using hc2
    | cons y ys ih =>
      obtain ⟨h1, h2⟩ := hc1
      exact ⟨h1, ih (fun x hx => hs1 x (List.mem_cons_of_mem _ hx)) h2⟩

theorem lchain_kids {ctx : NearSpec.Bytes} {P : Type} :
    ∀ (kids : List (S.Bnd × S.Bnd × P)) (a b : S.Bnd),
      (∀ c ∈ kids, LChain A kindOf cx lb ctx (lb c.1) (lb c.2.1)) →
      BndChained a (kids.map fun c => (c.1, c.2.1)) b → LChain A kindOf cx lb ctx (lb a) (lb b)
  | [], a, b, _, h => by cases h; exact ⟨[], by simp, rfl⟩
  | c :: rest, a, b, hk, ⟨h1, h2⟩ => by
    subst h1
    exact lchain_append (hk c (by simp))
      (lchain_kids rest c.2.1 b (fun x hx => hk x (by simp [hx])) h2)

variable (A kindOf cx lb)

/-- **Every accepted proof unfolds to a chain of M8 leaves at its statement's context**, unless a
bad event occurs. -/
theorem leaves_of_acc_tree8 (Hold : List Fp → Trace Fp → Prop) (BE : BadEvents)
    (hNv : NvFaithfulH Hold A.D (aggNodeV (Params := A.Params) A.Acc A.rdigest))
    (hEx : ExtractWGH A Hold BE) (hR : RangeBinding A BE) (hBad : ¬BE.Any) :
    ∀ (n : Nat) (st : Stmt S.Bnd) (π : A.Proof), A.level π < n → A.Acc st π →
      LChain A kindOf cx lb (cx st.ctx) (lb st.sa) (lb st.se)
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, st, π, hn, hacc => by
    rcases hEx st π hacc with hb | ⟨k, -, hl, hst⟩ | ⟨-, hl, hst, hlt⟩
    · exact absurd hb hBad
    · refine ⟨[⟨kindOf k, lb st.sa, lb st.se, (k, A.segPub π, A.ext π)⟩], ?_, ⟨rfl, rfl⟩⟩
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact ⟨rfl, hl, by rw [hst], by rw [hst], by rw [hst]⟩
    · obtain ⟨e, he⟩ := hNv (A.ext π) (A.pub π) hl
      obtain ⟨-, hk2, out, hc, hd⟩ := he
      have hkids : ∀ c ∈ A.D.proof (A.ext π), A.Acc c.1 c.2 := hk2
      have hchain := compose_chain _ out hc
      have hctx := compose_ctx _ out hc
      rw [hst] at hd
      rcases hR _ _ hd with hout | hcol
      · subst hout
        exact lchain_kids ((A.D.proof (A.ext π)).map fun c => (c.1.sa, c.1.se, c.2)) _ _
          (fun c hc => by
            obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
            have := leaves_of_acc_tree8 Hold BE hNv hEx hR hBad n c0.1 c0.2
              (by have := hlt c0 hc0; omega) (hkids c0 hc0)
            rw [hctx c0 hc0] at this
            exact this)
          (by simpa [List.map_map, Function.comp_def] using hchain)
      · exact absurd (.inr (.inr (.inr hcol))) hBad

/-- The M8 wrap's checks on the root statement's boundaries: phase `init` at the start, `done` /
`doneG` at the end. -/
def wrap8C : WrapCheck S where
  InitOK _ sa := (lb sa).1 = 0
  FinalOK _ se := DonePh (lb se).1

/-- **Obligation 1 for the M8 tree, from the node and wrap programs.** -/
theorem treeFaithful_of_aggH (Wr : AggWrap A) (hcx : ∀ s, cx (Wr.ctxOf s) = claimDigest s)
    (Hold HoldW : List Fp → Trace Fp → Prop) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (BE : BadEvents)
    (hNv : NvFaithfulH Hold A.D (aggNodeV (Params := A.Params) A.Acc A.rdigest))
    (hNvW : NvFaithfulH HoldW Wr.DW (aggWrapV (Params := Wr.ParamsW) A.Acc Wr.ctxOf
      (wrap8C lb).InitOK (wrap8C lb).FinalOK))
    (hEx : ExtractWGH A Hold BE) (extW : Proof → Trace Fp) (pubW : Proof → List Fp)
    (hExW : ExtractWH Wr HoldW extW pubW FinalVerify BE) (hR : RangeBinding A BE) :
    TreeFaithful (circAirs8 A kindOf cx lb) FinalVerify BE.Any := by
  classical
  intro s π hv
  by_cases hBad : BE.Any
  · exact .inl hBad
  rcases wrapOK_aggH Wr (wrap8C lb) HoldW FinalVerify BE hNvW extW pubW hExW s π hv with
    hb | ⟨st, p, hacc, hc, hi, hf⟩
  · exact .inl hb
  obtain ⟨ls, hs, hch⟩ :=
    leaves_of_acc_tree8 A kindOf cx lb Hold BE hNv hEx hR hBad (A.level p + 1) st p
      (Nat.lt_succ_self _) hacc
  rw [hc, hcx] at hs
  exact .inr ⟨⟨ls, lb st.sa, lb st.se⟩, ⟨hs, hch⟩, hi, hf⟩

/-- **The E2E statement from the M8 tree layer** and the per-template obligations over the
circuit's leaf AIRs (`e2e_sound_m8` with obligation 1 discharged by `treeFaithful_of_aggH`). -/
theorem e2e_sound_of_tree8 (V : ViewImpl) (Wr : AggWrap A)
    (hcx : ∀ s, cx (Wr.ctxOf s) = claimDigest s)
    (Hold HoldW : List Fp → Trace Fp → Prop) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (BE : BadEvents)
    (hNv : NvFaithfulH Hold A.D (aggNodeV (Params := A.Params) A.Acc A.rdigest))
    (hNvW : NvFaithfulH HoldW Wr.DW (aggWrapV (Params := Wr.ParamsW) A.Acc Wr.ctxOf
      (wrap8C lb).InitOK (wrap8C lb).FinalOK))
    (hEx : ExtractWGH A Hold BE) (extW : Proof → Trace Fp) (pubW : Proof → List Fp)
    (hExW : ExtractWH Wr HoldW extW pubW FinalVerify BE) (hR : RangeBinding A BE)
    (hInit : SegSoundInit8 V (circAirs8 A kindOf cx lb) BE.Any)
    (hState : SegSoundState8 V (circAirs8 A kindOf cx lb) BE.Any)
    (hRt : SegSoundRt8 V (circAirs8 A kindOf cx lb) BE.Any)
    (hWasm : SegSoundWasm8 V (circAirs8 A kindOf cx lb) BE.Any)
    (hFinal : SegSoundFinal8 V (circAirs8 A kindOf cx lb) BE.Any)
    (hPad : PadSound8 (circAirs8 A kindOf cx lb) BE.Any)
    (s : PublicStmt) (hwf : s.wf = true) (π : Proof) (hv : FinalVerify s π = true) :
    E2EStmt s ∨ BE.Any ∨ BndCollision V.bnd ∨ Sha384Coll :=
  e2e_sound_m8 V _ FinalVerify BE.Any
    (treeFaithful_of_aggH A kindOf cx lb Wr hcx Hold HoldW FinalVerify BE hNv hNvW hEx extW pubW
      hExW hR)
    hInit hState hRt hWasm hFinal hPad s hwf π hv

end Tree

/-! ## Non-vacuity of the context check -/

/-- Two children with different contexts do not compose (the node rejects a leaf of another
chunk). -/
example : compose ([⟨0, 0, 1, 0, 1⟩, ⟨1, 1, 2, 1, 2⟩] : List (Stmt Nat)) = none := rfl

#print axioms compose_ctx
#print axioms leaves_of_acc_tree8
#print axioms treeFaithful_of_aggH
#print axioms e2e_sound_of_tree8

end ZkFormal.PQ.E2ETree8
