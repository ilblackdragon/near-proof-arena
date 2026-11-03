import ZkFormal.PQ.NvFaithful
import NearSpecV3.E2E.Statement

/-!
# ZkFormal.PQ.E2EBridge — E2E obligation 1 from `NvFaithful`

Lane E (E2E M11b), 2026-11-03. `NearSpecV3.E2E.e2e_sound` (in the v3 package) takes obligation 1
as the hypothesis `NvFaithfulE2E S W FinalVerify Bad`: an accepted final proof yields a chain of
satisfied segment instances whose root boundaries pass the wrap checks. This file derives it from
`ZkFormal.PQ.Nv.NvFaithful` for the aggregation node circuit plus three named interface facts.

**Why here.** `ZkFormal` already requires `NearSpecV3` (`lakefile.toml`), so the link can only
live on this side: the v3 package cannot import `ZkFormal` without a cycle. Nothing in the v3
package changes.

**The hypotheses** (`AggIface`, `nvFaithfulE2E_of_nv`):
* `hNv : NvFaithful Pin D V` — the lane `pq-nv-faithful` obligation for the node circuit, whose
  native verifier checks a list of children `(B_in, B_out, proof)`;
* `NodeOK` — the node verifier's acceptance means every child proof is accepted for its
  statement, and the children's boundaries chain from the node's `B_in` to its `B_out`
  (plan §3.4);
* `Extract` — knowledge soundness of the native verifier (the QROM bound): an accepted proof is,
  unless `Bad`, a leaf whose rows satisfy its template (`Holds`), or a node proof with a trace
  satisfying the node AIR whose public statement is the proof's statement, with strictly lower
  children;
* `WrapOK` — the final verifier's acceptance means an accepted root proof whose boundaries pass
  the wrap checks (`InitOK`, `FinalOK`), or `Bad`.

`nvFaithfulE2E_of_nv` then proves `NvFaithfulE2E` by induction on the proof height. With
`e2e_sound` this closes the E2E soundness statement from `NvFaithful`, the interface facts,
obligation 1b, 2 and 4.
-/

namespace ZkFormal.PQ.E2EBridge

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.Nv
open NearSpecV3.E2E

/-- The aggregation interface over a segment system `S`. -/
structure AggIface (S : SegSystem) where
  Proof : Type
  Params : Type
  height : Proof → Nat
  /-- Native acceptance of a proof for the statement `(B_in, B_out)`. -/
  Acc : S.Bnd × S.Bnd → Proof → Prop
  /-- The node circuit (NvAir as an interface). -/
  Pin : NvPinned
  D : NvDecode (S.Bnd × S.Bnd) (List (S.Bnd × S.Bnd × Proof)) Params
  V : NvVerifier (S.Bnd × S.Bnd) (List (S.Bnd × S.Bnd × Proof)) Params

/-- **NodeOK**: an accepting node verification accepts every child for its statement, and the
children's boundaries chain from the node's `B_in` to its `B_out`. -/
def NodeOK {S : SegSystem} (A : AggIface S) : Prop :=
  ∀ st kids q (e : A.V.Execution st kids q), A.V.accepts st kids q e →
    (∀ c ∈ kids, A.Acc (c.1, c.2.1) c.2.2) ∧ BndChained st.1 (kids.map fun c => (c.1, c.2.1)) st.2

/-- **Extraction** (knowledge soundness, QROM): an accepted proof is a satisfied leaf, or a node
trace satisfying the node AIR with that statement and lower children, or `Bad`. -/
def Extract {S : SegSystem} (A : AggIface S) (Bad : Prop) : Prop :=
  ∀ st π, A.Acc st π → Bad ∨
    (∃ k tr, S.Holds k st.1 st.2 tr) ∨
    (∃ (tr : Trace Fp) (pub : List Fp), HoldsLogUp A.Pin.air pub tr ∧ A.D.stmt pub = st ∧
      ∀ c ∈ A.D.proof tr, A.height c.2.2 < A.height π)

/-- **Wrap**: final acceptance is an accepted root whose boundaries pass the wrap checks. -/
def WrapOK {S : SegSystem} (A : AggIface S) (W : WrapCheck S) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (Bad : Prop) : Prop :=
  ∀ s π, FinalVerify s π = true → Bad ∨
    ∃ b0 bN p, A.Acc (b0, bN) p ∧ W.InitOK s b0 ∧ W.FinalOK s bN

/-- Satisfied segment instances chaining from `b` to `b'`. -/
def Leaves (S : SegSystem) (b b' : S.Bnd) : Prop :=
  ∃ segs : List (S.Template × S.Bnd × S.Bnd × S.Trace),
    (∀ x ∈ segs, S.Holds x.1 x.2.1 x.2.2.1 x.2.2.2) ∧
      BndChained b (segs.map fun x => (x.2.1, x.2.2.1)) b'

theorem leaves_append {S : SegSystem} {a b c : S.Bnd} (h1 : Leaves S a b) (h2 : Leaves S b c) :
    Leaves S a c := by
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
      exact ⟨h1, ih (fun x hx => hs1 x (by simp [hx])) h2⟩

theorem leaves_of_kids {S : SegSystem} {P : Type} :
    ∀ (kids : List (S.Bnd × S.Bnd × P)) (a b : S.Bnd),
      (∀ c ∈ kids, Leaves S c.1 c.2.1) →
      BndChained a (kids.map fun c => (c.1, c.2.1)) b → Leaves S a b
  | [], a, b, _, h => by cases h; exact ⟨[], by simp, rfl⟩
  | c :: rest, a, b, hk, ⟨h1, h2⟩ => by
    subst h1
    exact leaves_append (hk c (by simp))
      (leaves_of_kids rest c.2.1 b (fun x hx => hk x (by simp [hx])) h2)

/-- Every accepted proof unfolds to satisfied leaves chaining across its statement, or `Bad`. -/
theorem leaves_of_acc {S : SegSystem} (A : AggIface S) (Bad : Prop)
    (hNv : NvFaithful A.Pin A.D A.V) (hNode : NodeOK A) (hEx : Extract A Bad) (hBad : ¬Bad) :
    ∀ (n : Nat) (st : S.Bnd × S.Bnd) (π : A.Proof), A.height π < n → A.Acc st π →
      Leaves S st.1 st.2
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, st, π, hn, hacc => by
    rcases hEx st π hacc with hb | ⟨k, tr, hh⟩ | ⟨tr, pub, hl, hst, hlt⟩
    · exact absurd hb hBad
    · exact ⟨[(k, st.1, st.2, tr)], by simpa using hh, ⟨rfl, rfl⟩⟩
    · obtain ⟨e, he⟩ := hNv tr pub hl
      obtain ⟨hkids, hchain⟩ := hNode _ _ _ e he
      rw [hst] at hchain
      exact leaves_of_kids _ _ _
        (fun c hc => leaves_of_acc A Bad hNv hNode hEx hBad n (c.1, c.2.1) c.2.2
          (by have := hlt c hc; omega) (hkids c hc)) hchain

/-- **E2E obligation 1 from `NvFaithful`.** -/
theorem nvFaithfulE2E_of_nv {S : SegSystem} (A : AggIface S) (W : WrapCheck S) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (Bad : Prop)
    (hNv : NvFaithful A.Pin A.D A.V) (hNode : NodeOK A) (hEx : Extract A Bad)
    (hWrap : WrapOK A W FinalVerify Bad) :
    NvFaithfulE2E S W FinalVerify Bad := by
  classical
  intro s π hv
  by_cases hBad : Bad
  · exact .inl hBad
  rcases hWrap s π hv with hb | ⟨b0, bN, p, hacc, hi, hf⟩
  · exact .inl hb
  obtain ⟨segs, hs, hc⟩ :=
    leaves_of_acc A Bad hNv hNode hEx hBad (A.height p + 1) (b0, bN) p (Nat.lt_succ_self _) hacc
  exact .inr ⟨⟨segs, b0, bN⟩, ⟨hs, hc⟩, hi, hf⟩

/-- **The E2E statement from `NvFaithful`**: `e2e_sound` with obligation 1 discharged by
`nvFaithfulE2E_of_nv`. -/
theorem e2e_sound_of_nv {S : SegSystem} (A : AggIface S) (W : WrapCheck S) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (Bad : Prop)
    (hNv : NvFaithful A.Pin A.D A.V) (hNode : NodeOK A) (hEx : Extract A Bad)
    (hWrap : WrapOK A W FinalVerify Bad)
    (ob1b : WrapFinalFaithful S W) (ob2 : SegSound S Bad) (ob4 : WitnessExtraction S W Bad)
    (s : PublicStmt) (π : Proof) (hv : FinalVerify s π = true) : E2EStmt s ∨ Bad :=
  e2e_sound S W FinalVerify Bad (nvFaithfulE2E_of_nv A W FinalVerify Bad hNv hNode hEx hWrap)
    ob1b ob2 ob4 s π hv

#print axioms nvFaithfulE2E_of_nv
#print axioms e2e_sound_of_nv

end ZkFormal.PQ.E2EBridge
