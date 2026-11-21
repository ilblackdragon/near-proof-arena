import ZkFormal.PQ.E2ETree

/-!
# ZkFormal.PQ.E2EHold — the aggregation composition over an arbitrary trace predicate

Lane E (E2E M11g), 2026-11-04. `E2EAgg.lean` (M11c) and `E2ENode.lean` (M11d) state the node and
wrap obligations against `HoldsLogUp Pin.air`, the trace predicate of a `ZkFormal.Air` transcription
(bit-decomposed natural multiplicities with a send flag). M11f found that NvAir's interactions have
**field-valued counts merged across roles** (`NvTape.lean`), which `ZkFormal.Air.Interaction`
cannot express: `HoldsLogUp` over a transcription is not the circuit's predicate.

This file re-derives the composition with the trace predicate as a **parameter** `Hold`:

* `NvFaithfulH Hold D V`, `ExtractWGH`, `ExtractWH`: `NvFaithful`, `ExtractWG`, `ExtractW` with
  `HoldsLogUp Pin.air` replaced by `Hold` (leaf templates keep `HoldsLogUp (segAir k)`: segment
  AIRs are separate keys);
* `leaves_of_acc_aggH`, `wrapOK_aggH`, `nvFaithfulE2E_of_aggH`, `e2e_sound_of_aggH`: the M11c
  proofs, unchanged in structure;
* `NodeExecH`, `nvFaithfulH_node`, `WrapExecH`, `nvFaithfulH_wrap`, `e2e_sound_of_execH`: the M11d
  reduction to the per-trace components, over `Hold`;
* `WrapExecTH` and `wrapT_ofH`: the D-5 wrap (`E2ETree.lean`) over `Hold`.

The old statements are the instance `Hold = HoldsLogUp Pin.air` (`nvFaithfulH_logUp`).
`NvField.lean` supplies the circuit's own predicate (`NvHold`: the four exported tables'
constraints and the field LogUp balance of every bus) and instantiates `Hold` with it.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace ZkFormal.PQ.E2EHold

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.Nv ZkFormal.PQ.E2EBridge ZkFormal.PQ.E2EAgg
open ZkFormal.PQ.E2ENode ZkFormal.PQ.E2ETree
open ZkFormal.PQ.Aggregation.Stmt
open NearSpecV3.E2E

/-- **`NvFaithful` over a trace predicate `Hold`.** -/
def NvFaithfulH (Hold : List Fp → Trace Fp → Prop) {St Proof Params : Type}
    (D : NvDecode St Proof Params) (V : NvVerifier St Proof Params) : Prop :=
  ∀ tr pub, Hold pub tr →
    ∃ e : V.Execution (D.stmt pub) (D.proof tr) (D.params tr),
      V.accepts (D.stmt pub) (D.proof tr) (D.params tr) e

/-- The old statement is the instance `Hold = HoldsLogUp Pin.air`. -/
theorem nvFaithfulH_logUp (Pin : NvPinned) {St Proof Params : Type} (D : NvDecode St Proof Params)
    (V : NvVerifier St Proof Params) :
    NvFaithfulH (fun pub tr => HoldsLogUp Pin.air pub tr) D V ↔ NvFaithful Pin D V := Iff.rfl

/-- **The extractor over `Hold`** for the node key (`ExtractWG` with `HoldsLogUp A.Pin.air`
replaced by `Hold`). -/
def ExtractWGH {S : SegSystem} (A : AggNode S) (Hold : List Fp → Trace Fp → Prop)
    (BE : BadEvents) : Prop :=
  ∀ st π, A.Acc st π → BE.Any ∨
    (∃ k, A.isLeaf π = some k ∧ HoldsLogUp (A.segAir k) (A.segPub π) (A.ext π) ∧
      A.segStmt (A.segPub π) = st) ∨
    (A.isLeaf π = none ∧ Hold (A.pub π) (A.ext π) ∧
      A.D.stmt (A.pub π) = A.rdigest st ∧
      ∀ c ∈ A.D.proof (A.ext π), A.level c.2 < A.level π)

/-- **Every accepted proof unfolds to satisfied leaves**, over `Hold`. -/
theorem leaves_of_acc_aggH {S : SegSystem} [DecidableEq S.Bnd] (A : AggNode S)
    (Hold : List Fp → Trace Fp → Prop) (BE : BadEvents)
    (hNv : NvFaithfulH Hold A.D (aggNodeV (Params := A.Params) A.Acc A.rdigest))
    (hEx : ExtractWGH A Hold BE) (hLeaf : LeafHolds A) (hR : RangeBinding A BE)
    (hBad : ¬BE.Any) :
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
      obtain ⟨hkids, out, hd, hchain⟩ := nodeOK_agg A.Acc A.rdigest _ _ _ e he
      rw [hst] at hd
      rcases hR _ _ hd with hout | hc
      · subst hout
        exact leaves_of_kids ((A.D.proof (A.ext π)).map fun c => (c.1.sa, c.1.se, c.2)) _ _
          (fun c hc => by
            obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
            exact leaves_of_acc_aggH A Hold BE hNv hEx hLeaf hR hBad n c0.1 c0.2
              (by have := hlt c0 hc0; omega) (hkids c0 hc0))
          (by simpa [List.map_map, Function.comp_def] using hchain)
      · exact absurd (.inr (.inr (.inr hc))) hBad

/-- **The wrap's extraction over `HoldW`.** -/
def ExtractWH {S : SegSystem} {A : AggNode S} (Wr : AggWrap A) (HoldW : List Fp → Trace Fp → Prop)
    {Proof : Type} (extW : Proof → Trace Fp) (pubW : Proof → List Fp)
    (FinalVerify : PublicStmt → Proof → Bool) (BE : BadEvents) : Prop :=
  ∀ s π, FinalVerify s π = true → BE.Any ∨ (HoldW (pubW π) (extW π) ∧ Wr.DW.stmt (pubW π) = s)

theorem wrapOK_aggH {S : SegSystem} {A : AggNode S} (Wr : AggWrap A) (W : WrapCheck S)
    (HoldW : List Fp → Trace Fp → Prop) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (BE : BadEvents)
    (hNvW : NvFaithfulH HoldW Wr.DW
      (aggWrapV (Params := Wr.ParamsW) A.Acc Wr.ctxOf W.InitOK W.FinalOK))
    (extW : Proof → Trace Fp) (pubW : Proof → List Fp)
    (hExW : ExtractWH Wr HoldW extW pubW FinalVerify BE) :
    ∀ s π, FinalVerify s π = true → BE.Any ∨
      ∃ st p, A.Acc st p ∧ st.ctx = Wr.ctxOf s ∧ W.InitOK s st.sa ∧ W.FinalOK s st.se := by
  intro s π hv
  rcases hExW s π hv with hb | ⟨hl, hs⟩
  · exact .inl hb
  obtain ⟨e, he⟩ := hNvW _ _ hl
  rw [hs] at he
  exact .inr ⟨_, _, he⟩

/-- **E2E obligation 1 over `Hold` / `HoldW`.** -/
theorem nvFaithfulE2E_of_aggH {S : SegSystem} [DecidableEq S.Bnd] (A : AggNode S)
    (Wr : AggWrap A) (W : WrapCheck S) (Hold HoldW : List Fp → Trace Fp → Prop) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (BE : BadEvents)
    (hNv : NvFaithfulH Hold A.D (aggNodeV (Params := A.Params) A.Acc A.rdigest))
    (hNvW : NvFaithfulH HoldW Wr.DW
      (aggWrapV (Params := Wr.ParamsW) A.Acc Wr.ctxOf W.InitOK W.FinalOK))
    (hEx : ExtractWGH A Hold BE) (extW : Proof → Trace Fp) (pubW : Proof → List Fp)
    (hExW : ExtractWH Wr HoldW extW pubW FinalVerify BE)
    (hLeaf : LeafHolds A) (hR : RangeBinding A BE) :
    NvFaithfulE2E S W FinalVerify BE.Any := by
  classical
  intro s π hv
  by_cases hBad : BE.Any
  · exact .inl hBad
  rcases wrapOK_aggH Wr W HoldW FinalVerify BE hNvW extW pubW hExW s π hv with
    hb | ⟨st, p, hacc, -, hi, hf⟩
  · exact .inl hb
  obtain ⟨segs, hs, hc⟩ :=
    leaves_of_acc_aggH A Hold BE hNv hEx hLeaf hR hBad (A.level p + 1) st p (Nat.lt_succ_self _)
      hacc
  exact .inr ⟨⟨segs, st.sa, st.se⟩, ⟨hs, hc⟩, hi, hf⟩

/-- **The E2E statement over `Hold` / `HoldW`.** -/
theorem e2e_sound_of_aggH {S : SegSystem} [DecidableEq S.Bnd] (A : AggNode S)
    (Wr : AggWrap A) (W : WrapCheck S) (Hold HoldW : List Fp → Trace Fp → Prop) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (BE : BadEvents)
    (hNv : NvFaithfulH Hold A.D (aggNodeV (Params := A.Params) A.Acc A.rdigest))
    (hNvW : NvFaithfulH HoldW Wr.DW
      (aggWrapV (Params := Wr.ParamsW) A.Acc Wr.ctxOf W.InitOK W.FinalOK))
    (hEx : ExtractWGH A Hold BE) (extW : Proof → Trace Fp) (pubW : Proof → List Fp)
    (hExW : ExtractWH Wr HoldW extW pubW FinalVerify BE)
    (hLeaf : LeafHolds A) (hR : RangeBinding A BE)
    (ob1b : WrapFinalFaithful S W) (ob2 : SegSound S BE.Any) (ob4 : WitnessExtraction S W BE.Any)
    (s : PublicStmt) (π : Proof) (hv : FinalVerify s π = true) : E2EStmt s ∨ BE.Any :=
  e2e_sound S W FinalVerify BE.Any
    (nvFaithfulE2E_of_aggH A Wr W Hold HoldW FinalVerify BE hNv hNvW hEx extW pubW hExW hLeaf hR)
    ob1b ob2 ob4 s π hv

/-! ## The node and wrap programs over `Hold` (M11d's reduction) -/

section Node

variable {K : NodeKey} {α Dg Proof : Type} (enc : List Fp → α) (rdigest : Stmt α → Dg)
  (InnerAcc : Proof → List Fp → Prop) (pvDig : List Fp → Dg) (segStmt : List Fp → Stmt α)

/-- **The AIR executes the node program**, over `Hold`. -/
def NodeExecH (Hold : List Fp → Trace Fp → Prop) (R : Trace Fp → NodeRead K Dg Proof)
    (pubDig : List Fp → Dg) : Prop :=
  ∀ tr pub, Hold pub tr →
    NodeSha enc rdigest (R tr) ∧ NodeInner InnerAcc (R tr) ∧ NodeTape pubDig (R tr) pub ∧
      NodeAsserts enc pvDig segStmt (R tr)

theorem nvFaithfulH_node [DecidableEq α] {Params : Type} (Hold : List Fp → Trace Fp → Prop)
    (Acc : Stmt α → Proof → Prop) (hAcc : AccNative rdigest InnerAcc pvDig segStmt Acc)
    (R : Trace Fp → NodeRead K Dg Proof) (pubDig : List Fp → Dg) (par : Trace Fp → Params)
    (hX : NodeExecH enc rdigest InnerAcc pvDig segStmt Hold R pubDig) :
    NvFaithfulH Hold (nodeDecode enc R pubDig par) (aggNodeV Acc rdigest) := by
  intro tr pub h
  obtain ⟨hS, hI, hT, hA⟩ := hX tr pub h
  exact ⟨PUnit.unit, node_composition enc rdigest InnerAcc pvDig segStmt Acc hAcc pubDig (R tr)
    pub (par tr) hS hI hT hA⟩

/-- **The wrap program over `Hold`** (M11d's `WrapExec`). -/
def WrapExecH {nCtx nState : Nat} (HoldW : List Fp → Trace Fp → Prop) (ctxOf : PublicStmt → α)
    (InitOK FinalOK : PublicStmt → α → Prop) (R : Trace Fp → WrapRead nCtx nState Dg Proof)
    (pubS : List Fp → PublicStmt) : Prop :=
  ∀ tr pub, HoldW pub tr →
    WrapComp enc rdigest InnerAcc pvDig ctxOf InitOK FinalOK (R tr) (pubS pub)

theorem nvFaithfulH_wrap {nCtx nState : Nat} {ParamsW : Type} (HoldW : List Fp → Trace Fp → Prop)
    (Acc : Stmt α → Proof → Prop) (hAcc : AccNative rdigest InnerAcc pvDig segStmt Acc)
    (ctxOf : PublicStmt → α) (InitOK FinalOK : PublicStmt → α → Prop)
    (R : Trace Fp → WrapRead nCtx nState Dg Proof) (pubS : List Fp → PublicStmt)
    (par : Trace Fp → ParamsW)
    (hX : WrapExecH enc rdigest InnerAcc pvDig HoldW ctxOf InitOK FinalOK R pubS) :
    NvFaithfulH HoldW (wrapDecode enc R pubS par) (aggWrapV Acc ctxOf InitOK FinalOK) :=
  fun tr pub h => ⟨PUnit.unit, wrap_composition enc rdigest InnerAcc pvDig segStmt Acc hAcc ctxOf
    InitOK FinalOK (R tr) (pubS pub) (par tr) (hX tr pub h)⟩

end Node

/-- **`e2e_sound` from the AIR-execution obligations, over `Hold`** (M11d's `e2e_sound_of_exec`
with the circuit's trace predicate a parameter). -/
theorem e2e_sound_of_execH {S0 : SegSystem} [DecidableEq S0.Bnd] (segAir : S0.Template → Air)
    (segStmt : List Fp → Stmt S0.Bnd) (A : AggNode (circSeg S0 segAir segStmt))
    (hsegAir : ∀ k, A.segAir k = segAir k) (hsegStmt : ∀ p, A.segStmt p = segStmt p)
    (Wr : AggWrap A) (W : WrapCheck (circSeg S0 segAir segStmt)) {Proof : Type}
    (FinalVerify : PublicStmt → Proof → Bool) (BE : BadEvents)
    (Hold HoldW : List Fp → Trace Fp → Prop)
    {K : NodeKey} (enc : List Fp → S0.Bnd) (InnerAcc : A.Proof → List Fp → Prop)
    (pvDig : List Fp → A.Dg) (hAcc : AccNative A.rdigest InnerAcc pvDig segStmt A.Acc)
    (R : Trace Fp → NodeRead K A.Dg A.Proof) (pubDig : List Fp → A.Dg)
    (par : Trace Fp → A.Params) (hD : A.D = nodeDecode enc R pubDig par)
    (hX : NodeExecH enc A.rdigest InnerAcc pvDig segStmt Hold R pubDig)
    {nCtx nState : Nat} (RW : Trace Fp → WrapRead nCtx nState A.Dg A.Proof)
    (pubS : List Fp → PublicStmt) (parW : Trace Fp → Wr.ParamsW)
    (hDW : Wr.DW = wrapDecode enc RW pubS parW)
    (hXW : WrapExecH enc A.rdigest InnerAcc pvDig HoldW Wr.ctxOf W.InitOK W.FinalOK RW pubS)
    (H : List Nat → A.Dg) (encB : S0.Bnd → List Nat) (hinj : ∀ x y, encB x = encB y → x = y)
    (hR : ∀ st, A.rdigest st = H (rmsg encB st)) (hBE : HColl H → BE.rangeColl)
    (hEx : ExtractWGH A Hold BE) (extW : Proof → Trace Fp) (pubW : Proof → List Fp)
    (hExW : ExtractWH Wr HoldW extW pubW FinalVerify BE)
    (ob1b : WrapFinalFaithful (circSeg S0 segAir segStmt) W)
    (ob2 : SegSound (circSeg S0 segAir segStmt) BE.Any)
    (ob4 : WitnessExtraction (circSeg S0 segAir segStmt) W BE.Any)
    (s : PublicStmt) (π : Proof) (hv : FinalVerify s π = true) : E2EStmt s ∨ BE.Any := by
  letI : DecidableEq (circSeg S0 segAir segStmt).Bnd := ‹DecidableEq S0.Bnd›
  have hNv : NvFaithfulH Hold A.D (aggNodeV (Params := A.Params) A.Acc A.rdigest) := by
    rw [hD]
    exact nvFaithfulH_node enc A.rdigest InnerAcc pvDig segStmt Hold A.Acc hAcc R pubDig par hX
  have hNvW : NvFaithfulH HoldW Wr.DW
      (aggWrapV (Params := Wr.ParamsW) A.Acc Wr.ctxOf W.InitOK W.FinalOK) := by
    rw [hDW]
    exact nvFaithfulH_wrap enc A.rdigest InnerAcc pvDig segStmt HoldW A.Acc hAcc Wr.ctxOf
      W.InitOK W.FinalOK RW pubS parW hXW
  exact e2e_sound_of_aggH A Wr W Hold HoldW FinalVerify BE hNv hNvW hEx extW pubW hExW
    (leafHolds_circ S0 segAir segStmt A hsegAir hsegStmt)
    (rangeBinding_of A BE H encB hinj hR hBE) ob1b ob2 ob4 s π hv

/-! ## The D-5 wrap (`E2ETree.lean`) over `HoldW` -/

/-- **The AIR executes `build_wrap`**, over `HoldW`. -/
def WrapExecTH {m : Nat} {Dg DgW Proof : Type} (HoldW : List Fp → Trace Fp → Prop)
    (rdigest : Stmt (List Fp) → Dg) (wdigest : List Fp → DgW)
    (InnerAcc : Proof → List Fp → Prop) (pvDig : List Fp → Dg) (rootLevel : Fp)
    (cNode : Fin m → Fp) (pubDig : List Fp → DgW) (R : Trace Fp → WrapReadT m Dg DgW Proof) :
    Prop :=
  ∀ tr pub, HoldW pub tr →
    WrapCompT rdigest wdigest InnerAcc pvDig rootLevel cNode pubDig (R tr) pub

/-- **The D-5 wrap's faithfulness over `HoldW`**: on every trace satisfying the circuit's
predicate whose public digest passes V_d's check against the claimed statement `s`, the native
wrap program accepts the decoded root, or the `D_wrap` hash collides. -/
theorem wrapT_ofH {m : Nat} {Dg DgW Proof ParamsW : Type} (HoldW : List Fp → Trace Fp → Prop)
    (rdigest : Stmt (List Fp) → Dg) (wdigest : List Fp → DgW)
    (InnerAcc : Proof → List Fp → Prop) (pvDig : List Fp → Dg)
    (segStmt : List Fp → Stmt (List Fp)) (Acc : Stmt (List Fp) → Proof → Prop)
    (hAcc : AccNative rdigest InnerAcc pvDig segStmt Acc) (rootLevel : Fp) (cNode : Fin m → Fp)
    (pubDig : List Fp → DgW) (ctxOf : PublicStmt → List Fp) (clsOf : PublicStmt → Fp)
    (hctx : ∀ s, (ctxOf s).length = 18) (R : Trace Fp → WrapReadT m Dg DgW Proof)
    (par : Trace Fp → ParamsW)
    (hX : WrapExecTH HoldW rdigest wdigest InnerAcc pvDig rootLevel cNode pubDig R)
    (tr : Trace Fp) (pub : List Fp) (s : PublicStmt) (h : HoldW pub tr)
    (hV : pubDig pub = wdigest (wmsg (ctxOf s) (clsOf s))) :
    (aggWrapV (Params := ParamsW) Acc ctxOf
        (fun s sa => sa.head? = some phInit ∧ sa[1]? = some (clsOf s))
        (fun _ se => se.head? = some phDone)).accepts s ((R tr).cell.stmt id, (R tr).proof)
          (par tr) PUnit.unit ∨
      WColl wdigest :=
  wrapT_composition rdigest wdigest InnerAcc pvDig segStmt Acc hAcc rootLevel cNode pubDig ctxOf
    clsOf hctx (R tr) pub s (par tr) (hX tr pub h) hV

#print axioms nvFaithfulH_logUp
#print axioms leaves_of_acc_aggH
#print axioms nvFaithfulE2E_of_aggH
#print axioms e2e_sound_of_aggH
#print axioms nvFaithfulH_node
#print axioms nvFaithfulH_wrap
#print axioms e2e_sound_of_execH
#print axioms wrapT_ofH

end ZkFormal.PQ.E2EHold
