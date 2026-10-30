import NearSpecV3.Successor.TierO3Run
import NearSpecV3.Successor.TierO6

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-!
# W12 / O3 step 6 — driver fields, the shells, and the `Lift`s under the well-formed-layout hypothesis

The global-action drivers differ from the lower ones in five fields: `apply` (the engine, `run_global`),
`decodeWitness` (`decodeWitness_ref`), `receiptShard` and `outgoingRoot` (equal on non-distribution
receipts), and `validateRouting` (passes on non-distribution receipts of a well-formed layout).
`DrvRel` collects those facts; the shells refine under it for a claim whose layouts are well formed
(`LayoutsWF`, the README §9 decision), the layout fact threaded down to `env.ctx.layout` as O7 threads
store authentication.
-/

namespace NearSpecV3.Successor
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Wasm

/-! ## Invariants of the lower witness -/

/-- No distribution receipt in any source-receipt entry. -/
def NDE (e : EntryD2) : Prop := ND e.receipts

def NDW (w : StateWitnessD2) : Prop := ∀ e ∈ w.entries, NDE e

theorem pMany_mem {α : Type} {p : P α} {Q : α → Prop} (hp : ∀ bs a rest, p bs = .ok (a, rest) → Q a) :
    ∀ n bs l rest, pMany p n bs = .ok (l, rest) → ∀ a ∈ l, Q a
  | 0, bs, l, rest, h => by
    simp only [pMany] at h; cases h; intro a ha; cases ha
  | n + 1, bs, l, rest, h => by
    simp only [pMany] at h
    obtain ⟨⟨a, bs1⟩, h1, h⟩ := Codec.ok_bind h
    obtain ⟨⟨as, bs2⟩, h2, h⟩ := Codec.ok_bind h
    cases h
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hp _ _ _ h1
    · exact pMany_mem hp n _ _ _ h2 x hx

theorem pVec_mem {α : Type} {p : P α} {Q : α → Prop} (hp : ∀ bs a rest, p bs = .ok (a, rest) → Q a)
    (wd : String) (bs : Bytes) (l : List α) (rest : Bytes) (h : pVec wd p bs = .ok (l, rest)) : ∀ a ∈ l, Q a := by
  unfold pVec at h
  obtain ⟨⟨n, bs1⟩, _, h⟩ := Codec.ok_bind h
  exact pMany_mem hp n _ _ _ h

theorem pEntryD2_nd (bs : Bytes) (e : EntryD2) (rest : Bytes) (h : pEntryD2 bs = .ok (e, rest)) : NDE e := by
  unfold pEntryD2 at h
  obtain ⟨⟨k, bs1⟩, _, h⟩ := Codec.ok_bind h
  obtain ⟨⟨rs, bs2⟩, h2, h⟩ := Codec.ok_bind h
  obtain ⟨⟨f, bs3⟩, _, h⟩ := Codec.ok_bind h
  obtain ⟨⟨t, bs4⟩, _, h⟩ := Codec.ok_bind h
  obtain ⟨⟨pa, bs5⟩, _, h⟩ := Codec.ok_bind h
  cases h
  exact pVec_mem (fun bs r rest h => Codec.pRcpt_not_distribution bs r rest h) _ _ _ _ h2

theorem decodeStateWitnessD2_nd (bs : Bytes) (w : StateWitnessD2) (h : decodeStateWitnessD2 bs = .ok w) :
    NDW w := by
  unfold decodeStateWitnessD2 at h
  by_cases c1 : lenT bs > MAX_WITNESS
  · rw [if_pos c1] at h; cases h
  rw [if_neg c1] at h; dsimp only at h
  obtain ⟨⟨t, bs1⟩, _, h⟩ := Codec.ok_bind h
  by_cases c2 : (t != 1) = true
  · rw [if_pos c2] at h; cases h
  rw [if_neg c2] at h; dsimp only at h
  obtain ⟨⟨eid, bs2⟩, _, h⟩ := Codec.ok_bind h
  obtain ⟨⟨⟨ib, ci⟩, bs3⟩, _, h⟩ := Codec.ok_bind h
  obtain ⟨⟨main, bs4⟩, _, h⟩ := Codec.ok_bind h
  obtain ⟨⟨entries, bs5⟩, h5, h⟩ := Codec.ok_bind h
  obtain ⟨⟨arh, bs6⟩, _, h⟩ := Codec.ok_bind h
  obtain ⟨⟨txs, bs7⟩, _, h⟩ := Codec.ok_bind h
  obtain ⟨⟨impl, bs8⟩, _, h⟩ := Codec.ok_bind h
  obtain ⟨⟨ntxs, bs9⟩, _, h⟩ := Codec.ok_bind h
  by_cases c3 : (!List.isEmpty bs9) = true
  · rw [if_pos c3] at h; cases h
  rw [if_neg c3] at h
  cases h
  exact pVec_mem pEntryD2_nd _ _ _ _ h5

theorem lookupLastD2_mem (k : Bytes) : ∀ (l : List EntryD2) (e : EntryD2), lookupLastD2 k l = some e → e ∈ l
  | [], _, h => by cases h
  | x :: xs, e, h => by
    unfold lookupLastD2 at h
    split at h
    · rename_i y hy
      cases h
      exact List.mem_cons_of_mem _ (lookupLastD2_mem k xs _ hy)
    · split at h
      · cases h; exact List.mem_cons_self
      · cases h

theorem swapAt_mem {α : Type} (l : List α) (i j : Nat) (x : α) (hx : x ∈ swapAt l i j) : x ∈ l := by
  unfold swapAt at hx
  split at hx
  · rename_i a b ha hb
    rcases List.mem_or_eq_of_mem_set hx with h | rfl
    · rcases List.mem_or_eq_of_mem_set h with h | rfl
      · exact h
      · exact List.mem_of_getElem? hb
    · exact List.mem_of_getElem? ha
  · exact hx

theorem shuffleLoop_mem {α : Type} : ∀ (n : Nat) (l : List α) (r : Rng) (l' : List α) (r' : Rng),
    shuffleLoop n l r = some (l', r') → ∀ x ∈ l', x ∈ l
  | 0, l, r, l', r', h => by simp only [shuffleLoop, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, _⟩ := h; exact fun _ hx => hx
  | n + 1, l, r, l', r', h => by
    unfold shuffleLoop at h
    split at h
    · cases h
    · intro x hx
      exact swapAt_mem _ _ _ _ (shuffleLoop_mem n _ _ _ _ h x hx)

theorem shuffleWithSeed_mem {α : Type} (l : List α) (seed : List UInt8) (l' : List α)
    (h : shuffleWithSeed l seed = some l') : ∀ x ∈ l', x ∈ l := by
  unfold shuffleWithSeed shuffle at h
  cases hs : shuffleLoop (l.length - 1) l (Rng.ofSeed seed) with
  | none => rw [hs] at h; cases h
  | some p =>
    rw [hs] at h
    obtain ⟨l2, r2⟩ := p
    cases h
    exact shuffleLoop_mem _ _ _ _ _ hs

#print axioms decodeStateWitnessD2_nd
#print axioms shuffleWithSeed_mem

/-! ## The hypothesis and the driver relation -/

/-- Every shard layout of the claim's epoch table that decodes is well formed (README §9). -/
def LayoutsWF (cb : Bytes) : Prop :=
  ∀ cl, decodeClaimE cb = .ok cl → ∀ ep ∈ cl.epochs, ∀ L, decodeLayout ep.shardLayout = .ok L → L.WF

theorem LayoutsWF.of_claim {cb : Bytes} (h : LayoutsWF cb) {f : String → String} {cl : Claim}
    (hc : (decodeClaimE cb).mapError f = .ok cl) :
    ∀ ep ∈ cl.epochs, ∀ L, decodeLayout ep.shardLayout = .ok L → L.WF := by
  apply h
  cases hd : decodeClaimE cb with
  | error e => rw [hd] at hc; cases hc
  | ok x => rw [hd] at hc; cases hc; rfl

/-- The upper driver's five fields against the lower driver's. -/
structure DrvRel (d : ExecutionDriver) (ap : ApplyFn) (dw : Bytes → Except String StateWitnessD2)
    (rs : Layout → Rcpt → Nat) (vr : Layout → List Rcpt → Except String Unit) (orr : Layout → List Rcpt → Bytes) :
    Prop where
  dw_ok : ∀ sw w, d.decodeWitness sw = .ok w → dw sw = .ok w ∧ NDW w
  dw_err : ∀ sw e, d.decodeWitness sw = .error e → isExclusion e = true ∨ dw sw = .error e
  rs_eq : ∀ L r, rcptIsDistribution r = false → rs L r = d.receiptShard L r
  vr_eq : ∀ L l, L.WF → ND l → vr L l = d.validateRouting L l
  or_eq : ∀ L l, ND l → orr L l = d.outgoingRoot L l
  ap_ref : ∀ h h' p e t vu ps rcs txs cg, e.ctx.layout.WF →
    Refines (d.apply h p e t vu ps rcs txs cg) (ap h' p e t vu ps rcs txs cg)
  ap_nd : ∀ h p e t vu ps rcs txs cg out, e.ctx.layout.WF → d.apply h p e t vu ps rcs txs cg = .ok out →
    ND out.outgoing

/-! ## Walk steps -/

theorem Refines.bind_eq {α β : Type} {x : Except String α} {f g : α → Except String β}
    (h : ∀ a, x = .ok a → Refines (f a) (g a)) : Refines (x >>= f) (x >>= g) := by
  cases hx : x with
  | error e => exact Refines.refl _
  | ok a => exact h a hx

section steps
variable {d : ExecutionDriver} {ap : ApplyFn} {dw : Bytes → Except String StateWitnessD2}
  {rs : Layout → Rcpt → Nat} {vr : Layout → List Rcpt → Except String Unit} {orr : Layout → List Rcpt → Bytes}

theorem DrvRel.dw_bind (H : DrvRel d ap dw rs vr orr) {β : Type} (sw : Bytes) {f g : StateWitnessD2 → Except String β}
    (h : ∀ w, NDW w → Refines (f w) (g w)) : Refines (d.decodeWitness sw >>= f) (dw sw >>= g) := by
  cases hx : d.decodeWitness sw with
  | error e =>
    rcases H.dw_err sw e hx with he | he
    · exact Or.inr ⟨e, rfl, he⟩
    · rw [he]; exact Refines.refl _
  | ok w =>
    obtain ⟨h1, h2⟩ := H.dw_ok sw w hx
    rw [h1]; exact h w h2

theorem DrvRel.vr_bind (H : DrvRel d ap dw rs vr orr) {β : Type} {L : Layout} {l : List Rcpt} (hL : L.WF) (hl : ND l)
    {f g : Unit → Except String β} (h : ∀ u, Refines (f u) (g u)) :
    Refines (d.validateRouting L l >>= f) (vr L l >>= g) := by
  rw [H.vr_eq L l hL hl]; exact Refines.bind (Refines.refl _) h

theorem DrvRel.ap_bind (H : DrvRel d ap dw rs vr orr) {β : Type} (hk hk' : ActionHooks) (p : Prims) (e : Env) (t : PTrie)
    (vu : Option ValidatorUpdateFacts) (ps : List (Bytes × Nat)) (rcs : List Rcpt) (txs : List (TxD2 × Bool))
    (cg : Congestion) (hL : e.ctx.layout.WF) {f g : MainOutD2 → Except String β}
    (h : ∀ out, ND out.outgoing → Refines (f out) (g out)) :
    Refines (d.apply hk p e t vu ps rcs txs cg >>= f) (ap hk' p e t vu ps rcs txs cg >>= g) := by
  rcases H.ap_ref hk hk' p e t vu ps rcs txs cg hL with h1 | ⟨x, h1, hx⟩
  · rw [← h1]
    cases hx : d.apply hk p e t vu ps rcs txs cg with
    | error x => exact Refines.refl _
    | ok out => exact h out (H.ap_nd hk p e t vu ps rcs txs cg out hL hx)
  · rw [h1]; exact Or.inr ⟨x, rfl, hx⟩

theorem DrvRel.filter_eq (H : DrvRel d ap dw rs vr orr) (L : Layout) (s : Nat) (l : List EntryD2) (hl : ∀ e ∈ l, NDE e) :
    (l.map fun e => e.receipts.filter fun r => rs L r == s) =
      (l.map fun e => e.receipts.filter fun r => d.receiptShard L r == s) := by
  apply List.map_congr_left
  intro e he
  apply List.filter_congr
  intro r hr
  rw [H.rs_eq L r (hl e he r hr)]

end steps

theorem Refines.bind_error {α β : Type} {x : Except String α} {e : String} (hx : x = .error e)
    (f g : α → Except String β) : Refines (x >>= f) (x >>= g) := by
  subst hx; exact Or.inl rfl

theorem Refines.throw_bind_same {α β : Type} (e : String) (f g : α → Except String β) :
    Refines ((throw e : Except String α) >>= f) ((throw e : Except String α) >>= g) := Or.inl rfl

theorem Refines.bind_q {α β : Type} {x y : Except String α} {Q : α → Prop} {f g : α → Except String β}
    (hx : Refines x y ∧ EOk Q x) (h : ∀ a, Q a → Refines (f a) (g a)) : Refines (x >>= f) (y >>= g) := by
  obtain ⟨h1, h2⟩ := hx
  rcases h1 with rfl | ⟨e, rfl, he⟩
  · cases hx : x with
    | error e => exact Refines.refl _
    | ok a => exact h a (h2 a hx)
  · exact Or.inr ⟨e, rfl, he⟩

/-- A loop whose bodies refine pointwise from states satisfying an invariant of the lower body. -/
theorem Refines.forIn_inv {α σ : Type} (l : List α) (b : σ) {f g : α → σ → Except String (ForInStep σ)}
    (I : σ → Prop) (hb : I b)
    (h : ∀ a s, I s → Refines (f a s) (g a s) ∧ EOk (fun r => I r.value) (f a s)) :
    Refines (forIn l b f) (forIn l b g) ∧ EOk I (forIn l b f) := by
  induction l generalizing b with
  | nil => exact ⟨Refines.refl _, fun v hv => by cases hv; exact hb⟩
  | cons a t ih =>
    simp only [List.forIn_cons]
    obtain ⟨h1, h2⟩ := h a b hb
    refine ⟨Refines.bind_q ⟨h1, h2⟩ fun r hr => ?_, ?_⟩
    · cases r with
      | done s => exact Refines.refl _
      | yield s => exact (ih s hr).1
    · intro v hv
      cases hx : f a b with
      | error e => rw [hx] at hv; cases hv
      | ok r =>
        rw [hx] at hv
        have hr := h2 r hx
        cases r with
        | done s => cases hv; exact hr
        | yield s => exact (ih s hr).2 v hv

/-! ## The shells

The walk `o3s` extends O7's `shellA_lockstep`. Its guarded steps (`lower_bind_has`) record the claim's
layout facts (`hLc` at the claim decoding, `hLwf : L.WF` at `decodeLayout` of an epoch-table entry),
the witness invariant (`hw : NDW w` at `decodeWitness`), and pass the five differing fields with
`DrvRel`; the source-proof loop carries `∀ e ∈ proofs, NDE e` (`Refines.forIn_inv`, unary side `eok`).
The relation hypothesis must be named `H`. -/

open Lean Elab Tactic Meta in
/-- The application spine of `e` with metadata removed at every level. -/
partial def stripSpine (e : Expr) : Expr :=
  match e with
  | .app f a => .app (stripSpine f) a
  | .mdata _ e => stripSpine e
  | e => e

open Lean Elab Tactic Meta in
/-- `lower_bind_has` robust to metadata in the goal's spine. -/
elab "lbh " n:ident : tactic => withMainContext do
  let t := stripSpine (← instantiateMVars (← getMainTarget))
  let args := t.getAppArgs
  if args.size < 2 then throwError "lbh: not a relation goal"
  let x := stripSpine args[args.size - 2]!
  unless x.isAppOfArity ``Bind.bind 6 do throwError "lbh: not a bind"
  let a := x.getAppArgs[4]!
  let c ← realizeGlobalConstNoOverloadWithInfo n
  unless (a.find? (·.isConstOf c)).isSome do throwError "lbh: absent"

open Lean Elab Tactic Meta in
/-- `lower_head` robust to metadata in the goal's spine. -/
elab "lhd " n:ident : tactic => withMainContext do
  let t := stripSpine (← instantiateMVars (← getMainTarget))
  let args := t.getAppArgs
  if args.size < 2 then throwError "lhd: not a relation goal"
  let x := stripSpine args[args.size - 2]!
  let c ← realizeGlobalConstNoOverloadWithInfo n
  unless x.getAppFn.isConstOf c do throwError "lhd: other head"

set_option hygiene false in
macro "eok" : tactic => `(tactic|
  repeat' (first
    | (exact EOk.throw _)
    | (split <;> (rename_i hsplit; (try simp only [hsplit, pure_bind]); (try dsimp only)))
    | (refine EOk.bind fun _ => ?_)
    | (refine EOk.pure ?_; intro e he; simp only [ForInStep.value, List.mem_append, List.mem_singleton] at he;
        (rcases he with he | rfl) <;> first | exact hst e he | exact hw _ (lookupLastD2_mem _ _ _ ‹_›))
    | (refine EOk.pure ?_; exact hst)
    | (dsimp only)))

set_option hygiene false in
macro "o3s" : tactic => `(tactic|
  repeat' (first
    | (with_reducible exact Refines.refl _)
    | (exact Refines.throw_bind _ _ _)
    | (exact Refines.throw_bind_same _ _ _)
    | ((first | lbh MonadExcept.throw | lbh MonadExceptOf.throw | lbh throwThe); exact Refines.bind_error rfl _ _)
    | (lhd checkD2CoreWith; assumption)
    | (lbh decodeClaimE; refine Refines.bind_eq fun cl hcl => ?_; have hLc := LayoutsWF.of_claim ‹_› hcl)
    | (lbh ExecutionDriver.decodeWitness; refine DrvRel.dw_bind H _ fun w hw => ?_)
    | (lbh decodeLayout; refine Refines.bind_eq fun L hL => ?_;
        try (have hLwf : L.WF := hLc _ (List.mem_of_find?_eq_some ‹_›) _ hL))
    | (lbh ExecutionDriver.validateRouting;
        refine DrvRel.vr_bind H hLwf (hw _ (lookupLastD2_mem _ _ _ ‹_›)) fun _ => ?_)
    | (lbh ExecutionDriver.apply;
        refine DrvRel.ap_bind H _ _ _ _ _ _ _ _ _ _ hLwf fun out hout => ?_;
        try rw [DrvRel.or_eq H _ _ hout])
    | (lhd Pure.pure; rw [DrvRel.filter_eq H _ _ _ (fun e he => hst e (shuffleWithSeed_mem _ _ _ ‹_› e he))])
    | (lbh forIn; refine Refines.bind_q (Refines.forIn_inv (I := fun st : Nat × List EntryD2 => ∀ e ∈ st.2, NDE e) _ _
        (by simp) fun _ _ hst => ⟨?_, ?_⟩) fun st hst => ?_)
    | ((refine Refines.bind (by with_reducible assumption) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind' (by with_reducible rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by with_reducible rfl) fun _ => ?_); try dsimp only)
    | (refine Refines.ite_bind_join _ _ _ fun _ => ?_)
    | (refine Refines.ite_bind_skip _ _ ?_)
    | (refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_))
    | ((refine Refines.bind (Refines.forIn_congr _ _ fun _ _ => ?_) fun _ => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun (_, _) => ?_); try dsimp only)
    | ((refine Refines.bind' (by rfl) fun _ => ?_); try dsimp only)
    | (split <;> (rename_i hsplit; (try simp only [hsplit, pure_bind]); (try dsimp only)))))

/-- The upper driver: `d` with the five global-action fields. -/
def upD (d : ExecutionDriver) (ap : ApplyFn) (dw : Bytes → Except String StateWitnessD2)
    (rs : Layout → Rcpt → Nat) (vr : Layout → List Rcpt → Except String Unit) (orr : Layout → List Rcpt → Bytes) :
    ExecutionDriver :=
  { d with apply := ap, decodeWitness := dw, receiptShard := rs, validateRouting := vr, outgoingRoot := orr }

section shells
variable (d : ExecutionDriver) (ap : ApplyFn) (dw : Bytes → Except String StateWitnessD2)
    (rs : Layout → Rcpt → Nat) (vr : Layout → List Rcpt → Except String Unit) (orr : Layout → List Rcpt → Bytes)

set_option maxHeartbeats 16000000 in
theorem checkD2CoreWithObs_o3 (H : DrvRel d ap dw rs vr orr) (h h' : ActionHooks) (a : Bool) (c w : Bytes)
    (g : Option Nat) (hLay : LayoutsWF c) :
    Refines (checkD2CoreWithObs d h a c w g) (checkD2CoreWithObs (upD d ap dw rs vr orr) h' a c w g) := by
  unfold checkD2CoreWithObs upD
  dsimp only
  o3s
  all_goals eok

theorem checkD2CoreWith_o3 (H : DrvRel d ap dw rs vr orr) (h h' : ActionHooks) (a : Bool) (c w : Bytes)
    (g : Option Nat) (hLay : LayoutsWF c) :
    Refines (checkD2CoreWith d h a c w g) (checkD2CoreWith (upD d ap dw rs vr orr) h' a c w g) :=
  Refines.map _ (checkD2CoreWithObs_o3 d ap dw rs vr orr H h h' a c w g hLay)

set_option maxHeartbeats 16000000 in
theorem checkD2CoreGWith_o3 (H : DrvRel d ap dw rs vr orr) (h h' : ActionHooks) (a : Bool) (c w : Bytes)
    (g : Option Nat) (hLay : LayoutsWF c) :
    Refines (checkD2CoreGWith d h a c w g) (checkD2CoreGWith (upD d ap dw rs vr orr) h' a c w g) := by
  have hW := checkD2CoreWith_o3 d ap dw rs vr orr H h h' a c w g hLay
  unfold checkD2CoreGWith
  unfold upD at hW ⊢
  dsimp only
  o3s
  all_goals eok

#print axioms checkD2CoreWithObs_o3
#print axioms checkD2CoreGWith_o3

end shells

end NearSpecV3.Successor
