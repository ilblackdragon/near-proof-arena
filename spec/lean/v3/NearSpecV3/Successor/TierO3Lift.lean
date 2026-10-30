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

theorem layoutBytesOf_mem (c : Claim) (e lb : Bytes) (h : layoutBytesOf c e = .ok lb) :
    ∃ ep ∈ c.epochs, ep.shardLayout = lb := by
  unfold layoutBytesOf at h
  split at h
  · rename_i r hr; cases h; exact ⟨r, List.mem_of_find?_eq_some hr, rfl⟩
  · cases h

theorem EOk.bind_eq {α β : Type} {P : β → Prop} {x : Except String α} {f : α → Except String β}
    (hf : ∀ a, x = .ok a → EOk P (f a)) : EOk P (x >>= f) := by
  intro v h
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact hf a hx v h

theorem EOk.forIn {α σ : Type} (l : List α) (b : σ) {f : α → σ → Except String (ForInStep σ)}
    (I : σ → Prop) (hb : I b) (h : ∀ a s, I s → EOk (fun r => I r.value) (f a s)) : EOk I (forIn l b f) := by
  induction l generalizing b with
  | nil => intro v hv; cases hv; exact hb
  | cons a t ih =>
    simp only [List.forIn_cons]
    intro v hv
    cases hx : f a b with
    | error e => rw [hx] at hv; cases hv
    | ok r =>
      rw [hx] at hv
      have hr := h a b hb r hx
      cases r with
      | done s => cases hv; exact hr
      | yield s => exact ih s hr v hv

/-- The walk's main layout is an epoch-table layout. -/
theorem walkSegment_mainLayout (c : Claim) (blks : List Blk) (ae : List Bytes) (s0 : Nat) (wk : Walk)
    (h : walkSegment c blks ae s0 = .ok wk) : ∃ ep ∈ c.epochs, ep.shardLayout = wk.mainLayout := by
  unfold walkSegment at h
  dsimp only at h
  obtain ⟨st, hst, h⟩ := Codec.ok_bind h
  have hI : ∀ x, st.2.2.2.2.1 = some x → ∃ ep ∈ c.epochs, ep.shardLayout = x.2.2 := by
    refine EOk.forIn (I := fun st : Nat × Nat × List WalkTransition × List (Nat × Nat) × Option (Nat × Nat × Bytes) × Option Nat =>
      ∀ x, st.2.2.2.2.1 = some x → ∃ ep ∈ c.epochs, ep.shardLayout = x.2.2) _ _ (by intro x hx; cases hx) ?_ st hst
    intro i s hs
    try dsimp only
    repeat' (first
      | (exact EOk.throw _)
      | (refine EOk.bind_eq fun _ _ => ?_)
      | (refine EOk.ite _ (fun _ => ?_) (fun _ => ?_))
      | (refine EOk.pure ?_; intro x hx; simp only [ForInStep.value, Option.some.injEq] at hx;
         first | exact hs x hx | (subst hx; exact layoutBytesOf_mem _ _ _ ‹_›))
      | (split <;> ((try simp only [pure_bind]); (try dsimp only)))
      | (dsimp only))
  split at h
  · rename_i b2i ms ml hm
    have hx := hI _ hm
    repeat' (first | (cases h; exact hx) | (cases h; done) | (split at h))
  · cases h

theorem walkSegment_wf {c : Claim} (hLc : ∀ ep ∈ c.epochs, ∀ L, decodeLayout ep.shardLayout = .ok L → L.WF)
    {blks : List Blk} {ae : List Bytes} {s0 : Nat} {wk : Walk} (hwk : walkSegment c blks ae s0 = .ok wk)
    {L : Layout} (hL : decodeLayout wk.mainLayout = .ok L) : L.WF := by
  obtain ⟨ep, hep, he⟩ := walkSegment_mainLayout c blks ae s0 wk hwk
  exact hLc ep hep L (he ▸ hL)

#print axioms walkSegment_mainLayout

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
        try (first | (have hLwf : L.WF := hLc _ (List.mem_of_find?_eq_some ‹_›) _ hL)
                   | (have hLwf : L.WF := walkSegment_wf hLc ‹_› hL)))
    | (lbh walkSegment; refine Refines.bind_eq fun wk hwk => ?_)
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
    | (rw [DrvRel.or_eq H _ _ ND.nil])
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

set_option maxHeartbeats 32000000 in
theorem checkReshardCoreObs_o3 (H : DrvRel d ap dw rs vr orr) (h h' : ActionHooks) (a : Bool) (c w : Bytes)
    (g : Option Nat) (hLay : LayoutsWF c) :
    Refines (checkReshardCoreObs d h a c w g) (checkReshardCoreObs (upD d ap dw rs vr orr) h' a c w g) := by
  unfold checkReshardCoreObs upD
  dsimp only
  o3s
  all_goals eok

theorem checkReshardCore_o3 (H : DrvRel d ap dw rs vr orr) (h h' : ActionHooks) (a : Bool) (c w : Bytes)
    (g : Option Nat) (hLay : LayoutsWF c) :
    Refines (checkReshardCore d h a c w g) (checkReshardCore (upD d ap dw rs vr orr) h' a c w g) :=
  Refines.map _ (checkReshardCoreObs_o3 d ap dw rs vr orr H h h' a c w g hLay)

#print axioms checkD2CoreWithObs_o3
#print axioms checkD2CoreGWith_o3
#print axioms checkReshardCoreObs_o3

end shells

/-! ## The global-action drivers satisfy `DrvRel` -/

/-- The global-action routing check passes on non-distribution receipts of a well-formed layout. -/
theorem validateRouting_global (cfg : NearCfg) (pol : CodeWitnessPolicy) (L : Layout) (hL : L.WF) :
    ∀ l : List Rcpt, ND l → (recorderDriver cfg true pol).validateRouting L l = pure ()
  | [], _ => rfl
  | r :: l, hl => by
    have h1 := globalTarget_wf hL r (hl r List.mem_cons_self)
    have h2 := validateRouting_global cfg pol L hL l (hl.sub fun x hx => List.mem_cons_of_mem _ hx)
    simp only [recorderDriver, ↓reduceIte] at h2 ⊢
    simp only [List.forIn_cons, h1]
    exact h2

/-- **O3, driver fields.** A driver whose five fields are the lower recorder driver's (any other
fields) against the global-action recorder driver's fields. -/
theorem drvRel_of_lower (d : ExecutionDriver) (w : NearCfg) (hg : w.globalActions = false) (pol : CodeWitnessPolicy)
    (h1 : d.decodeWitness = decodeStateWitnessD2) (h2 : d.receiptShard = fun l r => l.shardOf r.recv)
    (h3 : d.validateRouting = fun _ _ => pure ()) (h4 : d.outgoingRoot = outgoingReceiptsRootD2)
    (h5 : d.apply = (recorderDriver w false pol).apply) :
    DrvRel d (recorderDriver { w with globalActions := true } true pol).apply
      (recorderDriver { w with globalActions := true } true pol).decodeWitness
      (recorderDriver { w with globalActions := true } true pol).receiptShard
      (recorderDriver { w with globalActions := true } true pol).validateRouting
      (recorderDriver { w with globalActions := true } true pol).outgoingRoot where
  dw_ok sw x hx := by
    rw [h1] at hx
    simp only [recorderDriver, ↓reduceIte]
    rcases Codec.decodeWitness_ref sw with he | ⟨e, he, _⟩
    · exact ⟨he ▸ hx, decodeStateWitnessD2_nd sw x hx⟩
    · rw [he] at hx; cases hx
  dw_err sw e hx := by
    rw [h1] at hx
    simp only [recorderDriver, ↓reduceIte]
    rcases Codec.decodeWitness_ref sw with he | ⟨e', he, hX⟩
    · exact Or.inr (he ▸ hx)
    · rw [he] at hx; cases hx; exact Or.inl hX
  rs_eq L r hr := by
    rw [h2]
    exact recorderDriver_receiptShard_globals _ pol L r hr
  vr_eq L l hL hl := by
    rw [h3, validateRouting_global _ pol L hL l hl]
  or_eq L l hl := by
    rw [h4]
    exact recorderDriver_outgoingRoot_globals _ pol L l hl
  ap_ref _ _ p e t vu ps rcs txs cg hL := by
    rw [h5]
    exact run_global w hg pol p e hL t vu ps rcs txs cg
  ap_nd _ p e t vu ps rcs txs cg out hL hx := by
    rw [h5] at hx
    exact run_global_nd w hg pol p e hL t vu ps rcs txs cg out hx

#print axioms drvRel_of_lower

/-! ## Configuration and tier level -/

/-- The shells, for a lower driver with the recorder driver's five fields and the upper driver with
the global-action recorder driver's. -/
theorem shells_o3 (dL dU : ExecutionDriver) (w : NearCfg) (pol : CodeWitnessPolicy)
    (H : DrvRel dL (recorderDriver { w with globalActions := true } true pol).apply
      (recorderDriver { w with globalActions := true } true pol).decodeWitness
      (recorderDriver { w with globalActions := true } true pol).receiptShard
      (recorderDriver { w with globalActions := true } true pol).validateRouting
      (recorderDriver { w with globalActions := true } true pol).outgoingRoot)
    (hd : dU = upD dL (recorderDriver { w with globalActions := true } true pol).apply
      (recorderDriver { w with globalActions := true } true pol).decodeWitness
      (recorderDriver { w with globalActions := true } true pol).receiptShard
      (recorderDriver { w with globalActions := true } true pol).validateRouting
      (recorderDriver { w with globalActions := true } true pol).outgoingRoot)
    (h h' : ActionHooks) (a : Bool) (c wb : Bytes) (g : Option Nat) (hLay : LayoutsWF c) :
    Refines (checkD2CoreGWith dL h a c wb g) (checkD2CoreGWith dU h' a c wb g) ∧
    Refines (checkD2CoreWith dL h a c wb g) (checkD2CoreWith dU h' a c wb g) ∧
    Refines (checkReshardCore dL h a c wb g) (checkReshardCore dU h' a c wb g) := by
  subst hd
  exact ⟨checkD2CoreGWith_o3 _ _ _ _ _ _ H h h' a c wb g hLay, checkD2CoreWith_o3 _ _ _ _ _ _ H h h' a c wb g hLay,
    checkReshardCore_o3 _ _ _ _ _ _ H h h' a c wb g hLay⟩

/-- **O3, configuration level.** On every whole-state configuration (storage resolution, complete
code or resharding set) with global actions off, switching them on refines the checker on every
claim whose shard layouts are well formed. -/
theorem Lift.globalActions_wf (cfg : ProtocolCfg) (hga : cfg.globalActions = false)
    (hw : (cfg.storageResolution || cfg.completeCodeWitness || cfg.resharding) = true) (c wb : Bytes)
    (hLay : LayoutsWF c) :
    Refines (checkSuccessor cfg c wb) (checkSuccessor { cfg with globalActions := true } c wb) := by
  obtain ⟨pv, fl, gc, gen, ll, sr, ga, cc, ch, rs, seg, wu, lu, od, rh⟩ := cfg
  simp only at hga hw
  subst hga
  have h1 : (sr || false || cc || rs) = true := by
    cases sr <;> cases cc <;> cases rs <;> simp_all
  have h2 : (sr || true || cc || rs) = true := by simp
  let W := ProtocolCfg.wasm ⟨pv, fl, gc, gen, ll, sr, false, cc, ch, rs, seg, wu, lu, od, rh⟩
  let P : CodeWitnessPolicy := if cc then .complete else .coldPartial
  unfold checkSuccessor
  dsimp only
  split
  · simp only [h1, h2, ite_true]
    cases rs
    · simp only [Bool.false_and, Bool.false_eq_true, ite_false]
      refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
      · exact (shells_o3 _ _ W P (drvRel_of_lower _ W rfl P (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)) (by rfl) _ _ _ _ _ _ hLay).1
      · exact (shells_o3 _ _ W P (drvRel_of_lower _ W rfl P (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)) (by rfl) _ _ _ _ _ _ hLay).2.1
    · simp only [Bool.true_and, ite_true]
      refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
      · exact (shells_o3 _ _ W P (drvRel_of_lower _ W rfl P (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)) (by rfl) _ _ _ _ _ _ hLay).2.2
      · refine Refines.ite_congr _ (fun _ => ?_) (fun _ => ?_)
        · exact (shells_o3 _ _ W P (drvRel_of_lower _ W rfl P (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)) (by rfl) _ _ _ _ _ _ hLay).1
        · exact (shells_o3 _ _ W P (drvRel_of_lower _ W rfl P (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)) (by rfl) _ _ _ _ _ _ hLay).2.1
  · exact Refines.refl _

/-- **O3, `.storageResolution ⊑ .globalActions`**, on claims whose shard layouts are well formed. -/
theorem relSuccessor_storageResolution_globalActions_wf (c w : Bytes) (hLay : LayoutsWF c) :
    Refines (Tier.checker .storageResolution c w) (Tier.checker .globalActions c w) :=
  Lift.globalActions_wf (Tier.cfg .storageResolution) rfl rfl c w hLay

/-- **O3, the resharding configuration** (the `hGA` premise of `relSuccessor_resharding_allFeatures_of`,
on claims whose shard layouts are well formed). -/
theorem lift_resharding_globalActions_wf (c w : Bytes) (hLay : LayoutsWF c) :
    Refines (checkSuccessor (Tier.cfg .resharding) c w)
      (checkSuccessor { Tier.cfg .resharding with globalActions := true } c w) :=
  Lift.globalActions_wf (Tier.cfg .resharding) rfl rfl c w hLay

/-- `.resharding ⊑ .allFeatures`, on claims whose shard layouts are well formed. -/
theorem relSuccessor_resharding_allFeatures_wf (c w : Bytes) (hLay : LayoutsWF c) :
    Refines (Tier.checker .resharding c w) (Tier.checker .allFeatures c w) :=
  (lift_resharding_globalActions_wf c w hLay).trans (Lift.gateB _ rfl c w)

/-- **`.curveHosts ⊑ .allFeatures` at verdict level, under the layout hypothesis only**
(`relSuccessor_curveHosts_allFeatures_of` with `resharding_vlift_curveHosts` and the O3 lift). -/
theorem relSuccessor_curveHosts_allFeatures_wf (c w : Bytes) (hLay : LayoutsWF c) :
    VRefines (Tier.checker .curveHosts c w) (Tier.checker .allFeatures c w) :=
  ((resharding_vlift_curveHosts c w).trans (lift_resharding_globalActions_wf c w hLay).toV).trans
    ((Lift.gateB _ rfl).toV c w)

#print axioms Lift.globalActions_wf
#print axioms relSuccessor_storageResolution_globalActions_wf
#print axioms relSuccessor_resharding_allFeatures_wf
#print axioms relSuccessor_curveHosts_allFeatures_wf

end NearSpecV3.Successor
