import NearSpecV3.Wasm.FuelGasFin
import NearSpecV3.Wasm.FuelGasSem
/-!
# O-W4 (static): `gasTable` charges every costly instruction before it runs

`wc_gasTable`: for a body whose nesting is `openAt` (`NestOK`), the table finite-wasm's
instrumentation produces (`gasTable cfg.gas pf.code true`) satisfies `WC`.

Proof structure (helper modules `FuelGas*.lean`):
* `FuelGasScan`: the scan as a fold of `gstep`, per-instruction effects, `gAdjust` sequences.
* `FuelGasInv`: frame invariant `Inv` relating the scan's frame stack to `openAt`
  (loop frames carry their own header indices, `if` frames are forward, a targeted `block` frame is
  forward, a frame's parent poly flag is the poly flag at the opener); point tracking (`track`).
* `FuelGasFin`: live code is never in a poly region (`live_poly`); a branch to a loop marks its
  header point `.post` (`loop_post`).
* `FuelGasOpt`: the two `optimize` passes as list recursions, pass 2 groups (`SegQ`), the table.
* `FuelGasSem`: `WC` from abstract group-start facts (`GT`).
* this file: the raw points as one block per offset, per-offset kinds/fees, jump targets start a group.
-/
namespace NearSpecV3.Wasm.FuelGas
open NearSpecV3.Wasm

/-! ## The raw points as blocks, one per offset -/

def bsOf (g : GasCfg) (code : Array Instr) (t : Nat) : Option Pt × Pt :=
  (if (scanS g code t).sched.isSome then some (scanS g code code.size).pts[(scanS g code t).pts.size]!
    else none,
   (scanS g code code.size).pts[(scanS g code (t + 1)).pts.size - 1]!)

theorem flatB_append (a b : List (Option Pt × Pt)) : flatB (a ++ b) = flatB a ++ flatB b := by
  simp [flatB, List.flatMap_append]

theorem flatB_single (b : Option Pt × Pt) : flatB [b] = b.1.toList ++ [b.2] := by
  simp [flatB]

theorem seg (g : GasCfg) (code : Array Instr) (t : Nat) (ht : t < code.size) :
    ((scanS g code code.size).pts.toList.drop (scanS g code t).pts.size).take
      ((scanS g code (t + 1)).pts.size - (scanS g code t).pts.size) =
      (bsOf g code t).1.toList ++ [(bsOf g code t).2] := by
  have h1 := sz_succ g code t ht
  have h2 := sz_mono g code (t + 1) code.size (by omega) (by omega)
  generalize hA : (scanS g code code.size).pts = A at h2 ⊢
  unfold bsOf
  rw [hA]
  generalize (scanS g code t).pts.size = a at h1 h2 ⊢
  generalize (scanS g code (t + 1)).pts.size = b at h1 h2 ⊢
  split at h1
  · rename_i hs
    rw [if_pos hs]
    have e1 : b - a = 2 := by omega
    rw [e1, List.drop_eq_getElem_cons (by simp; omega), List.drop_eq_getElem_cons (by simp; omega)]
    simp only [List.take_succ_cons, List.take_zero, Option.toList_some, List.singleton_append]
    have ha : a < A.size := by omega
    have hb : b - 1 < A.size := by omega
    rw [show b - 1 = a + 1 by omega]
    simp [getElem!_pos A a ha, getElem!_pos A (a + 1) (by omega)]
  · rename_i hs
    rw [if_neg hs]
    have e1 : b - a = 1 := by omega
    rw [e1, List.drop_eq_getElem_cons (by simp; omega)]
    simp only [List.take_succ_cons, List.take_zero, Option.toList_none, List.nil_append]
    have hb : b - 1 < A.size := by omega
    rw [show b - 1 = a by omega]
    simp [getElem!_pos A a (by omega)]

theorem take_flat (g : GasCfg) (code : Array Instr) : ∀ k, k ≤ code.size →
    (scanS g code code.size).pts.toList.take (scanS g code k).pts.size =
      flatB ((List.range k).map (bsOf g code)) := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.map_append, flatB_append, ← ih (by omega), List.map_singleton,
      flatB_single, ← seg g code k (by omega)]
    have := sz_mono g code k (k + 1) (by omega) hk
    rw [← List.take_add]
    congr 1; omega

theorem raw_eq (g : GasCfg) (code : Array Instr) :
    (scanS g code code.size).pts.toList = flatB ((List.range code.size).map (bsOf g code)) := by
  rw [← take_flat g code code.size (Nat.le_refl _)]
  exact (List.take_of_length_le (by simp)).symm

theorem bang_of {A : Array Pt} {i : Nat} {x : Pt} (h : A[i]? = some x) : A[i]! = x := by
  obtain ⟨hl, e⟩ := Array.getElem?_eq_some_iff.mp h
  rw [getElem!_pos A i hl]; exact e

def ownOK (k : IK) : Prop := k = .pure ∨ k = .pre ∨ k = .linear ∨ k = .post

theorem ownReq_kind (g : GasCfg) (s : GS) (ins : Instr) :
    (ownReq g s ins).1 = .pure ∨ (ownReq g s ins).1 = .pre ∨ (ownReq g s ins).1 = .linear := by
  cases ins <;> simp only [ownReq, plainE, sideE, pureE] <;> (try split) <;> simp

theorem ownReq_fee (g : GasCfg) (s : GS) (ins : Instr) (hl : g.regular ≤ g.linearBase) :
    g.regular * costOf ins ≤ (ownReq g s ins).2.c := by
  cases ins <;> simp [ownReq, plainE, sideE, pureE, costOf, isFreeInstr, Fee.const, Fee.zero] <;>
    first | omega | (split <;> simp)

theorem ownPoly_live (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (t : Nat)
    (hl : Live pf (openAt pf.code) t) (ht : t < pf.code.size) :
    ownPoly (scanS g pf.code t) pf.code[t] = false := by
  have hp := live_poly g pf hn t hl ht
  cases pf.code[t] <;> simp only [ownPoly] <;> try exact hp
  unfold popF
  split
  · rename_i f L hs
    simp only
    have I := inv_all g pf hn t (by omega)
    cases h : f.poly
    · rfl
    · have := inh_iter g pf.code t I 1 f (by simp [frs, hs]) h
      rw [this] at hp; cases hp
  · exact hp

def Mf (g : GasCfg) (code : Array Instr) (t : Nat) : Pt := mBlk (bsOf g code t)

theorem mergeSame_some (a b : IK) (h : a ≠ .linear) : (mergeSame a b).isSome = true := by
  cases a <;> cases b <;> simp_all [mergeSame]

structure OffFacts (g : GasCfg) (pf : PFunc) (t : Nat) : Prop where
  bok : BOK (bsOf g pf.code t)
  off2 : (bsOf g pf.code t).2.off = t
  off : (Mf g pf.code t).off = t
  fee : (ownReq g (scanS g pf.code t) pf.code[t]!).2.c ≤ (Mf g pf.code t).fee.c
  own : (bsOf g pf.code t).2.k = (if ownPoly (scanS g pf.code t) pf.code[t]! then .unreach
      else (ownReq g (scanS g pf.code t) pf.code[t]!).1) ∨
    (bsOf g pf.code t).2.k = .pre ∨ (bsOf g pf.code t).2.k = .post
  sch : ∀ sp, (bsOf g pf.code t).1 = some sp → ∃ κ f, (scanS g pf.code t).sched = some (κ, f) ∧
    (sp.k = κ ∨ sp.k = .post) ∧ sp.k ≠ .linear ∧
    sp = (scanS g pf.code pf.code.size).pts[(scanS g pf.code t).pts.size]!
  some_of : (scanS g pf.code t).sched.isSome = true → ∃ sp, (bsOf g pf.code t).1 = some sp

theorem offFacts (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (t : Nat)
    (ht : t < pf.code.size) : OffFacts g pf t := by
  have hct : pf.code[t]! = pf.code[t] := getElem!_pos pf.code t ht
  obtain ⟨op, h1, h2, h3, h4⟩ := own_final g pf hn t ht
  have hb2 : (bsOf g pf.code t).2 = op := bang_of h1
  have hsch : ∀ sp, (bsOf g pf.code t).1 = some sp → ∃ κ f, (scanS g pf.code t).sched = some (κ, f) ∧
      sp.off = t ∧ sp.fee = f ∧ (sp.k = κ ∨ sp.k = .post) ∧ sp.k ≠ .linear ∧
      sp = (scanS g pf.code pf.code.size).pts[(scanS g pf.code t).pts.size]! := by
    intro sp hsp
    unfold bsOf at hsp
    split at hsp
    · rename_i hs
      cases hsp
      obtain ⟨⟨κ, f⟩, hκ⟩ := Option.isSome_iff_exists.mp hs
      obtain ⟨pt, p1, p2, p3, p4⟩ := sched_final_k g pf hn t ht κ f hκ
      rw [bang_of p1]
      refine ⟨κ, f, hκ, p2, p3, p4, ?_, rfl⟩
      have hk := sched_scan g pf.code
      rcases p4 with p4 | p4
      · rw [p4]
        cases t with
        | zero => rw [sched_zero] at hκ; cases hκ
        | succ t =>
          rw [sched_scan g pf.code t (by omega)] at hκ
          rcases schedOf_kind g _ _ κ f hκ with h | ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> simp
      · rw [p4]; simp
    · cases hsp
  have hbok : BOK (bsOf g pf.code t) := by
    intro sp hsp
    obtain ⟨κ, f, _, a1, _, _, a3, _⟩ := hsch sp hsp
    rw [hb2]
    exact ⟨by rw [a1, h2], mergeSame_some _ _ a3⟩
  refine ⟨hbok, by rw [hb2, h2], by unfold Mf; rw [mBlk_off _ hbok, hb2, h2], ?_, ?_, ?_, ?_⟩
  · unfold Mf mBlk
    rw [hct]
    split
    · rw [hb2, h3]; exact Nat.le_refl _
    · rw [hb2, h3]; simp [Fee.add]
  · rw [hb2, hct]
    rcases h4 with h4 | h4
    · exact Or.inl h4
    · rcases h4 with ⟨h, _⟩ | ⟨h, _⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · intro sp hsp
    obtain ⟨κ, f, a0, _, _, a2, a3, a4⟩ := hsch sp hsp
    exact ⟨κ, f, a0, a2, a3, a4⟩
  · intro hs; unfold bsOf; rw [if_pos hs]; exact ⟨_, rfl⟩

theorem Mf_fee (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (t : Nat)
    (ht : t < pf.code.size) (hl : g.regular ≤ g.linearBase) :
    g.regular * (match pf.code[t]? with | some i => costOf i | none => 0) ≤ (Mf g pf.code t).fee.c := by
  have F := offFacts g pf hn t ht
  have hct : pf.code[t]! = pf.code[t] := getElem!_pos pf.code t ht
  have := F.fee
  rw [hct] at this
  have h2 := ownReq_fee g (scanS g pf.code t) pf.code[t] hl
  rw [show pf.code[t]? = some pf.code[t] by simp [ht]]
  simp only
  omega

theorem own_live (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (t : Nat)
    (hl : Live pf (openAt pf.code) t) (ht : t < pf.code.size) : ownOK (bsOf g pf.code t).2.k := by
  have F := offFacts g pf hn t ht
  have hct : pf.code[t]! = pf.code[t] := getElem!_pos pf.code t ht
  have hp := ownPoly_live g pf hn t hl ht
  rcases F.own with h | h | h
  · rw [hct, hp] at h
    simp only [Bool.false_eq_true, if_false] at h
    rw [h]
    rcases ownReq_kind g (scanS g pf.code t) pf.code[t] with k | k | k <;> rw [k] <;> simp [ownOK]
  · rw [h]; simp [ownOK]
  · rw [h]; simp [ownOK]

theorem Mf_not_unreach (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (t : Nat)
    (hl : Live pf (openAt pf.code) t) (ht : t < pf.code.size) : (Mf g pf.code t).k ≠ .unreach := by
  have F := offFacts g pf hn t ht
  have ho := own_live g pf hn t hl ht
  unfold Mf mBlk
  split
  · rename_i hb
    rcases ho with h | h | h | h <;> rw [h] <;> simp
  · rename_i sp hb
    obtain ⟨κ, f, hκ, hk, _, _⟩ := F.sch sp hb
    have hsk : sp.k = .post ∨ sp.k = .pure := by
      rcases hk with hk | hk
      · rw [hk]
        cases t with
        | zero => rw [sched_zero] at hκ; cases hκ
        | succ t =>
          rw [sched_scan g pf.code t (by omega)] at hκ
          rcases schedOf_kind g _ _ κ f hκ with h | ⟨h, hu⟩ | ⟨h, _⟩
          · exact Or.inl h
          · exfalso
            have := live_prev pf hn (t + 1) hl (by omega)
            simp only [Nat.add_sub_cancel] at this
            exact this (by rw [← hu]; simp [show t < pf.code.size by omega])
          · exact Or.inr h
      · exact Or.inl hk
    simp only
    rcases hsk with h1 | h1 <;> rcases ho with h | h | h | h <;> rw [h1, h] <;> simp [mergeSame]

theorem Mf_starter (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (t : Nat)
    (hl : Live pf (openAt pf.code) t) (ht : t < pf.code.size)
    (hs : (scanS g pf.code t).sched.isSome = true)
    (hpost : ∃ pt, (scanS g pf.code pf.code.size).pts[(scanS g pf.code t).pts.size]? = some pt ∧
      pt.k = .post) :
    starter (Mf g pf.code t).k = true := by
  have F := offFacts g pf hn t ht
  have ho := own_live g pf hn t hl ht
  obtain ⟨sp, hsp⟩ := F.some_of hs
  obtain ⟨_, _, _, _, _, e⟩ := F.sch sp hsp
  obtain ⟨pt, h1, h2⟩ := hpost
  rw [bang_of h1] at e
  subst e
  unfold Mf mBlk
  rw [hsp]
  simp only
  rcases ho with h | h | h | h <;> rw [h2, h] <;> simp [mergeSame, starter]

/-! ## Jump targets start a group -/

theorem open_le_end (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (pc l o : Nat)
    (hl : (openAt pf.code pc)[l]? = some o) : pc ≤ endAt pf o := by
  obtain ⟨hop, i, hi, hopn⟩ := openAt_mem pf.code pc o (List.mem_of_getElem? hl)
  obtain ⟨_, hlt, hend, _, henc⟩ := hn.opener o i hi hopn
  have h1 := (hn.end_ _ hend).2 o (openAt pf.code o) henc
  have key : ∀ d, ∀ x ∈ openAt pf.code (endAt pf o + 1 + d), x ∈ openAt pf.code o ∨ endAt pf o < x := by
    intro d
    induction d with
    | zero => intro x hx; left; rw [Nat.add_zero, h1.2] at hx; exact hx
    | succ d ih =>
      intro x hx
      rw [show endAt pf o + 1 + (d + 1) = (endAt pf o + 1 + d) + 1 by omega, openAt_succ] at hx
      split at hx
      · rename_i i' _
        cases i' <;> simp only [openStep] at hx
        all_goals first
          | (rcases List.mem_cons.mp hx with hx | hx
             · right; omega
             · exact ih x hx)
          | exact ih x (List.mem_of_mem_tail hx)
          | exact ih x hx
      · exact ih x hx
  rcases Nat.lt_or_ge (endAt pf o) pc with hc | hc
  · exfalso
    have := key (pc - (endAt pf o + 1)) o
      (by rw [show endAt pf o + 1 + (pc - (endAt pf o + 1)) = pc by omega]; exact List.mem_of_getElem? hl)
    rcases this with h | h
    · have := (openAt_mem pf.code o o h).1; omega
    · omega
  · exact hc

theorem fwd_end (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (o : Nat) (i : Instr)
    (hi : pf.code[o]? = some i)
    (hk : (∃ bt, i = .if_ bt) ∨ ((∃ bt, i = .block bt) ∧ TgtB pf.code o (endAt pf o))) :
    (scanS g pf.code (endAt pf o + 1)).sched = some (.post, Fee.zero) := by
  have hop : isOpener i = true := by
    rcases hk with ⟨bt, rfl⟩ | ⟨⟨bt, rfl⟩, _⟩ <;> rfl
  obtain ⟨_, _, hend, _, henc⟩ := hn.opener o i hi hop
  have he := lt_of_get pf.code _ _ hend
  have I := inv_all g pf hn (endAt pf o) (by omega)
  obtain ⟨f, hf, hfk⟩ := I.kind 0 o (by rw [henc]; rfl)
  rw [cur_get0] at hf; cases hf
  have hfw : (scanS g pf.code (endAt pf o)).cur.kind = .forward := by
    unfold FrK at hfk
    rw [hi] at hfk
    rcases hk with ⟨bt, rfl⟩ | ⟨⟨bt, rfl⟩, ht⟩
    · exact hfk
    · exact hfk.2 ht
  have hc : pf.code[endAt pf o] = .end_ := by simpa [he] using hend
  rw [sched_scan g pf.code _ he, hc]
  simp [schedOf, hfw, isFwd]

theorem post_of_sched (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (q : Nat)
    (hq : q < pf.code.size) (f : Fee) (hs : (scanS g pf.code q).sched = some (.post, f)) :
    (scanS g pf.code q).sched.isSome = true ∧
    ∃ pt, (scanS g pf.code pf.code.size).pts[(scanS g pf.code q).pts.size]? = some pt ∧ pt.k = .post := by
  refine ⟨by rw [hs]; rfl, ?_⟩
  obtain ⟨pt, h1, _, _, h4⟩ := sched_final_k g pf hn q hq _ f hs
  exact ⟨pt, h1, by rcases h4 with h | h <;> exact h⟩

theorem target_branch (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (pc l o : Nat)
    (hpc : pc < pf.code.size) (hlab : l ∈ brLabels pf.code[pc]) (hl : (openAt pf.code pc)[l]? = some o)
    (hq : labTarget pf o < pf.code.size) :
    (scanS g pf.code (labTarget pf o)).sched.isSome = true ∧
    ∃ pt, (scanS g pf.code pf.code.size).pts[(scanS g pf.code (labTarget pf o)).pts.size]? = some pt ∧
      pt.k = .post := by
  obtain ⟨hopc, i, hi, hopn⟩ := openAt_mem pf.code pc o (List.mem_of_getElem? hl)
  have hot := lt_of_get pf.code o i hi
  unfold labTarget at hq ⊢
  rw [hi] at hq ⊢
  cases i <;> simp [isOpener] at hopn <;> simp only at hq ⊢
  case loop bt =>
    have hc : pf.code[o] = .loop bt := by simpa [hot] using hi
    refine ⟨by rw [sched_scan g pf.code o hot, hc]; rfl, ?_⟩
    exact loop_post g pf hn pc l o bt hpc hlab hl hi
  case if_ bt =>
    exact post_of_sched g pf hn _ hq _ (fwd_end g pf hn o _ hi (Or.inl ⟨bt, rfl⟩))
  case block bt =>
    apply post_of_sched g pf hn _ hq _ (fwd_end g pf hn o _ hi (Or.inr ⟨⟨bt, rfl⟩, ?_⟩))
    have hle := open_le_end pf hn pc l o hl
    obtain ⟨_, _, hend, _, _⟩ := hn.opener o _ hi rfl
    have hne : pc ≠ endAt pf o := by
      intro h
      have h2 : pf.code[pc] = .end_ := by
        have : pf.code[pc]? = some .end_ := by rw [h]; exact hend
        simpa [hpc] using this
      rw [h2] at hlab; simp [brLabels] at hlab
    exact ⟨pc, hopc, by omega, pf.code[pc], l, by simp [hpc], hlab, hl⟩

theorem jump_start (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (pc q : Nat)
    (hs : Succ pf (openAt pf.code) pc q true) (hq : q < pf.code.size) :
    (scanS g pf.code q).sched.isSome = true ∧
    ∃ pt, (scanS g pf.code pf.code.size).pts[(scanS g pf.code q).pts.size]? = some pt ∧ pt.k = .post := by
  cases hs with
  | ifElse bt hc hne =>
    rcases (hn.if_ pc bt hc).2 with h | ⟨_, _, hel, _⟩
    · exact absurd h hne
    · have hlt := lt_of_get pf.code _ _ hel
      have hc' : pf.code[elseAt pf pc] = .else_ := by simpa [hlt] using hel
      apply post_of_sched g pf hn _ hq Fee.zero
      rw [sched_scan g pf.code _ hlt, hc']; rfl
  | ifEnd bt hc _ =>
    exact post_of_sched g pf hn _ hq _ (fwd_end g pf hn pc _ hc (Or.inl ⟨bt, rfl⟩))
  | else_ o rest hc henc =>
    obtain ⟨o', rest', bt, henc', ho, _, _, _⟩ := hn.else_ pc hc
    rw [henc] at henc'; cases henc'
    exact post_of_sched g pf hn _ hq _ (fwd_end g pf hn o _ ho (Or.inl ⟨bt, rfl⟩))
  | br l _ hc hbt =>
    have hpc := lt_of_get pf.code pc _ hc
    have hc' : pf.code[pc] = .br l := by simpa [hpc] using hc
    unfold brTarget at hbt
    cases ho : (openAt pf.code pc)[l]? with
    | none => rw [ho] at hbt; cases hbt
    | some o =>
      rw [ho] at hbt; cases hbt
      exact target_branch g pf hn pc l o hpc (by rw [hc']; simp [brLabels]) ho hq
  | brIf l _ hc hbt =>
    have hpc := lt_of_get pf.code pc _ hc
    have hc' : pf.code[pc] = .brIf l := by simpa [hpc] using hc
    unfold brTarget at hbt
    cases ho : (openAt pf.code pc)[l]? with
    | none => rw [ho] at hbt; cases hbt
    | some o =>
      rw [ho] at hbt; cases hbt
      exact target_branch g pf hn pc l o hpc (by rw [hc']; simp [brLabels]) ho hq
  | brTable ls d l _ hc hmem hbt =>
    have hpc := lt_of_get pf.code pc _ hc
    have hc' : pf.code[pc] = .brTable ls d := by simpa [hpc] using hc
    unfold brTarget at hbt
    cases ho : (openAt pf.code pc)[l]? with
    | none => rw [ho] at hbt; cases hbt
    | some o =>
      rw [ho] at hbt; cases hbt
      exact target_branch g pf hn pc l o hpc (by rw [hc']; simp [brLabels]; simpa using hmem) ho hq

theorem succ_bounds (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (pc q : Nat)
    (hs : Succ pf (openAt pf.code) pc q true) : 0 < q ∧ q ≤ pf.code.size := by
  have lab : ∀ (l o : Nat), (openAt pf.code pc)[l]? = some o → 0 < labTarget pf o ∧ labTarget pf o ≤ pf.code.size := by
    intro l o hl
    obtain ⟨_, i, hi, hopn⟩ := openAt_mem pf.code pc o (List.mem_of_getElem? hl)
    obtain ⟨_, _, hend, _, _⟩ := hn.opener o i hi hopn
    have h1 := lt_of_get pf.code _ _ hend
    have h2 := lt_of_get pf.code _ _ hi
    unfold labTarget; rw [hi]; split <;> omega
  cases hs with
  | ifElse bt hc hne =>
    rcases (hn.if_ pc bt hc).2 with h | ⟨_, _, hel, _⟩
    · exact absurd h hne
    · have := lt_of_get pf.code _ _ hel; omega
  | ifEnd bt hc _ =>
    obtain ⟨_, _, hend, _, _⟩ := hn.opener pc _ hc rfl
    have := lt_of_get pf.code _ _ hend; omega
  | else_ o rest hc henc =>
    obtain ⟨o', rest', bt, henc', ho, _, _, _⟩ := hn.else_ pc hc
    rw [henc] at henc'; cases henc'
    obtain ⟨_, _, hend, _, _⟩ := hn.opener o _ ho rfl
    have := lt_of_get pf.code _ _ hend; omega
  | br l _ hc hbt =>
    unfold brTarget at hbt
    cases ho : (openAt pf.code pc)[l]? with
    | none => rw [ho] at hbt; cases hbt
    | some o => rw [ho] at hbt; cases hbt; exact lab l o ho
  | brIf l _ hc hbt =>
    unfold brTarget at hbt
    cases ho : (openAt pf.code pc)[l]? with
    | none => rw [ho] at hbt; cases hbt
    | some o => rw [ho] at hbt; cases hbt; exact lab l o ho
  | brTable ls d l _ hc _ hbt =>
    unfold brTarget at hbt
    cases ho : (openAt pf.code pc)[l]? with
    | none => rw [ho] at hbt; cases hbt
    | some o => rw [ho] at hbt; cases hbt; exact lab l o ho

theorem cs_le (cfg : NearCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code))
    (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) :
    ∀ len s, s + len ≤ pf.code.size →
      cfg.regularOpCost * cs pf s len ≤ sumL (fun t => (Mf cfg.gas pf.code t).fee.c) s len := by
  intro len
  induction len with
  | zero => intro s _; simp [cs, sumL]
  | succ len ih =>
    intro s h
    have h1 := ih (s + 1) (by omega)
    have h2 := Mf_fee cfg.gas pf hn s (by omega) hl
    simp only [cs, sumL, Nat.mul_add]
    exact Nat.add_le_add h2 h1

theorem segQ_main (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (hpos : 0 < pf.code.size) :
    let Q := (optimize (scanS g pf.code pf.code.size).pts true).toList
    SegQ (fun t => (Mf g pf.code t).fee.c) (fun t => (Mf g pf.code t).k) pf.code.size Q 0 ∧
    ∀ t, 1 ≤ t → t < pf.code.size → starter (Mf g pf.code t).k = true → ∃ q ∈ Q, q.off = t := by
  intro Q
  have hQ : Q = optL m2 ((List.range pf.code.size).map (Mf g pf.code)) := by
    show (optimize (scanS g pf.code pf.code.size).pts true).toList = _
    rw [optimize_eq, optimizeWith_eq, optimizeWith_eq, raw_eq, optL_blocks _ 0]
    · rw [List.map_map]; rfl
    · intro t ht
      simp only [List.length_map, List.length_range] at ht
      simp only [List.getElem_map, List.getElem_range]
      have F := offFacts g pf hn t ht
      exact ⟨by rw [F.off2]; omega, F.bok⟩
  have hr : (List.range pf.code.size).map (Mf g pf.code) =
      Mf g pf.code 0 :: (List.range' 1 (pf.code.size - 1)).map (Mf g pf.code) := by
    rw [List.range_eq_range', show pf.code.size = (pf.code.size - 1) + 1 by omega, List.range'_succ]
    simp
  rw [hQ, hr]
  simp only [optL]
  have h0 := (offFacts g pf hn 0 hpos).off
  have := pass2 (fun t => (Mf g pf.code t).fee.c) (fun t => (Mf g pf.code t).k) pf.code.size
    ((List.range' 1 (pf.code.size - 1)).map (Mf g pf.code)) 1 (Mf g pf.code 0)
    (by
      intro t ht
      have ht' : t < pf.code.size - 1 := by simpa using ht
      simp only [List.getElem_map, List.getElem_range', Nat.one_mul]
      exact ⟨(offFacts g pf hn _ (by omega)).off, trivial, trivial⟩)
    (by simp; omega) (by omega) (by rw [h0]; simp [sumL]) (by rw [h0]; exact id)
  rw [h0] at this
  exact this

theorem wc_gasTable' (cfg : NearCfg) (pf : PFunc)
    (hn : NestOK pf (openAt pf.code))
    (hg : pf.gas = gasTable cfg.gas pf.code true)
    (hr : 0 < cfg.regularOpCost) (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) :
    WC cfg pf (openAt pf.code) := by
  have hgas := gasTable_eq cfg.gas pf.code
  rw [← hg] at hgas
  have hsize : pf.gas.size = pf.code.size := by rw [hgas, table_size]; simp
  have SQ := segQ_main cfg.gas pf hn
  generalize hQ : (optimize (scanS cfg.gas pf.code pf.code.size).pts true).toList = Q at hgas SQ
  have SP : 0 < pf.code.size → SegP (fun t => (Mf cfg.gas pf.code t).fee.c) (fun t => (Mf cfg.gas pf.code t).k)
      pf.code.size Q 0 := fun h => SegQ_props _ _ _ Q 0 (SQ h).1
  let start : Nat → Prop := fun t => (∃ q ∈ Q, q.off = t) ∨ t = pf.code.size
  -- the group of a start point extends at least to any gap-free prefix
  have reach : ∀ q ∈ Q, ∀ nx len, 0 < pf.code.size → q.off < nx → (nx = pf.code.size ∨ ∃ q' ∈ Q, q'.off = nx) →
      q.off + len ≤ pf.code.size → (∀ t, q.off < t → t < q.off + len → ¬ start t) → len ≤ nx - q.off := by
    intro q hq nx len _ h1 h2 h3 h4
    rcases Nat.lt_or_ge (nx - q.off) len with h | h
    · exfalso
      apply h4 nx h1 (by omega)
      rcases h2 with h2 | h2
      · exact Or.inr h2
      · exact Or.inl h2
    · exact h
  have startOf : ∀ t, 1 ≤ t → t < pf.code.size → Live pf (openAt pf.code) t →
      (scanS cfg.gas pf.code t).sched.isSome = true →
      (∃ pt, (scanS cfg.gas pf.code pf.code.size).pts[(scanS cfg.gas pf.code t).pts.size]? = some pt ∧
        pt.k = .post) → start t := by
    intro t h1 h2 hlv hs hp
    exact Or.inl ((SQ (by omega)).2 t h1 h2 (Mf_starter cfg.gas pf hn t hlv h2 hs hp))
  apply wc_of_GT hn (start := start)
  refine ⟨?_, Or.inr rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos pf.code.size with h | h
    · exact Or.inr h.symm
    · obtain ⟨q, rest, hq, hqo⟩ := SegQ_head _ _ _ Q 0 (SQ h).1
      exact Or.inl ⟨q, by rw [hq]; simp, hqo⟩
  · intro a e he
    rw [hgas] at he
    rcases table_some pf.code.size Q _ a e he with h | ⟨q, hq, h1, _⟩
    · obtain ⟨_, e2⟩ := Array.getElem?_eq_some_iff.mp h; simp at e2
    · exact Or.inl ⟨q, hq, h1⟩
  · intro s k fee len hge hlen hgap
    have hs : s < pf.code.size := by
      rw [← hsize]; exact (Array.getElem?_eq_some_iff.mp hge).1
    rw [hgas] at hge
    rcases table_some pf.code.size Q _ s _ hge with h | ⟨q, hq, h1, h2, _⟩
    · obtain ⟨_, e2⟩ := Array.getElem?_eq_some_iff.mp h; simp at e2
    · obtain ⟨_, _, P3⟩ := SP (by omega)
      obtain ⟨_, nx, u1, u2, u3, _, u5⟩ := P3 q hq
      have hle := reach q hq nx len (by omega) u1 u5 (by rw [h1]; exact hlen) (by rw [h1]; exact hgap)
      have e1 : fee = q.fee := (Prod.mk.inj h2).2
      rw [e1, u3, h1]
      rw [h1] at hle
      exact Nat.le_trans (cs_le cfg pf hn hl len s hlen) (sumL_mono _ _ _ _ hle)
  · intro s len hst hlv hne hlen hgap
    rcases Nat.eq_zero_or_pos len with h0 | hpos
    · subst h0; rfl
    have hs : s < pf.code.size := by omega
    rcases hst with ⟨q, hq, hqo⟩ | hst
    · obtain ⟨_, _, P3⟩ := SP (by omega)
      obtain ⟨hk, nx, u1, u2, u3, _, u5⟩ := P3 q hq
      have hle := reach q hq nx len (by omega) u1 u5 (by rw [hqo]; exact hlen) (by rw [hqo]; exact hgap)
      have hz : q.fee = Fee.zero := by
        by_cases hk' : q.k = .unreach
        · rw [hqo] at hk; exact absurd (hk hk') (Mf_not_unreach cfg.gas pf hn s hlv hs)
        · by_cases hf : q.fee = Fee.zero
          · exact hf
          · have := table_hit pf.code.size Q (Array.replicate pf.code.size none) (SP (by omega)).2.1 (by simp) q hq hk' hf (by omega)
            rw [← hgas, hqo] at this
            exact absurd this (hne _)
      have hc : q.fee.c = 0 := by rw [hz]; rfl
      rw [hc, hqo] at u3
      rw [hqo] at hle
      have h1 := cs_le cfg pf hn hl len s hlen
      have h2 := sumL_mono (fun t => (Mf cfg.gas pf.code t).fee.c) s _ _ hle
      have h3 : cfg.regularOpCost * cs pf s len = 0 := by omega
      rcases Nat.mul_eq_zero.mp h3 with h | h
      · omega
      · exact h
    · omega
  · intro pc q hlv hs
    obtain ⟨hq0, hqn⟩ := succ_bounds pf hn pc q hs
    rcases Nat.lt_or_ge q pf.code.size with h | h
    · obtain ⟨a1, a2⟩ := jump_start cfg.gas pf hn pc q hs h
      exact startOf q hq0 h (Live.step pc q true hlv hs) a1 a2
    · exact Or.inr (by omega)
  · intro pc i hlv hc hi
    have hpc := lt_of_get pf.code pc i hc
    have hft : fallsThrough i = true := by cases i <;> simp_all [isCallI, fallsThrough]
    rcases live_fall hn hlv hc hft with hl' | he
    · rcases Nat.lt_or_ge (pc + 1) pf.code.size with h | h
      · have hci : pf.code[pc] = i := by simpa [hpc] using hc
        have hs : (scanS cfg.gas pf.code (pc + 1)).sched = some (.post, Fee.zero) := by
          rw [sched_scan cfg.gas pf.code pc hpc, hci, schedOf_call _ _ _ hi]
        obtain ⟨a1, a2⟩ := post_of_sched cfg.gas pf hn _ h _ hs
        exact startOf _ (by omega) h hl' a1 a2
      · exact Or.inr (by omega)
    · exact Or.inr he


end NearSpecV3.Wasm.FuelGas

namespace NearSpecV3.Wasm

/-- O-W4, static half: finite-wasm's instrumentation table pays for every costly instruction before
it runs. `hw` and `he` are not needed beyond `hn` (the nesting they imply). -/
theorem wc_gasTable (cfg : NearCfg) (pf : PFunc) (_hw : WellNested pf.code)
    (hn : NestOK pf (openAt pf.code))
    (_he : matchBlocks pf.code = (pf.endOf, pf.elseOf))
    (hg : pf.gas = gasTable cfg.gas pf.code true)
    (hr : 0 < cfg.regularOpCost) (hl : cfg.regularOpCost ≤ cfg.linearOpBaseCost) :
    WC cfg pf (openAt pf.code) :=
  FuelGas.wc_gasTable' cfg pf hn hg hr hl

end NearSpecV3.Wasm
