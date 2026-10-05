import ZkFormal.Bcs.StarkParse

/-!
# ZkFormal.Bcs.StarkChain — L4's transcript chain certifies a `Bcs.Chain`
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace ZkFormal.Bcs.Adapter

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

theorem evalT_starkH {tbl : Table} (wf : TableWF tbl) (m : Bytes) :
    evalT tbl (Stark.H m) = tbl.lookup m := by
  unfold Stark.H
  simp only [evalT]
  cases h : tbl.lookup m with
  | none => rfl
  | some y => simp only [evalT, Stark.fit32_of_length (wf.lookup_length h)]

theorem evalT_starkWH_eq {tbl : Table} (wf : TableWF tbl) (tag : UInt8) (m : Bytes) :
    evalT tbl (Stark.WH tag m) = evalT tbl (wh (tag :: m)) := by
  unfold Stark.WH Stark.H wh
  simp only [OracleComp.bind, evalT]
  have e0 : whq (tag :: m) 0 = tag :: 1 :: m := rfl
  have e1 : whq (tag :: m) 1 = tag :: 2 :: m := rfl
  rw [e0, e1]
  cases ha : tbl.lookup (tag :: 1 :: m) with
  | none => rfl
  | some a =>
    simp only
    cases hb : tbl.lookup (tag :: 2 :: m) with
    | none => rfl
    | some b =>
      simp only [evalT, Stark.fit32_of_length (wf.lookup_length ha),
        Stark.fit32_of_length (wf.lookup_length hb)]

theorem evalT_starkWH {tbl : Table} (wf : TableWF tbl) (tag : UInt8) (m u : Bytes) :
    evalT tbl (Stark.WH tag m) = some u ↔ WHin tbl (tag :: m) u := by
  rw [evalT_starkWH_eq wf, evalT_wh]

theorem whin_take32 {tbl : Table} (wf : TableWF tbl) {m a b : Bytes}
    (ha : tbl.lookup (whq m 0) = some a) : (a ++ b).take 32 = a :=
  List.take_left' (wf.lookup_length ha)

section
variable {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]

/-- A parsed slot, the entry L4's chain makes of it, and the verifier view. -/
inductive SlotRel : Stark.PSlot K → Stark.Entry K Bytes → EntryV → Prop
  | msg (vs : List (Stark.PartV K Bytes)) (raw : Bytes) :
      SlotRel (.msg vs raw) (.msg vs) (.msg (Stark.rootsOf vs) (Stark.clearOf vs raw))
  | chal (ood : Bool) (y : Bytes) :
      SlotRel (.chal ood)
        (.chal (if ood then Stark.decodeOod (F := F) y else Stark.decodeChal (F := F) y)) (.chal y)

inductive Rel3 {α β γ : Type} (R : α → β → γ → Prop) : List α → List β → List γ → Prop
  | nil : Rel3 R [] [] []
  | cons {a b c as bs cs} : R a b c → Rel3 R as bs cs → Rel3 R (a :: as) (b :: bs) (c :: cs)

/-- Roots of every message are 64-byte and fewer than 256. -/
def RootsOk (ps : List (Stark.PSlot K)) : Prop :=
  ∀ vs raw, Stark.PSlot.msg vs raw ∈ ps →
    (∀ r ∈ Stark.rootsOf vs, r.length = 64) ∧ (Stark.rootsOf vs).length < 256

/-- **Chain refinement.** -/
theorem chain_refine {tbl : Table} (wf : TableWF tbl) (ctx cb : Bytes) :
    ∀ (ps : List (Stark.PSlot K)) (d : Bytes) (es0 : List EntryV) (entries : List (Stark.Entry K Bytes))
      (dfin : Bytes), RootsOk ps → Chain tbl ctx cb es0 d →
      evalT tbl (Stark.chain (F := F) d ps) = some (entries, dfin) →
      ∃ es, Rel3 (SlotRel (F := F)) ps entries es ∧ Chain tbl ctx cb (es0 ++ es) dfin
  | [], d, es0, entries, dfin, _, hch, h => by
    simp only [Stark.chain, evalT, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], .nil, by simpa using hch⟩
  | .msg vs raw :: ss, d, es0, entries, dfin, hok, hch, h => by
    simp only [Stark.chain, evalT_bind] at h
    cases hw : evalT tbl (Stark.WH Stark.tagAbs (Stark.absBody d (Stark.rootsOf vs) (Stark.clearOf vs raw))) with
    | none => rw [hw] at h; cases h
    | some d' =>
      rw [hw] at h
      simp only [Option.bind_some] at h
      cases hc : evalT tbl (Stark.chain (F := F) d' ss) with
      | none => rw [hc] at h; cases h
      | some res =>
        rw [hc] at h
        simp only [Option.bind_some, evalT, Option.some.injEq] at h
        obtain ⟨ents, df⟩ := res
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hok1 := hok vs raw List.mem_cons_self
        have hwh := (evalT_starkWH wf _ _ _).mp hw
        have hch' : Chain tbl ctx cb (es0 ++ [.msg (Stark.rootsOf vs) (Stark.clearOf vs raw)]) d' :=
          Chain.msg _ _ _ _ _ hch hok1.1 hok1.2 hwh
        obtain ⟨es, hrel, hfin⟩ := chain_refine wf ctx cb ss d' _ ents df
          (fun vs' raw' hm => hok vs' raw' (List.mem_cons_of_mem _ hm)) hch' hc
        exact ⟨_ :: es, .cons (.msg vs raw) hrel, by simpa using hfin⟩
  | .chal ood :: ss, d, es0, entries, dfin, hok, hch, h => by
    simp only [Stark.chain, evalT_bind] at h
    cases hw : evalT tbl (Stark.WH Stark.tagChal d) with
    | none => rw [hw] at h; cases h
    | some d' =>
      rw [hw] at h
      simp only [Option.bind_some] at h
      cases hc : evalT tbl (Stark.chain (F := F) d' ss) with
      | none => rw [hc] at h; cases h
      | some res =>
        rw [hc] at h
        simp only [Option.bind_some, evalT, Option.some.injEq] at h
        obtain ⟨ents, df⟩ := res
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨a, b, ha, hb, rfl⟩ := (evalT_starkWH wf _ _ _).mp hw
        have hch' : Chain tbl ctx cb (es0 ++ [.chal a]) (a ++ b) := Chain.chal _ _ _ _ hch ha hb
        obtain ⟨es, hrel, hfin⟩ := chain_refine wf ctx cb ss (a ++ b) _ ents df
          (fun vs' raw' hm => hok vs' raw' (List.mem_cons_of_mem _ hm)) hch' hc
        refine ⟨_ :: es, ?_, by simpa using hfin⟩
        have := SlotRel.chal (F := F) (K := K) ood a
        rw [whin_take32 wf ha]
        exact .cons this hrel

end

end ZkFormal.Bcs.Adapter
