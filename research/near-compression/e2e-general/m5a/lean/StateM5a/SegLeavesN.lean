import StateM5a.StcSound

/-!
# StateM5a.SegLeavesN — B-T3: `SegLeaves` restated (finding B3-1) and reduced to the leaf content

**Finding B3-1 (B-T2's `WsBridge.SegLeaves` is too strong).** `SegLeaves` quantified over *every*
entry list with `wsLen` `Ok` entries. With a repeated key, `updE w` updates every copy while the
segment's rows touch one leaf per key (`WsSeg.ws_final` needs distinct key digests among the
touched leaves, `hkd`), so the premise is false for such lists and could not be discharged. Two
facts the circuit argument needs were also missing: the list's view root is the input root (the
touched leaves' old digests are its leaves, `m5tSeg_ws`). **`SegLeavesN`** adds both (distinct keys,
`wsRoot es = R_in`); `ws_moves_segN` / `WsMovesN` / `st_stepN` / **`stHalf_segN`** are the B-T2/B-T3
results over it, with the view's working set key-distinct as a premise (`((P.wsOf v).map
Prod.fst).Nodup`: lane E's `keysOf` is the chunk's key set — an obligation on the view, not on the
circuit).

**The reduction (`segLeavesN_of`).** `SegLeavesN` follows from two per-index facts about the
segment's rows, both content-level (the M5b chain `write_sent` → `WRITE` → `WSA` memory chain →
`WSL`, restated per template; open):

* `LastNew`: at an index `i < |es|`, a touching `WSL` row of the latest internal segment writes the
  leaf digest of `(upd es)[i]`;
* `Untouched`: an index no row touches keeps its entry (`(upd es)[i] = es[i]`).

The Merkle-level part is proved here: `wsAt_cases` (index by index, `wsAt s` holds the initial leaf
or the new digest of a latest touching row) and the padding indices (`l.i < wsLen`, `wsl_ok_seg`).

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace StateM5a.SegLeavesN

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Sha512If StateM5a.WsBridge StateM5a.StHalfC
open StateM5a.TmplSeg StateM5a.TmplWsx StateM5a.WsDecode StateM5a.WsDecode2 StateM5a.WsBus StateM5a.Merkle StateM5a.Bus
open StateM5a.StateView (Entry StViewParams wsRoot)
open StateM5a.WsSeg (wsAt)

/-! ## `wsAt`, index by index -/

section Cases
variable {Kd V α : Type} {wsl : List (WslRow Kd V α)} {ws0 : List α}

/-- **What `wsAt s` holds at `i`** (`i` inside the list): the initial leaf (no row of a segment
`< s` touches `i`), or the new digest of a touching row whose segment is the latest `< s` among the
rows touching `i`. -/
theorem wsAt_cases (i : Nat) (hi : i < ws0.length) : ∀ s,
    ((wsAt wsl ws0 s)[i]? = ws0[i]? ∧ ∀ l ∈ wsl, l.i = i → s ≤ l.seg) ∨
    ∃ l ∈ wsl, l.i = i ∧ l.seg < s ∧ (∀ l' ∈ wsl, l'.i = i → l'.seg < s → l'.seg ≤ l.seg) ∧
      (wsAt wsl ws0 s)[i]? = some l.dgN
  | 0 => .inl ⟨rfl, fun _ _ _ => Nat.zero_le _⟩
  | s + 1 => by
    have hsome : ∃ a, (wsAt wsl ws0 s)[i]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by rw [WsSeg.wsAt_length rfl]; exact hi)⟩
    obtain ⟨a, ha⟩ := hsome
    have e : (wsAt wsl ws0 (s + 1))[i]? = some ((WsSeg.touch wsl s i).getD a) := by
      show (WsSeg.segApply wsl s (wsAt wsl ws0 s))[i]? = _
      rw [WsSeg.segApply_get, ha]; rfl
    cases hf : wsl.find? (fun x => decide (x.seg = s ∧ x.i = i)) with
    | some l =>
      have hl := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [decide_eq_true_eq] at hp
      have ht : WsSeg.touch wsl s i = some l.dgN := by unfold WsSeg.touch; rw [hf]; rfl
      right
      exact ⟨l, hl, hp.2, by omega, fun l' _ _ h => by omega, by rw [e, ht]; rfl⟩
    | none =>
      have hn := List.find?_eq_none.1 hf
      have hne : ∀ l ∈ wsl, l.i = i → l.seg ≠ s := fun l hl hli hs => hn l hl (by simp [hs, hli])
      have ht : WsSeg.touch wsl s i = none := by unfold WsSeg.touch; rw [hf]; rfl
      rw [ht] at e
      rcases wsAt_cases i hi s with ⟨h0, hlt⟩ | ⟨l, hl, hli, hs, hmax, he⟩
      · left
        refine ⟨by rw [e, ← h0, ha]; rfl, fun l hl hli => ?_⟩
        have := hlt l hl hli; have := hne l hl hli; omega
      · right
        refine ⟨l, hl, hli, by omega, fun l' hl' e1 e2 => ?_, by rw [e]; rw [ha] at he; rw [← he]; rfl⟩
        have := hne l' hl' e1
        exact hmax l' hl' e1 (by omega)

end Cases

/-! ## The restated premise and its reduction -/

section Seg
variable (P : StViewParams) {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}

/-- The entry lists the segment acts on: `wsLen` `Ok` entries with distinct keys and view root `R_in`. -/
def Inputs (pub : List Fp) (es : List Entry) : Prop :=
  es.length = WsLen.wsLen pub ∧ (∀ e ∈ es, e.Ok) ∧ (es.map Prod.fst).Nodup ∧
    wsRoot P es = toB (pubDig pub PUB_WSA)

/-- **The segment's leaf content, restated (B3-1).** -/
def SegLeavesN (D : Nat) (tr : Trace Fp) (pub : List Fp) (upd : List Entry → List Entry) : Prop :=
  ∀ es, Inputs P pub es →
    wsAt (wsl (trS tr) pub) (leavesDig P D es) (ev tr 7 0 pub (Wsx.c "sb")) = leavesDig P D (upd es)

/-- (open, content) A latest touching row at an index inside the list writes the updated entry's leaf. -/
def LastNew (tr : Trace Fp) (pub : List Fp) (upd : List Entry → List Entry) : Prop :=
  ∀ es, Inputs P pub es → ∀ l ∈ wsl (trS tr) pub, l.i < es.length → l.seg < ev tr 7 0 pub (Wsx.c "sb") →
    (∀ l' ∈ wsl (trS tr) pub, l'.i = l.i → l'.seg < ev tr 7 0 pub (Wsx.c "sb") → l'.seg ≤ l.seg) →
      ((upd es).map (leafDig P))[l.i]? = some l.dgN

/-- (open, content) An index no row touches keeps its entry. -/
def Untouched (tr : Trace Fp) (pub : List Fp) (upd : List Entry → List Entry) : Prop :=
  ∀ es, Inputs P pub es → ∀ i, i < es.length →
    (∀ l ∈ wsl (trS tr) pub, l.i = i → ev tr 7 0 pub (Wsx.c "sb") ≤ l.seg) → (upd es)[i]? = es[i]?

theorem leavesDig_get_lt (es : List Entry) {i : Nat} (hi : i < es.length) :
    (leavesDig P D es)[i]? = (es.map (leafDig P))[i]? := by
  unfold leavesDig
  rw [List.getElem?_append_left (by simp; exact hi)]

theorem leavesDig_get_ge (es : List Entry) {i : Nat} (hi : es.length ≤ i) :
    (leavesDig P D es)[i]? = (List.replicate (2 ^ D - es.length) z0)[i - es.length]? := by
  unfold leavesDig
  rw [List.getElem?_append_right (by simp; exact hi), List.length_map]

/-- **The reduction**: `SegLeavesN` from the two per-index content facts and `l.i < wsLen`. -/
theorem segLeavesN_of {upd : List Entry → List Entry} (hupd : ∀ es, (upd es).length = es.length)
    (hwl : ∀ l ∈ wsl (trS tr) pub, l.i < WsLen.wsLen pub)
    (hLN : LastNew P tr pub upd) (hU : Untouched P tr pub upd) : SegLeavesN P D tr pub upd := by
  intro es hin
  have hlen := hin.1
  have hL : (leavesDig P D (upd es)).length = (leavesDig P D es).length := by
    simp [leavesDig, hupd]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < (leavesDig P D es).length
  · rcases wsAt_cases (wsl := wsl (trS tr) pub) i hi (ev tr 7 0 pub (Wsx.c "sb")) with
      ⟨h0, hlt⟩ | ⟨l, hl, hli, hs, hmax, he⟩
    · rw [h0]
      by_cases hie : i < es.length
      · rw [leavesDig_get_lt P es hie, leavesDig_get_lt P (upd es) (by rw [hupd]; exact hie),
          List.getElem?_map, List.getElem?_map, hU es hin i hie hlt]
      · rw [leavesDig_get_ge P es (by omega), leavesDig_get_ge P (upd es) (by rw [hupd]; omega), hupd]
    · rw [he]
      have hie : l.i < es.length := by rw [hlen]; exact hwl l hl
      subst hli
      rw [leavesDig_get_lt P (upd es) (by rw [hupd]; exact hie)]
      exact (hLN es hin l hl hie hs hmax).symm
  · rw [List.getElem?_eq_none (by rw [WsSeg.wsAt_length rfl]; omega), List.getElem?_eq_none (by omega)]

/-! ## The B-T2 / B-T3 results over `SegLeavesN` -/

/-- The view's working-set step over key-distinct lists with the input root. -/
def WsMovesN (n : Nat) (RIn ROut : ArenaCore.Bytes) (upd : List Entry → List Entry) : Prop :=
  ∀ es : List Entry, es.length = n → (∀ e ∈ es, e.Ok) → (es.map Prod.fst).Nodup → wsRoot P es = RIn →
    wsRoot P (upd es) = ROut

theorem ws_moves_segN (hH : Holds (segAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG)
    (hC : Sha512IfContract cW ((busList (segAir D extra nb np) tr pub B_IF384 true).map decIf))
    (hD1 : 1 ≤ D) (hD : D ≤ 20) (hCR : NodeCR cW) (hdep : P.depth = 24)
    (hz : toB (zD D) = zd StateView.nodeH StateView.zero48 D) (hn : WsLen.wsLen pub ≤ 2 ^ D)
    {upd : List Entry → List Entry} (hupd : ∀ es, (upd es).length = es.length)
    (hSL : SegLeavesN P D tr pub upd) :
    WsMovesN P (WsLen.wsLen pub) (toB (pubDig pub PUB_WSA)) (toB (pubDig pub PUB_WSB)) upd := by
  intro es hlen hok hnd hroot
  have hle : es.length ≤ 2 ^ D := hlen ▸ hn
  have hDd : D ≤ P.depth := by omega
  obtain ⟨r, hr, he⟩ := wsRoot_dig P D hDd es hle
  have hzD : zD D = zd (Sha512If.nodeH cW) z0 D := by
    apply toB_inj; rw [hz, ← zd_map _ _ toB hnode, toB_z0]
  have hin : extUp (Sha512If.nodeH cW) (zD D) 0 (24 - D) r = pubDig pub PUB_WSA := by
    apply toB_inj
    rw [hzD, extUp_shift, ← hroot, he, hdep]
  obtain ⟨r', hr', hout⟩ := seg_rin_rout hH hx cW_ok hC hD1 hD hCR
    (leavesDig_length P D es hle) hr hin
  rw [hSL es ⟨hlen, hok, hnd, hroot⟩] at hr'
  have hle' : (upd es).length ≤ 2 ^ D := by rw [hupd]; exact hle
  obtain ⟨r'', hr'', he'⟩ := wsRoot_dig P D hDd (upd es) hle'
  rw [hr''] at hr'
  cases hr'
  rw [he', ← hout, hzD, extUp_shift, hdep]

/-- `StHalfC.st_step` over `WsMovesN` (the input state's working set has distinct keys). -/
theorem st_stepN {r r' RIn ROut : ArenaCore.Bytes} {n : Nat} {mi mo : StMeta} {upd : List Entry → List Entry}
    (hS : StcOK r r' RIn ROut n mi mo) (hW : WsMovesN P n RIn ROut upd)
    (hupd : ∀ es, (upd es).length = es.length) (v v' : NearSpecV3.E2E.Bnd.StV) (hv : StateView.stD P v = r)
    (hnd : ((P.wsOf v).map Prod.fst).Nodup)
    (hr : StepRel P upd mo v v') : NearSpecV3.E2E.Bnd.Sha384Coll ∨ (StateView.stD P v' = r' ∧ metaOf P v = mi) := by
  obtain ⟨c, hcw, hcd, hcws, hcn, hct, hcr, hr'⟩ := hS
  obtain ⟨hf, hf', hws, htr, hix, hmo⟩ := hr
  simp only [StateView.stD, hf, ite_true] at hv
  classical
  by_cases hs : (StateView.commitOf P v).ser = c.ser
  · have e := StateView.ser_inj _ _ (StateView.commitOf_wf P v hf) hcw hs
    subst e
    have hroot : wsRoot P (upd (P.wsOf v)) = ROut :=
      hW _ hcn (P.fits_ws_ok v hf) hnd hcws
    have hc' : StateView.commitOf P v' = close (StateView.commitOf P v) ROut mo := by
      simp only [StateView.commitOf, close, ← hmo, metaOf, hws, hroot, hupd, htr, hix]
    refine .inr ⟨?_, ?_⟩
    · simp only [StateView.stD, hf', ite_true, hc', hr']
    · cases mi with
      | mk t rs => exact (StMeta.mk.injEq _ _ _ _).mpr ⟨hct, hcr⟩
  · exact .inl ⟨_, _, hs, by rw [hv, hcd]⟩

end Seg

/-! ## Lane B's state half of a STATE leaf over `SegLeavesN` -/

section Half
open StateM5a.StcSound
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}

/-- **`StcSound.stHalf_seg` over the restated premise** (B3-1): with `LastNew` / `Untouched` (the
leaf content, open) in place of `SegLeaves`, and the view's working set key-distinct. -/
theorem stHalf_segN (Pv : StViewParams) (hH : Holds (segAir D (stcTables D ++ extra) nb np) pub tr)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG)
    (hxs : ∀ T ∈ extra, ∀ i ∈ T.interactions, ¬ (i.bus = B_SRNG ∧ i.send = true))
    (hC : Sha512IfContract cW ((busList (segAir D (stcTables D ++ extra) nb np) tr pub B_IF384 true).map decIf))
    (hD1 : 1 ≤ D) (hD : D ≤ 20) (hCR : NodeCR cW) (hdep : Pv.depth = 24)
    (hz : toB (zD D) = zd StateView.nodeH StateView.zero48 D)
    {upd : List Entry → List Entry} (hupd : ∀ es, (upd es).length = es.length)
    (hLN : LastNew Pv tr pub upd) (hU : Untouched Pv tr pub upd)
    {r : Nat} (hr : r < tr.height 8) (hA : ev tr 8 r pub (Stc.c "act") = 1)
    (v v' : NearSpecV3.E2E.Bnd.StV) (hv : StateView.stD Pv v = decR (qv tr 8 r pub))
    (hnd : ((Pv.wsOf v).map Prod.fst).Nodup)
    (hrel : StepRel Pv upd (decM (qv tr 8 r pub)) v v') :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      (StateView.stD Pv v' = decR (av tr 8 r pub) ∧ metaOf Pv v = decM (av tr 8 r pub)) := by
  obtain ⟨hS, hn⟩ := stc_seg hH (fun T hT i hi => hxs T hT i hi) hC hD hr hA
  have hx' : ∀ T ∈ stcTables D ++ extra, ∀ i ∈ T.interactions,
      i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG := by
    intro T hT
    rcases List.mem_append.1 hT with h | h
    · exact stc_buses D T h
    · exact hx T h
  have hwl : ∀ l ∈ wsl (trS tr) pub, l.i < WsLen.wsLen pub :=
    fun l hl => (wsl_ok_seg hH hx' hD1 hD l hl).2
  have hSL := segLeavesN_of (D := D) Pv hupd hwl hLN hU
  have hW := ws_moves_segN Pv hH hx' hC hD1 hD hCR hdep hz hn hupd hSL
  exact st_stepN Pv hS hW hupd v v' hv hnd hrel

end Half

#print axioms wsAt_cases
#print axioms segLeavesN_of
#print axioms ws_moves_segN
#print axioms st_stepN
#print axioms stHalf_segN

end StateM5a.SegLeavesN
