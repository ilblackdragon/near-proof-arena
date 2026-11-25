import NearSpecV3.E2E.Glue

set_option linter.unusedVariables false

/-!
# E2E lane E, decision D-b: the finalize step as its own STATE leaf (state half: lane B's IF-FINAL)

M12 finding (2): the finalize step `yields yf yn 0 i k rs → done out` has no overlay at its output
(`finalizeStep` commits the overlay and hashes the trie), so the working-set glue of the STATE leaf
does not apply to it. Integrator decision D-b: **cut STATE before the finalize step** and prove the
finalize step in a STATE leaf whose state half is lane B's IF-FINAL (`m5b_final`); `FinStart` and
`Templates.lean` are unchanged (the finalize leaf's meaning is `MState`, one VM-free step).

## 1. `FinalizeAgree`, precisely, proved (`finalizeAgree`)

M12 named `FinalizeAgree : ∀ o r e a r', finalizeR o r e = .ok (a, r') → o.finalize = .ok a`. As
stated it is **false** (`finalizeAgree_unconditional_false`): the logged finalize
(`Ovl.finalizeL`) never reads `o.trie`; it re-reveals the pre-state lazily from the environment's
`preRoot` over `e.store`. The precise statement (`FinalizeAgreeT`) adds the two facts that make the
overlay's trie the one the lazy trie reveals: `HInv e.store` (every stored node hashes to its key)
and `o.trie = preT e.store e.preRoot` (the overlay's trie is the revealed pre-state). It is proved
from the spec library's `Logged.R_finalize` (lazy `applyChangesL` / `preTrieL` / `hashOfL` = eager
`Ovl.finalize`). On the engine's run both hold for the intake's overlay: `I.tMain` is
`revealAll store revealFuel prev_state_root` (`Intake`) and the overlay's trie is `I.tMain` along
every run (`OvlInv`); `FinTrieOK` names them for the opened configuration.

## 2. The finalize step's root (`fin_step_root`)

`estep P ⟨yields yf yn 0 i k rs, r⟩ = .ok ⟨done out, r'⟩` gives a run of `finalizeR (finO …)` with
result `out.root`, where `finO yf yn rs i` is the committed overlay `finalizeStep` hashes (the
yield index set if it moved, then `commit`); `finO_trie`: its trie is `rs.o.trie`;
`fin_step_committed`: `out.committed = some (sortKV (finO …).committed)`.

## 3. The finalize leaf (`fin_sound_relC`) and the two-mode STATE template (`tmplSoundRel8C_modes`)

The finalize leaf is a split leaf in the **relational** form (D-c): engine half (lane F's rows for
`finalizeStep` / `raceCheck`, `EngHalfRCOn` with the precondition `FinPre`: the input is a
`yields _ _ 0 _ _ _` position whose overlay satisfies `FinTrieOK`), state half (lane B's IF-FINAL,
`FinHalfB`: for the input's committed overlay `o` with `sortKV o.committed` = the bus's change
list, `o.finalize = .ok post` — `Glue.final_glue` from `m5b_final` when the IF's trie is `o.trie`),
glue (lane E, proved here: `fin_reqs`, from §§1–2). `W` = bytes: the input's `stRoot` and the
output's post-state root (`finW`).

`tmplSoundRel8C_modes`: a STATE AIR whose traces are those of a working-set leaf **or** a finalize
leaf (two sub-AIRs, e.g. selected by a public mode bit) is sound if each mode is.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace NearSpecV3.E2E.GlueFin
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.T1
open NearSpecV3.E2E.SB NearSpecV3.E2E.M8 NearSpecV3.Wasm NearSpecV3.E2E.Glue
open NearSpecV3.Successor NearSpecV3.Successor.StorageExecution

/-! ## 1. `FinalizeAgree` -/

/-- `finalizeR` returns the logged mirror's value (`Logged.LM.ev`) and changes only the recorder. -/
theorem finalizeR_run (o : Ovl) (r : Recording) (e : Env) :
    ∃ r'', finalizeR o r e = (Logged.LM.ev e.store e.preRoot o.finalizeL).map fun a => (a, r'') := by
  unfold finalizeR
  rw [Successor.logged_run_rr]
  simp only [Logged.SM.runR_eq, Logged.LM.ev]
  exact ⟨_, rfl⟩

/-- **`FinalizeAgree`, precisely**: on a hash-consistent store, if the overlay's trie is the
revealed pre-state of the environment's root, the logged lazy finalize returns the D2 finalize. -/
def FinalizeAgreeT : Prop :=
  ∀ (o : Ovl) (r : Recording) (e : Env) (a : Bytes) (r' : Recording),
    Logged.HInv e.store → o.trie = Logged.preT e.store e.preRoot →
      finalizeR o r e = .ok (a, r') → o.finalize = .ok a

/-- **`FinalizeAgreeT` holds.** -/
theorem finalizeAgree : FinalizeAgreeT := by
  intro o r e a r' hs ht h
  obtain ⟨r'', h0⟩ := finalizeR_run o r e
  rw [h0] at h
  have hR := Logged.R_finalize (root := e.preRoot) hs o
  unfold Logged.R at hR
  have hw : o.wt (Logged.preT e.store e.preRoot) = o := by
    obtain ⟨t, c, p, n⟩ := o
    simp only at ht
    simp only [Ovl.wt, ht]
  rw [hw] at hR
  rw [hR]
  cases hx : Logged.LM.ev e.store e.preRoot o.finalizeL with
  | error err => rw [hx] at h; cases h
  | ok v =>
    rw [hx] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    simp only [Except.map, h.1, id]

/-- **M12's unconditional `FinalizeAgree` fails** on any environment with the empty store and the
empty root: the lazy finalize returns the environment's root `[]`, the D2 finalize of an overlay
whose trie is the bare hash `[1]` returns `[1]`. -/
theorem finalizeAgree_fails (e : Env) (hs : e.store = .tip) (hp : e.preRoot = []) (r : Recording) :
    ∃ o a r', finalizeR o r e = .ok (a, r') ∧ o.finalize ≠ .ok a := by
  obtain ⟨r'', h0⟩ := finalizeR_run ⟨.hash [1], [], [], 0⟩ r e
  have hv : Logged.LM.ev e.store e.preRoot (Ovl.finalizeL ⟨.hash [1], [], [], 0⟩) = .ok [] := by
    rw [hs, hp]; rfl
  have hf : Ovl.finalize ⟨.hash [1], [], [], 0⟩ = .ok [1] := rfl
  refine ⟨⟨.hash [1], [], [], 0⟩, [], r'', by rw [h0, hv]; rfl, ?_⟩
  rw [hf]; intro h; cases h

/-! ## 2. The finalize step's root -/

theorem bindRes_ok {α β : Type} {x : Except String (α × Recording)} {f : α → Recording → Except String β}
    {b : β} (h : bindRes x f = .ok b) : ∃ a r1, x = .ok (a, r1) ∧ f a r1 = .ok b := by
  cases x with
  | ok p => obtain ⟨a, r1⟩ := p; exact ⟨a, r1, rfl, h⟩
  | error e => cases h

theorem bind_ok {α β : Type} {x : M α} {f : α → M β} {r : Recording} {e : Env} {b : β × Recording}
    (h : (x >>= f) r e = .ok b) : ∃ a r1, x r e = .ok (a, r1) ∧ f a r1 e = .ok b := by
  rw [M.bind_run] at h
  obtain ⟨a, r1, h1, h2⟩ := bindRes_ok h
  exact ⟨a, r1, h1, h2⟩

/-- The receipt state `finalizeStep` continues with (the yield index written if it moved). -/
def rsY (yf yn : Nat) (rs : RS) (i : Nat) : RS :=
  if i != yf then { rs with o := rs.o.set kYieldIdx (encIndices i yn) } else rs

/-- **The committed overlay `finalizeStep` hashes.** -/
def finO (yf yn : Nat) (rs : RS) (i : Nat) : Ovl := (rsY yf yn rs i).o.commit

theorem finO_trie (yf yn : Nat) (rs : RS) (i : Nat) : (finO yf yn rs i).trie = rs.o.trie := by
  unfold finO rsY; split <;> rfl

theorem finalizeStep_eq (env : Env) (yf yn : Nat) (rs : RS) (i : Nat) :
    finalizeStep env yf yn (rs, i) = finalizeStep env yf yn (rsY yf yn rs i, yf) := by
  unfold finalizeStep rsY
  cases h : (i != yf) <;> simp only [h, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true]

theorem finalizeStep_root0 {env e : Env} {yf yn : Nat} {rs : RS} {r r' : Recording}
    {out : MainOutD2} (h : finalizeStep env yf yn (rs, yf) r e = .ok (out, r')) :
    (∃ r1 r2, finalizeR rs.o.commit r1 e = .ok (out.root, r2)) ∧
      out.committed = some (sortKV rs.o.commit.committed) := by
  unfold finalizeStep at h
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false] at h
  obtain ⟨cong, r1, -, h⟩ := bind_ok h
  obtain ⟨bw, r2, -, h⟩ := bind_ok h
  obtain ⟨root, r3, hroot, h⟩ := bind_ok h
  obtain ⟨g, r4, -, h⟩ := bind_ok h
  obtain ⟨bu, r5, -, h⟩ := bind_ok h
  split at h
  · obtain ⟨u, r6, h6, -⟩ := bind_ok h
    cases h6
  · obtain ⟨recd, r6, -, h⟩ := bind_ok h
    cases h
    exact ⟨⟨r2, r3, hroot⟩, rfl⟩

/-- **A successful `finalizeStep`** ran `finalizeR` on `finO …` with result `out.root`, and its
committed list is the sorted committed overlay. -/
theorem finalizeStep_root {env e : Env} {yf yn : Nat} {rs : RS} {i : Nat} {r r' : Recording}
    {out : MainOutD2} (h : finalizeStep env yf yn (rs, i) r e = .ok (out, r')) :
    (∃ r1 r2, finalizeR (finO yf yn rs i) r1 e = .ok (out.root, r2)) ∧
      out.committed = some (sortKV (finO yf yn rs i).committed) := by
  rw [finalizeStep_eq] at h
  exact finalizeStep_root0 h

theorem raceCheck_ok {out out' : MainOutD2} {r r' : Recording} {e : Env}
    (h : raceCheck out r e = .ok (out', r')) : out' = out := by
  unfold raceCheck at h
  obtain ⟨s, r1, -, h⟩ := bind_ok h
  split at h
  · cases h
  · cases h; rfl

/-- **The finalize step**: from `yields _ _ 0` the engine step reaches `done out`, with `out.root`
the result of `finalizeR` on the committed overlay `finO …`. -/
theorem fin_step_root {P : Prog} {yf yn i k : Nat} {rs : RS} {r : Recording} {c' : EConf}
    (h : estep P ⟨.yields yf yn 0 i k rs, r⟩ = .ok c') :
    ∃ out, c'.pos = .done out ∧
      (∃ r1 r2, finalizeR (finO yf yn rs i) r1 P.env = .ok (out.root, r2)) ∧
      out.committed = some (sortKV (finO yf yn rs i).committed) := by
  unfold estep at h
  split at h
  · rename_i p r' hs
    cases h
    simp only [stepM] at hs
    obtain ⟨out1, r1, h1, hs⟩ := bind_ok hs
    obtain ⟨out0, r0, h0, h1⟩ := bind_ok h1
    cases hs
    rw [raceCheck_ok h1]
    exact ⟨out0, rfl, finalizeStep_root h0⟩
  · cases h

/-! ## 3. The finalize leaf -/

/-- The committed overlay of a finalize-step input (`yields _ _ 0 _ _ rs`). -/
def finOv : RConf → Option Ovl
  | .base (.eng _ ⟨.yields yf yn 0 i _ rs, _⟩) => some (finO yf yn rs i)
  | _ => none

/-- The post-state root of a finished engine configuration (the finalize leaf's output state
value: `MainOutD2.root`, the root lane B's IF-FINAL proves). -/
def finW : RConf → Bytes
  | .base (.eng _ ⟨.done out, _⟩) => out.root
  | _ => []

/-- **The finalize leaf's precondition** (the engine half establishes it): the input is a
finalize-step position, its overlay's trie is the intake environment's revealed pre-state over a
hash-consistent store, and the output is finished. -/
def FinPre (x x' : RConf) : Prop :=
  ∃ I yf yn i k rs r out r', x = .base (.eng I ⟨.yields yf yn 0 i k rs, r⟩) ∧
    x' = .base (.eng I ⟨.done out, r'⟩) ∧ Logged.HInv I.prog.env.store ∧
    rs.o.trie = Logged.preT I.prog.env.store I.prog.env.preRoot

/-- **The relation of the finalize leaf**: the output's post-state root is the D2 finalize of the
input's committed overlay, whose sorted change list is the bus traffic. -/
def FinRel (q : KV) (x x' : RConf) : Prop :=
  ∃ o, finOv x = some o ∧ q = sortKV o.committed ∧ o.finalize = .ok (finW x')

/-- The finalize leaf's join as a `SplitAir`: traffic = the sorted change list, value = bytes (the
input's `stRoot` / the output's post-state root). -/
def finAir {A : Airs8} (HoldsE : Bytes → LB → LB → KV → Bytes → Bytes → Prop)
    (HoldsS : KV → Bytes → Bytes → Prop)
    (joint : ∀ ctx b b' (tr : A.Tr (.tmpl .state)), A.Holds (.tmpl .state) ctx b b' tr →
      ∃ q r r', HoldsE ctx b b' q r r' ∧ HoldsS q r r') : SplitAir A .state :=
  ⟨KV, Bytes, HoldsE, HoldsS, joint⟩

/-- The finalize leaf's split semantics: `wIn` the input's state commitment (`win`: the view's
`stRoot`, lane B's `stD`), `wOut` the post-state root, `qOf` the sorted committed list. -/
def finSem {A : Airs8} {HoldsE HoldsS joint} (win : RConf → Bytes) :
    SplitSem (finAir (A := A) HoldsE HoldsS joint) where
  wIn := win
  wOut := finW
  qOf x _ := match finOv x with
    | some o => sortKV o.committed
    | none => []
  apply _ r := r

/-- **The engine side of the finalize glue, proved** (lane E): a finalize-step meaning instance is
related by its own traffic — `FinalizeAgreeT` (`finalizeAgree`) on the run of `finalizeR` that
`fin_step_root` exhibits. -/
theorem fin_reqs {A : Airs8} {HoldsE HoldsS joint} (win : RConf → Bytes) :
    ReqsRelOn (finSem (A := A) (HoldsE := HoldsE) (HoldsS := HoldsS) (joint := joint) win) FinRel
      FinPre := by
  intro x x' hm hp
  obtain ⟨I, yf, yn, i, k, rs, r, out, r', rfl, rfl, hs, ht⟩ := hp
  cases hm with
  | run hv =>
  have he := vfsteps_esteps hv
  cases he with
  | step h1 h2 =>
    rename_i b
    obtain ⟨out1, hb, ⟨r1, r2, hf⟩, -⟩ := fin_step_root h1
    obtain ⟨bp, bs⟩ := b
    simp only at hb; subst hb
    have := OvlInv.esteps_from_done I.prog h2
    simp only [EConf.mk.injEq, EPos.done.injEq] at this
    obtain ⟨rfl, -⟩ := this
    refine ⟨finO yf yn rs i, rfl, rfl, ?_⟩
    exact finalizeAgree _ r1 _ _ r2 hs (by rw [finO_trie]; exact ht) hf

/-- **Lane B's IF-FINAL half for the finalize leaf** (relational): for every input whose state
commitment is the leaf's `r` and whose committed overlay `o` has the bus's sorted change list,
`o.finalize = .ok r'` — what `Glue.final_glue` gives from `m5b_final` when the IF's authenticated
trie is `o.trie` (the input `stRoot` commits the trie: its hash `TCH` and its reveal shape in
`rest`). -/
def FinHalfB (HoldsS : KV → Bytes → Bytes → Prop) (win : RConf → Bytes) (Bad : Prop) : Prop :=
  ∀ q r r', HoldsS q r r' → Bad ∨ ∀ x o, win x = r → finOv x = some o → q = sortKV o.committed →
    o.finalize = .ok r'

theorem finHalf_rel {A : Airs8} {HoldsE HoldsS joint} (win : RConf → Bytes) (Bad : Prop)
    (h : FinHalfB HoldsS win Bad) :
    StHalfRel (finSem (A := A) (HoldsE := HoldsE) (HoldsS := HoldsS) (joint := joint) win) FinRel
      Bad := by
  intro q r r' hS
  rcases h q r r' hS with hb | h
  · exact .inl hb
  refine .inr fun x x' hx ⟨o, ho, hq, hf⟩ => ?_
  have e := h x o hx ho hq
  rw [hf] at e
  exact Except.ok.inj e

/-- **The finalize leaf is relatively, canonically sound** (D-b): lane F's engine half for the
finalize step (`EngHalfRCOn` with `FinPre`), lane B's IF-FINAL half (`FinHalfB`), and the glue
`fin_reqs` (proved). -/
theorem fin_sound_relC (sf : Intake → TTN.Store) (V : ViewImpl) {A : Airs8} {HoldsE HoldsS joint}
    (win : RConf → Bytes) (Bad : Prop)
    (hE : EngHalfRCOn sf V (finSem (A := A) (HoldsE := HoldsE) (HoldsS := HoldsS) (joint := joint)
      win) FinPre Bad)
    (hS : FinHalfB HoldsS win Bad) : TmplSoundRel8C sf V A Bad .state :=
  split_sound_relC_relOn sf V _ _ FinRel FinPre Bad hE (finHalf_rel win Bad hS) (fin_reqs win)

/-- **The intake facts behind `FinPre`'s trie premise on the honest run**: the overlay's trie is
`I.prog.t` along every run from `start` (`OvlInv.reach_trie_nodup`), so `FinPre`'s
`rs.o.trie = preT …` is `IntakeTrie I` (the intake's revealed trie is the environment's
pre-state: `Intake`'s `tMain := revealAll store revealFuel prev_state_root`, the program's `env`
carrying that store and root). -/
def IntakeTrie (I : Intake) : Prop :=
  Logged.HInv I.prog.env.store ∧ I.prog.t = Logged.preT I.prog.env.store I.prog.env.preRoot

theorem finPre_trie_of_reach {I : Intake} {yf yn i k : Nat} {rs : RS} {r0 r1 : Recording}
    (hI : IntakeTrie I) (h : ESteps I.prog ⟨.start, r0⟩ ⟨.yields yf yn 0 i k rs, r1⟩) :
    Logged.HInv I.prog.env.store ∧ rs.o.trie = Logged.preT I.prog.env.store I.prog.env.preRoot := by
  refine ⟨hI.1, ?_⟩
  obtain ⟨ht, -⟩ := OvlInv.reach_trie_nodup I.prog _ h (o := rs.o) rfl
  rw [ht]; exact hI.2

#print axioms finalizeR_run
#print axioms finalizeAgree
#print axioms finalizeAgree_fails
#print axioms finalizeStep_root
#print axioms fin_step_root
#print axioms fin_reqs
#print axioms finHalf_rel
#print axioms fin_sound_relC
#print axioms finPre_trie_of_reach

end NearSpecV3.E2E.GlueFin
