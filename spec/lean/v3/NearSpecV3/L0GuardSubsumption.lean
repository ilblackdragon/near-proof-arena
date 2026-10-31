import NearSpecV3.Successor.TierO6
import NearSpecV3.Logged.TrieHash
import NearSpecV3.Successor.LayoutReach
import NearSpecV3.Wasm.FuelHost
import NearSpecV3.Wasm.FuelSufficiency

/-! # L0 row validation: masked and dead d2-core guards (Gate-B, `allFeatures`)

Each lemma states why a d2-core guard of the canonical checker (`checkReshardCoreObs` /
`checkD2CoreGWith`, which share the guard sequence) can never be the first failing check, or can
never fail at all. The coverage tool (`tools/d3/lean_chunk_coverage.py`, `promote_row`) names these
lemmas in the rows' evidence; it checks that each named lemma is declared in this file.

* `L0-D2-006` (`invalid: empty chain segment`) is subsumed by `L0-D2-021`
  (`segment does not start at prev_block_hash`): with no block, the guard compares `[]` with the chunk
  header's `prev_block_hash`, which the decoder reads as exactly 32 bytes.
* `L0-D2-007` (`epoch table not strictly ascending`) is subsumed by `L0-D2-008` (`epoch table does
  not match the referenced epochs`): the referenced list is `dedupSorted`, which is strictly ascending.
* `L0-D2-009` (`epoch_id not in the epoch table`) is subsumed by `L0-D2-008`: the referenced list
  contains the claim's `epoch_id`.
* `L0-D2-038` (`bandwidth scheduler params (assert panics)`) never fails: the PV 86 configuration
  satisfies `BandwidthSchedulerParams::calculate`'s assertions for every shard count.
* `L0-D2-039` (`main base_state does not hash to prev_state_root`) never fails: a trie revealed from a
  hash-addressed store hashes to the root it was revealed from (`Logged.hashOf_revealAll`).
* `L0-D2-012` / `L0-same-layout` (`c.same_layout`) and `L0-D2-019` / `L0-split-gate`
  (`c.no_split_gate`), and their description `L0-guard-noResharding`, are evaluated on `allFeatures`
  only for segments that contain the genesis block (`checkD2CoreGWith`). They run after the
  epoch-protocol-version check (`c.pv86`, `L0-D2-011`), so every epoch of the claim is PV86 when they
  run. On nearcore's epoch model (`Successor.LayoutReach.Chain`), a chain whose genesis epoch is
  PV86 has a *static* `config(86)` (`genesis.rs:64-69`), so every PV86 epoch keeps the genesis
  layout (`genesis_segment_same_layout`) and no block of such an epoch carries a split gate
  (`genesis_segment_no_split_gate`): nearcore computes one only under a dynamic config
  (`runtime/mod.rs:597`, oracle `claim.rs:176`).
-/

namespace NearSpecV3.L0Guards
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.Successor

/-! ## L0-D2-006 ⊂ L0-D2-021 -/

theorem takeN_length : ∀ (n : Nat) (bs out rest : Bytes), takeN n bs = some (out, rest) → out.length = n
  | 0, bs, out, rest, h => by simp [takeN] at h; obtain ⟨rfl, -⟩ := h; rfl
  | n + 1, [], out, rest, h => by simp [takeN] at h
  | n + 1, b :: bs, out, rest, h => by
    simp only [takeN] at h
    cases hr : takeN n bs with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨o, r⟩ := p
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [takeN_length n bs o r hr]

theorem readHash_length {bs out rest : Bytes} (h : readHash bs = some (out, rest)) : out.length = 32 :=
  takeN_length 32 bs out rest h

/-- `pChunkInner` reads `prev_block_hash` with `pHash` (`Wire.lean`), which yields 32 bytes. -/
theorem pHash_length {w : String} {bs out rest : Bytes} (h : pHash w bs = .ok (out, rest)) :
    out.length = 32 := by
  unfold pHash lift at h
  split at h
  · rename_i x hx
    cases h
    exact readHash_length hx
  · cases h

/-- The empty-segment guard: with no block, the start guard (`L0-D2-021`) compares `[]` with
`prev_block_hash`, so it fails whenever `prev_block_hash` is non-empty. -/
theorem empty_segment_fails_start (hashes : List Bytes) (pbh : Bytes) (hb : hashes = [])
    (hp : pbh.length = 32) : (hashes.headD [] == pbh) = false := by
  subst hb
  cases pbh with
  | nil => simp at hp
  | cons _ _ => rfl

/-! ## L0-D2-009 ⊂ L0-D2-008 -/

/-- If the epoch table's ids equal the referenced epochs (`L0-D2-008` passes), the claim's own epoch
is in the table (`L0-D2-009` passes). -/
theorem epoch_in_table_of_referenced (c : Claim) (rest : List Bytes)
    (h8 : (c.epochs.map (·.epochId) == dedupSorted (c.epochId :: rest)) = true) :
    (c.epochs.find? (·.epochId == c.epochId)).isSome = true := by
  have htab : c.epochs.map (·.epochId) = dedupSorted (c.epochId :: rest) := by simpa using h8
  have hm : c.epochId ∈ c.epochs.map (·.epochId) := by
    rw [htab]; exact mem_dedupSorted _ _ List.mem_cons_self
  obtain ⟨r, hr, hre⟩ := List.mem_map.mp hm
  cases hf : c.epochs.find? (·.epochId == c.epochId) with
  | some _ => rfl
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp [hre]) (hf r hr)

/-! ## L0-D2-007 ⊂ L0-D2-008 -/

theorem bytesLt_irrefl : ∀ a : Bytes, bytesLt a a = false
  | [] => rfl
  | a :: as => by simp [bytesLt, bytesLt_irrefl as]

/-- Trichotomy of the byte order. -/
theorem bytesLt_total : ∀ a b : Bytes, bytesLt a b = false → bytesLt b a = false → a = b
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [bytesLt] at h
  | _ :: _, [], _, h => by simp [bytesLt] at h
  | x :: xs, y :: ys, h1, h2 => by
    simp only [bytesLt] at h1 h2
    by_cases hxy : x.toNat < y.toNat
    · simp [hxy] at h1
    · by_cases hyx : y.toNat < x.toNat
      · simp [hyx] at h2
      · simp [hxy, hyx] at h1 h2
        have : x = y := UInt8.toNat_inj.mp (by omega)
        subst this
        rw [bytesLt_total xs ys h1 h2]

theorem bytesLt_trans : ∀ a b c : Bytes, bytesLt a b = true → bytesLt b c = true → bytesLt a c = true
  | [], [], _, h, _ => by simp [bytesLt] at h
  | [], _ :: _, [], _, h => by simp [bytesLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [bytesLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [bytesLt] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [bytesLt] at h1 h2 ⊢
    by_cases hxz : x.toNat < z.toNat
    · simp only [hxz, ↓reduceIte]
    · simp only [hxz, ↓reduceIte]
      by_cases hxy : x.toNat < y.toNat
      · by_cases hyz : y.toNat < z.toNat
        · omega
        · simp only [hyz, ↓reduceIte] at h2
          by_cases hzy : z.toNat < y.toNat
          · simp only [hzy, ↓reduceIte, Bool.false_eq_true] at h2
          · omega
      · simp only [hxy, ↓reduceIte] at h1
        by_cases hyx : y.toNat < x.toNat
        · simp only [hyx, ↓reduceIte, Bool.false_eq_true] at h1
        · simp only [hyx, ↓reduceIte] at h1
          by_cases hyz : y.toNat < z.toNat
          · omega
          · simp only [hyz, ↓reduceIte] at h2
            by_cases hzy : z.toNat < y.toNat
            · simp only [hzy, ↓reduceIte, Bool.false_eq_true] at h2
            · simp only [hzy, ↓reduceIte] at h2
              have hzx : ¬ z.toNat < x.toNat := by omega
              simp only [hzx, ↓reduceIte]
              exact bytesLt_trans xs ys zs h1 h2

/-- Non-strictly ascending: no element is smaller than its predecessor. -/
def Asc : List (Bytes × Option Bytes) → Prop
  | a :: b :: rest => bytesLt b.1 a.1 = false ∧ Asc (b :: rest)
  | _ => True

theorem asc_insertSorted (p : Bytes × Option Bytes) :
    ∀ l, Asc l → Asc (insertSorted p l)
  | [], _ => trivial
  | [q], _ => by
    simp only [insertSorted]
    split
    · rename_i h
      refine ⟨?_, trivial⟩
      cases hq : bytesLt q.1 p.1
      · rfl
      · have := bytesLt_trans p.1 q.1 p.1 h hq
        rw [bytesLt_irrefl] at this; cases this
    · rename_i h
      exact ⟨by simpa using h, trivial⟩
  | q :: r :: rest, ⟨hqr, hrest⟩ => by
    simp only [insertSorted]
    split
    · rename_i h
      refine ⟨?_, hqr, hrest⟩
      cases hq : bytesLt q.1 p.1
      · rfl
      · have := bytesLt_trans p.1 q.1 p.1 h hq
        rw [bytesLt_irrefl] at this; cases this
    · rename_i h
      have ih := asc_insertSorted p (r :: rest) hrest
      have hp : bytesLt p.1 q.1 = false := by simpa using h
      revert ih
      simp only [insertSorted]
      split
      · intro ih; exact ⟨hp, ih⟩
      · intro ih; exact ⟨hqr, ih⟩

theorem asc_sortKV (l : List (Bytes × Option Bytes)) : Asc (sortKV l) := by
  unfold sortKV
  suffices ∀ acc, Asc acc → Asc (l.foldl (fun acc p => insertSorted p acc) acc) from this [] trivial
  induction l with
  | nil => intro acc h; exact h
  | cons p ps ih => intro acc h; exact ih _ (asc_insertSorted p acc h)

/-- The fold of `dedupStep` over a non-strictly ascending list: strictly ascending, and its head
(if any) is the list's head key. -/
theorem dedup_foldr_spec : ∀ L : List (Bytes × Option Bytes), Asc L →
    strictlyAscending (L.foldr dedupStep []) = true ∧
      (L.foldr dedupStep []).head? = L.head?.map (·.1)
  | [], _ => ⟨rfl, rfl⟩
  | [kv], _ => by obtain ⟨k, v⟩ := kv; exact ⟨rfl, rfl⟩
  | kv :: kv2 :: rest, ⟨h12, hrest⟩ => by
    obtain ⟨ih1, ih2⟩ := dedup_foldr_spec (kv2 :: rest) hrest
    obtain ⟨k, v⟩ := kv
    rw [List.foldr_cons]
    generalize hacc : (kv2 :: rest).foldr dedupStep [] = acc at ih1 ih2
    cases acc with
    | nil => simp at ih2
    | cons k' tl =>
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at ih2
      subst ih2
      simp only [dedupStep]
      split
      · rename_i heq
        have : k = kv2.1 := by simpa using heq
        subst this
        exact ⟨ih1, rfl⟩
      · rename_i hne
        refine ⟨?_, rfl⟩
        simp only [strictlyAscending, ih1, Bool.and_true]
        have hne' : k ≠ kv2.1 := by simpa using hne
        cases hlt : bytesLt k kv2.1
        · exact absurd (bytesLt_total _ _ hlt h12) hne'
        · rfl

theorem strictlyAscending_dedupSorted (l : List Bytes) : strictlyAscending (dedupSorted l) = true := by
  rw [dedupSorted_eq]
  exact (dedup_foldr_spec _ (asc_sortKV _)).1

/-- If the epoch table's ids equal the referenced epochs (`L0-D2-008` passes), they are strictly
ascending (`L0-D2-007` passes). -/
theorem ascending_of_referenced (ids referenced : List Bytes) (l : List Bytes)
    (hr : referenced = dedupSorted l) (h8 : (ids == referenced) = true) :
    strictlyAscending ids = true := by
  have : ids = referenced := by simpa using h8
  rw [this, hr]; exact strictlyAscending_dedupSorted l

/-! ## L0-D2-038 and L0-D2-039: checks that never fail -/

theorem scheduler_params_pv86 (n : Nat) :
    (Scheduler.Params.calculate Scheduler.Config.pv86 n).isSome = true := by
  simp [Scheduler.Params.calculate, Scheduler.Config.pv86]

theorem base_state_hashes (merged : List Bytes) (fuel : Nat) (root : Bytes) :
    (revealAll (mkHStore merged) fuel root).hashOf = root :=
  Logged.hashOf_revealAll (Logged.HInv_mkHStore merged) fuel root

/-! ## Resharding guards on genesis segments (L0-D2-012, L0-D2-019) -/

section GenesisSegment
open NearSpecV3.Successor.LayoutReach

/-- Any two epochs `i, j ≤ w` of a chain whose epochs `0..w` are all PV86 have the same layout: the
honest epoch table of a genesis segment satisfies `c.same_layout`. -/
theorem genesis_segment_same_layout {L : Type} (ch : Chain L) (w : Nat)
    (hpv : ∀ i, i ≤ w → ch.pv i = 86) (i j : Nat) (hi : i ≤ w) (hj : j ≤ w) :
    ch.layout i = ch.layout j := by
  rw [genesis_segment_one_layout ch w hpv i hi, genesis_segment_one_layout ch w hpv j hj]

/-- `gate i` is the split gate of a block of epoch `i`. nearcore (and the oracle's claim) computes
one only when `config(pv i)` is dynamic (`hg`). If epochs `0..w` are PV86, `config(86)` is the
genesis epoch's static config, so no block of those epochs has a gate: the honest `apply_facts` of
a genesis segment satisfy `c.no_split_gate`. -/
theorem genesis_segment_no_split_gate {L G : Type} (ch : Chain L) (gate : Nat → Option G)
    (hg : ∀ i g, gate i = some g → ch.cfg (ch.pv i) = .dynamic) (w : Nat)
    (hpv : ∀ i, i ≤ w → ch.pv i = 86) : ∀ i, i ≤ w → gate i = none := by
  intro i hi
  have hs : ch.cfg 86 = .static (ch.layout 0) := by
    have := ch.genesis0; rwa [hpv 0 (Nat.zero_le _)] at this
  cases h : gate i with
  | none => rfl
  | some g =>
    have hd := hg i g h
    rw [hpv i hi, hs] at hd
    cases hd

end GenesisSegment

end NearSpecV3.L0Guards

/-! ## L0-W-011: on certified code the fuel-certificate invariant holds at every state, so no frame names a missing function or a pc outside its code (`frame_ok`, `run_inv`); with prepare's gas-table size check (`GasSized`) every step finds its instruction and gas (`step_lookups`). (third pass, 2026-10-31) -/

section
open NearSpecV3.Wasm

namespace NearSpecV3.Wasm.L0W011

/-- Generic: an `Id` loop over a list whose body always yields and keeps `P` at members. -/
theorem loop_bind {σ β : Type} (P : σ → Prop) (Q : β → Prop) :
    ∀ (l : List Nat) (body : Nat → σ → Id (ForInStep σ)) (st : σ) (k : σ → Id β),
      (∀ i ∈ l, ∀ t, P t → ∃ t', body i t = pure (.yield t') ∧ P t') → P st →
      (∀ t, P t → Q (k t)) → Q (forIn l st body >>= k)
  | [], _, st, k, _, h, hk => hk st h
  | x :: xs, body, st, k, hb, h, hk => by
    simp only [List.forIn_cons]
    obtain ⟨t', ht, hp⟩ := hb x List.mem_cons_self st h
    rw [ht]
    exact loop_bind P Q xs body t' k (fun i hi t htp => hb i (List.mem_cons_of_mem _ hi) t htp) hp hk

theorem getD_set!_ne (a : Array Bool) (i j : Nat) (v : Bool) (h : i ≠ j) :
    (a.set! i v).getD j false = a.getD j false := by
  simp only [Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds_ne h]

/-- A position the built certificate marks live is a code position. -/
theorem buildLblLive_live (pf : PFunc) (j : Nat) (h : (buildLblLive pf).2.getD j false = true) :
    j < pf.code.size := by
  apply Classical.byContradiction
  intro hj
  have hj : pf.code.size ≤ j := by omega
  have hfalse : (buildLblLive pf).2.getD j false = false := by
    unfold buildLblLive
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
    apply loop_bind (P := fun st : Array (List (Nat × Bool)) × Array Bool × List (Nat × Bool) × Bool × List Bool =>
        st.2.1.getD j false = false) (Q := fun r : Array (List (Nat × Bool)) × Array Bool => r.2.getD j false = false)
    · intro i hi t ht
      have hilt : i < pf.code.size := by
        rw [List.mem_range'_1] at hi; simp at hi; omega
      have hne : i ≠ j := by omega
      split <;> (try split) <;> (try split) <;>
        exact ⟨_, rfl, by simp only; rw [getD_set!_ne _ _ _ _ hne]; exact ht⟩
    · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    · intro t ht; exact ht
  rw [hfalse] at h
  exact Bool.false_ne_true h

/-- The certificate family the checker uses (`prepCertOK_certified`). -/
def cdOf (cfg : NearCfg) (p : Prepared) : Nat → FCert := fun k => buildCert cfg (p.funcs[k]?.getD default)

/-- Every frame satisfying the fuel-certificate invariant names a defined function and sits at a
code position: `step`'s `bad frame` and `pc out of range` arms are not taken. With `GasSized`
(checked by `prepare`, `Prepare.lean:492-495`) the `gas table shorter` arm is not taken either. -/
theorem frame_ok (cfg : NearCfg) (p : Prepared) (f : Frame) (h : FrameInv (cdOf cfg p) f) :
    ∃ pf, p.funcs[f.fn]? = some pf ∧ f.pc < pf.code.size := by
  have hl := h.1
  simp only [cdOf, buildCert, FCert.lv] at hl
  have hlt := buildLblLive_live _ _ hl
  cases hk : p.funcs[f.fn]? with
  | none =>
    rw [hk] at hlt
    simp only [Option.getD_none] at hlt
    exact absurd hlt (Nat.not_lt_zero _)
  | some pf =>
    rw [hk] at hlt
    exact ⟨pf, rfl, hlt⟩

def GasSized (p : Prepared) : Prop := ∀ (k : Nat) (pf : PFunc), p.funcs[k]? = some pf → pf.gas.size = pf.code.size

/-- At a state satisfying the invariant, `step` reaches an instruction and its gas entry. -/
theorem step_lookups (cfg : NearCfg) (p : Prepared) (hg : GasSized p) (s : St) (f : Frame)
    (fs : List Frame) (hf : s.frames = f :: fs) (hinv : Inv (cdOf cfg p) s) :
    ∃ pf i o, p.funcs[f.fn]? = some pf ∧ pf.code[f.pc]? = some i ∧ pf.gas[f.pc]? = some o := by
  obtain ⟨pf, hpf, hpc⟩ := frame_ok cfg p f (hinv f (by rw [hf]; exact List.mem_cons_self))
  have hgs := hg _ _ hpf
  refine ⟨pf, pf.code[f.pc], pf.gas[f.pc]'(by omega), hpf, ?_, ?_⟩
  · exact Array.getElem?_eq_getElem hpc
  · exact Array.getElem?_eq_getElem (by omega)

/-- Hence `step` from such a state never returns any of the three `unmodeled` invariant arms:
its result is `fin` (no frame), or the instruction's own result. -/
theorem step_not_invariant (cfg : NearCfg) (p : Prepared) (hg : GasSized p) (s : St)
    (hinv : Inv (cdOf cfg p) s) :
    s.frames = [] ∨ ∃ f fs pf i o, s.frames = f :: fs ∧ p.funcs[f.fn]? = some pf ∧
      pf.code[f.pc]? = some i ∧ pf.gas[f.pc]? = some o ∧
      step cfg p s = (match o with
        | none => exec cfg p s f pf i
        | some (k, fee) =>
          match charge s fee (if k = .linear then topCount s else 0) with
          | .cont s => exec cfg p s f pf i
          | r => r) := by
  cases hf : s.frames with
  | nil => exact .inl rfl
  | cons f fs =>
    obtain ⟨pf, i, o, h1, h2, h3⟩ := step_lookups cfg p hg s f fs hf hinv
    refine .inr ⟨f, fs, pf, i, o, rfl, h1, h2, h3, ?_⟩
    simp only [step, hf, h1, h2, h3]
    cases o <;> rfl

/-- Every state a run visits satisfies the invariant: the run's result is fuel exhaustion or the
result of `step` at an invariant state. -/
theorem run_inv (cfg : NearCfg) (p : Prepared) (hcert : Certified cfg p (cdOf cfg p))
    (hr : 0 < cfg.regularOpCost) :
    ∀ (n : Nat) (s : St), Inv (cdOf cfg p) s →
      run cfg p n s = .unmodeled "fuel exhausted" ∨
      ∃ t, Inv (cdOf cfg p) t ∧ run cfg p n s = step cfg p t ∧ ∀ u, step cfg p t ≠ .cont u
  | 0, _, _ => .inl rfl
  | n + 1, s, hi => by
    simp only [run]
    cases hs : step cfg p s with
    | cont s' =>
      obtain ⟨hi', -, -⟩ := step_dec hcert hostsOK hr hi hs
      exact run_inv cfg p hcert hr n s' hi'
    | fin t => exact .inr ⟨s, hi, hs.symm, by rw [hs]; intro u h; cases h⟩
    | abort t e => exact .inr ⟨s, hi, hs.symm, by rw [hs]; intro u h; cases h⟩
    | unmodeled w => exact .inr ⟨s, hi, hs.symm, by rw [hs]; intro u h; cases h⟩

theorem certified_of_prepCertOK (cfg : NearCfg) (p : Prepared) (h : prepCertOK cfg p = true) :
    Certified cfg p (cdOf cfg p) := prepCertOK_certified cfg p h

end NearSpecV3.Wasm.L0W011

end

/-! ## L0-W-013: `popArgs n` always returns `n` values, so the host-call arity throw is dead. (third pass, 2026-10-31) -/

section
open NearSpecV3.Wasm

namespace NearSpecV3.Wasm.L0W013

/-- The pop loop of `popArgs`, run on any list: it never fails and pushes one value per element. -/
theorem popLoop (l : List Nat) : ∀ (out : Array Nat) (s : St),
    ∃ out' s', (forIn (m := EStateM String St) l out (fun _ r => do
        let (v, s) := popN (← get)
        set s
        pure (ForInStep.yield (r.push v)))).run s = .ok out' s' ∧ out'.size = out.size + l.length := by
  induction l with
  | nil => intro out s; exact ⟨out, s, rfl, by simp⟩
  | cons x xs ih =>
    intro out s
    obtain ⟨out', s', h, hs⟩ := ih (out.push (popN s).1) (popN s).2
    refine ⟨out', s', ?_, ?_⟩
    · simp only [List.forIn_cons]
      exact h
    · simp at hs ⊢; omega

/-- `popArgs n` never reports `unmodeled host-call arity`: it always returns `n` values. -/
theorem popArgs_ok (n : Nat) (s : St) : ∃ v s', (popArgs n).run s = .ok v s' := by
  unfold popArgs
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  obtain ⟨out', s', h, hs⟩ := popLoop (List.range' 0 [:n].size) #[] s
  simp only [List.length_range', Array.size_empty, Nat.zero_add] at hs
  have hsz : out'.reverse.size = n := by simp [hs]
  refine ⟨⟨out'.reverse, hsz⟩, s', ?_⟩
  simp only [EStateM.run, bind, EStateM.bind] at h ⊢
  split
  · rename_i a s2 heq
    have e := h.symm.trans heq
    cases e
    simp only [hsz, dite_true]
    rfl
  · rename_i e s2 heq
    have e := h.symm.trans heq
    cases e

end NearSpecV3.Wasm.L0W013

end

/-! ## L0-W-013: with a real store the accessors take their store branch on the unchanged state. (third pass, 2026-10-31) -/

section
open NearSpecV3.Wasm

namespace NearSpecV3.Wasm.L0W013

/-- With a trie-backed store present, `realHasH` takes the store branch (the `unmodeled: real store`
throw is not taken) and leaves the state unchanged. -/
theorem realHasH_some (k : ByteArray) (s : St) (r : TTN.RealStore) (hr : s.real = some r) :
    (realHasH k).run s =
      (match r.overlay.get? k with
        | some v => .ok v.isSome s
        | none =>
          match TTN.lookup r.store r.root k with
          | .error e => .error e s
          | .ok l => .ok l.value.isSome s) := by
  simp only [realHasH, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, hr]
  cases h1 : r.overlay.get? k with
  | some v => rfl
  | none =>
    cases h2 : TTN.lookup r.store r.root k with
    | error e => rfl
    | ok l => rfl

theorem realGetH_some (k : ByteArray) (s : St) (r : TTN.RealStore) (hr : s.real = some r) :
    (realGetH k).run s =
      (match r.overlay.get? k with
        | some v => .ok v s
        | none =>
          match TTN.lookup r.store r.root k with
          | .error e => .error e s
          | .ok l => match l.value with
            | none => .ok none s
            | some (_, vh) => match r.store vh with
              | some v => .ok (some v) s
              | none => .error TTN.errMissing s) := by
  simp only [realGetH, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, hr]
  cases h1 : r.overlay.get? k with
  | some v => rfl
  | none =>
    cases h2 : TTN.lookup r.store r.root k with
    | error e => rfl
    | ok l =>
      cases h3 : l.value with
      | none => simp only [h3]; rfl
      | some p =>
        obtain ⟨n, vh⟩ := p
        cases h4 : r.store vh with
        | none => simp only [h3, h4]; rfl
        | some v => simp only [h3, h4]; rfl

end NearSpecV3.Wasm.L0W013

end

/-! ## L0-W-014: on a trie whose reachable extensions have non-empty keys, `lookup` fails only with MissingTrieValue or a node-decoding error, never on its fuel (`lookup_errors`). (third pass, 2026-10-31) -/

section
open NearSpecV3.Wasm

namespace NearSpecV3.Wasm.L0W014
open NearSpecV3.Wasm.TTN

/-- `G` is a set of node hashes closed under the child pointers a lookup follows, and no node in
it is an extension with an empty nibble path. Instantiated with "reachable from the state root":
nearcore never builds an empty extension (`insert_delete.rs` creates extensions only from a
non-empty common prefix or remainder; `squash.rs` only lengthens them). Values and code blobs
in the same store are not constrained (a lookup never decodes them as nodes). -/
def NoEmptyExt (st : TTN.Store) (G : ByteArray → Prop) : Prop :=
  ∀ h b, G h → st h = some b →
    (∀ k c, decodeNode b = some (.ext k c) → k ≠ [] ∧ G c) ∧
    (∀ v kids (n : Nat) c, decodeNode b = some (.branch v kids) → kids[n]? = some (some c) → G c)

theorem isPrefixN_length : ∀ (k key : List Nat), isPrefixN k key = true → k.length ≤ key.length
  | [], _, _ => Nat.zero_le _
  | _ :: _, [], h => by simp [isPrefixN] at h
  | a :: as, b :: bs, h => by
    simp only [isPrefixN, Bool.and_eq_true] at h
    have := isPrefixN_length as bs h.2
    simp; omega

/-- With fuel above the key's nibble count, a lookup's only errors are the two storage errors:
never `unmodeled: lookup fuel`. -/
theorem lookupFrom_errors (st : TTN.Store) (G : ByteArray → Prop) (hne : NoEmptyExt st G) :
    ∀ (fuel : Nat) (h : ByteArray) (key : List Nat) (acc : List ByteArray) (e : String),
      G h → key.length < fuel → lookupFrom st fuel h key acc = .error e →
      e = errMissing ∨ e = "StorageInconsistentState(node decoding)"
  | 0, _, _, _, _, _, hl, _ => absurd hl (Nat.not_lt_zero _)
  | fuel + 1, h, key, acc, e, hg, hl, he => by
    simp only [lookupFrom] at he
    cases hs : st h with
    | none => rw [hs] at he; cases he; exact .inl rfl
    | some bytes =>
      rw [hs] at he
      simp only at he
      cases hd : decodeNode bytes with
      | none => rw [hd] at he; cases he; exact .inr rfl
      | some n =>
        rw [hd] at he
        cases n with
        | leaf k len vh => cases he
        | ext k c =>
          simp only at he
          split at he
          · rename_i hp
            obtain ⟨hk, hgc⟩ := (hne h bytes hg hs).1 k c hd
            have hkl := isPrefixN_length k key hp
            have hpos : 0 < k.length := List.length_pos_iff.mpr hk
            exact lookupFrom_errors st G hne fuel c (key.drop k.length) _ e hgc
              (by simp only [List.length_drop]; omega) he
          · cases he
        | branch v kids =>
          simp only at he
          cases key with
          | nil => cases he
          | cons n rest =>
            simp only at he
            split at he
            · rename_i c hc
              exact lookupFrom_errors st G hne fuel _ rest _ e ((hne h bytes hg hs).2 v kids n c hd hc)
                (by simp at hl; omega) he
            · cases he

theorem loop_length (bs : ByteArray) : ∀ (k i : Nat) (r : List UInt8), bs.size - i = k →
    (ByteArray.toList.loop bs i r).length = r.length + (bs.size - i)
  | 0, i, r, hk => by
    rw [ByteArray.toList.loop.eq_1]
    have : ¬ i < bs.size := by omega
    simp [this]; omega
  | k + 1, i, r, hk => by
    rw [ByteArray.toList.loop.eq_1]
    have : i < bs.size := by omega
    simp only [this, ite_true]
    rw [loop_length bs k (i + 1) _ (by omega)]
    simp; omega

theorem toList_length (d : ByteArray) : d.toList.length = d.size := by
  unfold ByteArray.toList
  rw [loop_length d _ 0 [] rfl]
  simp

theorem replicate_two_sum (n : Nat) : (List.replicate n 2).sum = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.sum_cons, ih]; omega

theorem nibblesOf_length (d : ByteArray) : (nibblesOf d).length = 2 * d.size := by
  unfold nibblesOf
  rw [List.length_flatMap]
  simp only [List.length_cons, List.length_nil]
  rw [List.map_const', replicate_two_sum, toList_length]

/-- `TTN.lookup` never reports `unmodeled: lookup fuel` on a store without empty extensions. -/
theorem lookup_errors (st : TTN.Store) (G : ByteArray → Prop) (hne : NoEmptyExt st G)
    (root key : ByteArray) (hroot : G root) (e : String) (h : lookup st root key = .error e) :
    e = errMissing ∨ e = "StorageInconsistentState(node decoding)" := by
  unfold lookup at h
  split at h
  · cases h
  · exact lookupFrom_errors st G hne _ root _ [] e hroot (by rw [nibblesOf_length]; omega) h

end NearSpecV3.Wasm.L0W014

end
