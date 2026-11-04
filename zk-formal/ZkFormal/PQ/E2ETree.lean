import ZkFormal.PQ.E2ENode

/-!
# ZkFormal.PQ.E2ETree — the chunk-independent tree of lane D (D-5), transcribed

Lane E (E2E M11e), 2026-11-04.

## Why this file exists

`E2ENode.lean` (M11d) transcribed `build_agg` from `openvm-recursion-agg.patch`. In that overlay,
`nv/verifier.rs` reads `if b.bind || b.bind_child { /* comments */ } else if false { … }`, so
**no child of an aggregation node was program-bound**. Both lane E and lane D (main `59fc5ddb9`,
`README-agg-patch.md` "Defect found in D-5") found this. Consequences for M11d's theorems:

* `node_composition`, `nvComposition_node` and `nvFaithful_node` (and `nodeOK_agg` in
  `E2EAgg.lean`) are **not wrong**. They never modelled binding as present: program binding was a
  part of the open premise `NodeInner` (component 2 + 4 of `NodeExec`), which E2ENode's docstring
  says "must be read as including program binding".
* For the old program, that premise was **false**: a child proof under a different program passes
  the node. So `NodeExec` was unsatisfiable for the pinned old node, and `nvFaithful_node`
  instantiated at it would have been vacuous. Nothing downstream used such an instance.
* The statement-level transcription (cells, `hash_range`, continuity, `outCell`) is **unchanged**
  in the new overlay: `agg.rs` of `e2e-tree.patch` differs from the old one only in visibility,
  the header comment and `b.bind_child_index = i` (checked by `diff`). `compose_of_asserts` and
  `node_composition` therefore stand for the new node as they are.

## What is transcribed here (from `patches/e2e-tree.patch`, `nv/tree.rs` and the `verifier.rs` hunk)

* **Child program binding** (`verifier.rs`, D-5). Per child: `flag = (level − M)·inv` with the
  "level flag" assert `(level − M)(1 − flag) = 0`. At the anchor level (flag 0), the anchor-set
  selector `s_t` is boolean, sums to 1 and `Σ s_t (root − C_t) = 0`. Child 0 at flag 1 is bound
  by BIND. Later siblings assert `flag·(root_i − root_0) = 0`. `build_agg` adds "children at the
  same level". `node_bind`: either every child is at the anchor level with program root in the
  pinned set, or every child shares child 0's root and child 0 is BIND-bound. The selector
  arithmetic is proved over `Fp` (`sel_mem`: a boolean selector summing to 1 picks a member, if
  the set has fewer than `p` elements).
* **Leaves.** `build_norm` (template normaliser: `(ctx = child digest, a, a + 1, [init, cls],
  [done, cls])`, child level forced, root = anchor constant) and `build_pad` (identity on a done
  boundary). `one_template`: in a chainable leaf sequence whose first start phase is `init`,
  every leaf being a normaliser or a PAD forces **exactly one template leaf, first, followed only
  by PADs**, and the root statement is that template's `init → done` statement.
* **Wrap** (`build_wrap`). Root at the pinned level with program root `C_node`, preimage hash =
  root digest, `a = 0`, `B_0.phase = init`, `B_N.phase = done`, exposes
  `D_wrap = H8(WRAP_MARKER, 18, ctx, B_0.class)`. `wrapT_composition`: with V_d's check
  `pub = D_wrap(ctxOf s, clsOf s)`, the wrap is accepted natively (`aggWrapV`) or `H8` collides
  (`wmsg_inj`: the message is injective at the fixed `n_ctx = 18`).

## What remains open (unchanged in kind from M11d)

`NodeExecT`/`WrapExecT`/`NormExec`: the NvAir executes these programs (sub-obligations 1–4,
including BIND's own faithfulness, `BindSound`). The NvAir model work of M11e
(`NvAirModel.lean`, if present) targets the tape component.
-/

namespace ZkFormal.PQ.E2ETree

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.Nv ZkFormal.PQ.E2EBridge ZkFormal.PQ.E2EAgg
open ZkFormal.PQ.E2ENode
open ZkFormal.PQ.Aggregation.Stmt
open NearSpecV3.E2E

/-! ## Constants of `tree.rs` -/

/-- `PHASE_INIT`. -/
def phInit : Fp := 1
/-- `PHASE_DONE`. -/
def phDone : Fp := 2
/-- `N_CTX` (the statement digest limbs). -/
def nCtxT : Nat := 18
/-- `N_STATE` (`[phase, class]`). -/
def nStateT : Nat := 2

theorem phInit_ne_phDone : phInit ≠ phDone := by decide

/-! ## Field sums of boolean selectors -/

/-- `Σ` of a list of field elements. -/
def fsum : List Fp → Fp
  | [] => 0
  | x :: xs => x + fsum xs

/-- The number of ones. -/
def ones : List Fp → Nat
  | [] => 0
  | x :: xs => (if x = 1 then 1 else 0) + ones xs

/-- `s (1 − s) = 0` gives `s ∈ {0, 1}`. -/
theorem bool_cases {s : Fp} (h : s * (1 - s) = 0) : s = 0 ∨ s = 1 := by
  by_cases h0 : s = 0
  · exact .inl h0
  · right; grind

theorem ones_le : ∀ l : List Fp, ones l ≤ l.length
  | [] => Nat.le_refl _
  | x :: xs => by
    have := ones_le xs
    simp only [ones, List.length_cons]
    split <;> omega

/-- On a boolean list shorter than `p`, the field sum is the number of ones. -/
theorem fsum_toNat : ∀ l : List Fp, (∀ s ∈ l, s = 0 ∨ s = 1) → l.length < P →
    (fsum l).toNat = ones l
  | [] => fun _ _ => rfl
  | x :: xs => fun hb hl => by
    have ih := fsum_toNat xs (fun s hs => hb s (List.mem_cons_of_mem _ hs))
      (by simp at hl; omega)
    have hle := ones_le xs
    simp only [List.length_cons] at hl
    simp only [fsum, ones, Fp.add_def, Fp.toNat_add, ih]
    rcases hb x (List.mem_cons_self) with rfl | rfl
    · simp only [show ((0 : Fp) = 1) = False from by decide, ite_false, Fp.toNat_zero]
      exact Nat.mod_eq_of_lt (by omega)
    · simp only [ite_true, Fp.toNat_one]
      exact Nat.mod_eq_of_lt (by omega)

/-- No ones in a boolean list: all zero. -/
theorem all_zero_of_ones : ∀ l : List Fp, (∀ s ∈ l, s = 0 ∨ s = 1) → ones l = 0 → ∀ s ∈ l, s = 0
  | [] => fun _ _ s hs => absurd hs (by simp)
  | x :: xs => fun hb h s hs => by
    simp only [ones] at h
    have hx : x ≠ 1 := fun e => by rw [if_pos e] at h; omega
    rw [if_neg hx] at h
    rcases List.mem_cons.1 hs with rfl | hs
    · exact (hb s List.mem_cons_self).resolve_right hx
    · exact all_zero_of_ones xs (fun s hs => hb s (List.mem_cons_of_mem _ hs)) (by omega) s hs

/-- The selector accumulator `Σ s_t (x − c_t)` of the anchor-set check. -/
def facc (x : Fp) : List Fp → List Fp → Fp
  | s :: ss, c :: cs => s * (x - c) + facc x ss cs
  | _, _ => 0

theorem facc_zero (x : Fp) : ∀ ss cs : List Fp, (∀ s ∈ ss, s = 0) → facc x ss cs = 0
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | s :: ss, c :: cs, h => by
    simp only [facc]
    rw [h s List.mem_cons_self, facc_zero x ss cs (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    grind

/-- **The anchor-set selector picks a member.** A boolean selector with exactly one `1`, whose
accumulator vanishes coefficientwise, forces the root to be one of the pinned set's entries. -/
theorem sel_mem {m : Nat} (x : Fin m → Fp) :
    ∀ (ss : List Fp) (T : List (Fin m → Fp)), ss.length = T.length → (∀ s ∈ ss, s = 0 ∨ s = 1) →
      ones ss = 1 → (∀ j, facc (x j) ss (T.map (· j)) = 0) → x ∈ T
  | [], [], _, _, h1, _ => by simp [ones] at h1
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | s :: ss, c :: T, hl, hb, h1, hacc => by
    have hb' : ∀ t ∈ ss, t = 0 ∨ t = 1 := fun t ht => hb t (List.mem_cons_of_mem _ ht)
    rcases hb s List.mem_cons_self with rfl | rfl
    · have h1' : ones ss = 1 := by
        simp only [ones, show ((0 : Fp) = 1) = False from by decide, ite_false] at h1; omega
      exact List.mem_cons_of_mem _ (sel_mem x ss T (by simpa using hl) hb' h1' (fun j => by
        have := hacc j
        simp only [List.map_cons, facc] at this
        grind))
    · have h0 : ones ss = 0 := by simp only [ones, ite_true] at h1; omega
      have hz := all_zero_of_ones ss hb' h0
      have : x = c := by
        funext j
        have := hacc j
        simp only [List.map_cons, facc, facc_zero (x j) ss _ hz] at this
        grind
      exact this ▸ List.mem_cons_self

/-- From a field sum `1` of a short boolean list: exactly one `1`. -/
theorem ones_of_fsum (ss : List Fp) (hb : ∀ s ∈ ss, s = 0 ∨ s = 1) (hl : ss.length < P)
    (h : fsum ss = 1) : ones ss = 1 := by
  have := fsum_toNat ss hb hl
  rw [h, Fp.toNat_one] at this
  exact this.symm

/-! ## Child program binding (the D-5 `verifier.rs` hunk) -/

/-- One child's binding cells: its exposed level, the inverse witness, the anchor-set selector
and its cached program root (coefficientwise). -/
structure KidB (m : Nat) where
  level : Fp
  inv : Fp
  sel : List Fp
  root : Fin m → Fp

/-- `flag = (cl − M)·inv`. -/
def KidB.flag {m : Nat} (M : Fp) (c : KidB m) : Fp := (c.level - M) * c.inv

/-- The per-child asserts, at anchor level `M` and anchor set `T`:
"level flag", "anchor set selector boolean", "anchor set selector sums to one" (gated by
`1 − flag`) and "anchor child program commitment in the anchor set" (gated by `1 − flag`). -/
def KidAsserts {m : Nat} (M : Fp) (T : List (Fin m → Fp)) (c : KidB m) : Prop :=
  (c.level - M) * (1 - c.flag M) = 0 ∧ c.sel.length = T.length ∧
    (∀ s ∈ c.sel, s * (1 - s) = 0) ∧ (fsum c.sel - 1) * (1 - c.flag M) = 0 ∧
    ∀ j, facc (c.root j) c.sel (T.map (· j)) * (1 - c.flag M) = 0

/-- **The node's binding asserts**: per child `KidAsserts`; siblings `flag·(root_i − root_0) = 0`;
`build_agg`'s "children at the same level". -/
def NodeBindAsserts {m k : Nat} (M : Fp) (T : List (Fin m → Fp)) (kids : Fin (k + 1) → KidB m) :
    Prop :=
  (∀ i, KidAsserts M T (kids i)) ∧ (∀ i j, ((kids i).root j - (kids 0).root j) * (kids i).flag M = 0) ∧
    ∀ i, (kids i).level = (kids 0).level

theorem flag_zero {m : Nat} {M : Fp} {c : KidB m} (h : c.level = M) : c.flag M = 0 := by
  simp only [KidB.flag, h]; grind

theorem flag_one {m : Nat} {M : Fp} {c : KidB m} (h : c.level ≠ M)
    (ha : (c.level - M) * (1 - c.flag M) = 0) : c.flag M = 1 := by
  have : c.level - M ≠ 0 := fun e => h (by grind)
  grind

/-- **Program binding of a node's children.** Either every child is at the anchor level and its
program root is one of the pinned `C_t`, or no child is, every child has child 0's root, and child
0 is BIND-bound. `Bound` is what BIND's region proves for child 0 (its program evaluates to the
node's own at the child's point; open: BIND faithfulness). -/
theorem node_bind {m k : Nat} (M : Fp) (T : List (Fin m → Fp)) (hT : T.length < P)
    (kids : Fin (k + 1) → KidB m) (Bound : Prop) (h : NodeBindAsserts M T kids)
    (hBind : (kids 0).flag M = 1 → Bound) :
    (∀ i, (kids i).level = M ∧ (kids i).root ∈ T) ∨
      ((∀ i, (kids i).level ≠ M ∧ (kids i).root = (kids 0).root) ∧ Bound) := by
  obtain ⟨hk, hs, hl⟩ := h
  by_cases h0 : (kids 0).level = M
  · left
    intro i
    have hli : (kids i).level = M := (hl i).trans h0
    obtain ⟨-, hlen, hb, hsum, hacc⟩ := hk i
    have hf := flag_zero (c := kids i) hli
    rw [hf] at hsum hacc
    have hb' : ∀ s ∈ (kids i).sel, s = 0 ∨ s = 1 := fun s hs => bool_cases (hb s hs)
    have h1 : fsum (kids i).sel = 1 := by grind
    refine ⟨hli, sel_mem _ _ T hlen hb' (ones_of_fsum _ hb' (hlen ▸ hT) h1) (fun j => ?_)⟩
    have := hacc j
    grind
  · right
    have hf : ∀ i, (kids i).flag M = 1 := fun i =>
      flag_one (fun e => h0 ((hl i).symm.trans e)) (hk i).1
    refine ⟨fun i => ⟨fun e => h0 ((hl i).symm.trans e), ?_⟩, hBind (hf 0)⟩
    funext j
    have := hs i j
    rw [hf i] at this
    grind

/-! ## Leaves: the template normaliser and PAD (`build_norm`, `build_pad`) -/

/-- `build_norm`'s exposed cells: `ctx` = the template child's statement digest limbs,
`e = a + 1`, `s_a = [init, class]`, `s_e = [done, class]` (class a program constant). -/
def normCell (ctx : List Fp) (a cls : Fp) : SCell := ⟨ctx, a, a + 1, [phInit, cls], [phDone, cls]⟩

/-- `build_pad`'s exposed cells: witness `(ctx, a, s)`, exposes `(ctx, a, a + 1, s, s)`. -/
def padCell (ctx : List Fp) (a : Fp) (s : List Fp) : SCell := ⟨ctx, a, a + 1, s, s⟩

/-- `build_pad`'s assert `s[0] = done`. -/
def PadAssert (s : List Fp) : Prop := s.head? = some phDone

/-- A normaliser leaf's statement (boundaries as raw cells). -/
def IsNorm (st : Stmt (List Fp)) : Prop := ∃ cls, st.sa = [phInit, cls] ∧ st.se = [phDone, cls]

/-- A PAD leaf's statement: identity on a done boundary. -/
def IsPad (st : Stmt (List Fp)) : Prop := st.sa = st.se ∧ st.sa.head? = some phDone

theorem normCell_isNorm (ctx : List Fp) (a cls : Fp) : IsNorm ((normCell ctx a cls).stmt id) :=
  ⟨cls, rfl, rfl⟩

theorem padCell_isPad (ctx : List Fp) (a : Fp) (s : List Fp) (h : PadAssert s) :
    IsPad ((padCell ctx a s).stmt id) := ⟨rfl, h⟩

/-- After a done end boundary, a chainable run of normaliser/PAD leaves is all PADs, and each
keeps that end boundary. -/
theorem tail_pads : ∀ (prev : Stmt (List Fp)) (rest : List (Stmt (List Fp))),
    Chainable (prev :: rest) → prev.se.head? = some phDone → (∀ x ∈ rest, IsNorm x ∨ IsPad x) →
      ∀ x ∈ rest, IsPad x ∧ x.se = prev.se
  | _, [], _, _, _ => fun _ hx => absurd hx (by simp)
  | prev, y :: rest, hc, hd, hk => by
    obtain ⟨⟨-, -, hsa⟩, hc'⟩ := hc
    have hy : IsPad y := by
      rcases hk y List.mem_cons_self with ⟨cls, h1, -⟩ | hp
      · exfalso
        rw [hsa] at h1
        rw [h1] at hd
        exact phInit_ne_phDone (Option.some.inj hd)
      · exact hp
    have hyse : y.se = prev.se := hy.1.symm.trans hsa
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨hy, hyse⟩
    · have := tail_pads y rest hc' (hyse ▸ hd) (fun z hz => hk z (List.mem_cons_of_mem _ hz)) x hx
      exact ⟨this.1, this.2.trans hyse⟩

/-- **Exactly one template.** A chainable leaf sequence of normalisers and PADs that starts at an
`init` boundary (the wrap's check) is one normaliser followed only by PADs, and its root
statement is the normaliser's `init → done` statement with the leaves' context and range. -/
theorem one_template (l : List (Stmt (List Fp))) (hc : Chainable l)
    (hk : ∀ x ∈ l, IsNorm x ∨ IsPad x) (n : Stmt (List Fp)) (rest : List (Stmt (List Fp)))
    (hl : l = n :: rest) (hi : n.sa.head? = some phInit) :
    IsNorm n ∧ (∀ x ∈ rest, IsPad x) ∧
      ∃ cls, root l = some ⟨n.ctx, n.a, (rest.getLast?.getD n).e, [phInit, cls], [phDone, cls]⟩ := by
  subst hl
  have hn : IsNorm n := by
    rcases hk n List.mem_cons_self with h | ⟨h1, h2⟩
    · exact h
    · exfalso; rw [hi] at h2; exact phInit_ne_phDone (Option.some.inj h2)
  obtain ⟨cls, hsa, hse⟩ := hn
  have hd : n.se.head? = some phDone := by rw [hse]; rfl
  have hp := tail_pads n rest hc hd (fun x hx => hk x (List.mem_cons_of_mem _ hx))
  refine ⟨⟨cls, hsa, hse⟩, fun x hx => (hp x hx).1, cls, ?_⟩
  have hlast : (rest.getLast?.getD n).se = n.se := by
    cases h : rest.getLast? with
    | none => rfl
    | some y => exact (hp y (List.mem_of_getLast? h)).2
  simp only [root, hsa, ← hse, hlast]

/-! ## The wrap (`build_wrap`) -/

/-- `WRAP_MARKER = 0x57524150 mod p`. -/
def wrapMarker : Fp := Fp.ofNat (0x5752_4150 % 0x7800_0001)

/-- The wrap statement message `[WRAP_MARKER, n_ctx, ctx.., class]`. -/
def wmsg (ctx : List Fp) (cls : Fp) : List Fp := [wrapMarker, Fp.ofNat nCtxT] ++ ctx ++ [cls]

/-- **The wrap message is injective** at a fixed context length (`n_ctx` is the constant 18, not
the length, so the length must be fixed: `List.ofFn` over `Fin 18` in the program). -/
theorem wmsg_inj {c c' : List Fp} {x x' : Fp} (hl : c.length = c'.length)
    (h : wmsg c x = wmsg c' x') : c = c' ∧ x = x' := by
  simp only [wmsg, List.cons_append, List.nil_append, List.cons.injEq] at h
  obtain ⟨-, -, h⟩ := h
  obtain ⟨h1, h2⟩ := List.append_inj h hl
  exact ⟨h1, by simpa using h2⟩

/-- The wrap program's cells in a trace: the root statement preimage (fixed shape), the root
proof and public values, the root's exposed level and program root, the digest of the root
statement's `hash_range` job, and the digest of the `D_wrap` job. -/
structure WrapReadT (m : Nat) (Dg DgW Proof : Type) where
  ctx : Fin 18 → Fp
  a : Fp
  e : Fp
  sa : Fin 2 → Fp
  se : Fin 2 → Fp
  proof : Proof
  pv : List Fp
  level : Fp
  root : Fin m → Fp
  rootDig : Dg
  wrapDig : DgW

variable {m : Nat} {Dg DgW Proof : Type}

def WrapReadT.cell (R : WrapReadT m Dg DgW Proof) : SCell :=
  ⟨List.ofFn R.ctx, R.a, R.e, List.ofFn R.sa, List.ofFn R.se⟩

/-- **The wrap's components** (`build_wrap`, forced anchor `(root_level, C_node)`):
* SHA: the root statement's tag-9 job and the `D_wrap` tag-8 job are the native digests;
* inner: the root proof is accepted with those public values;
* asserts: root level forced, program root `= C_node`, root digest link, `a = 0`,
  `B_0.phase = init`, `B_N.phase = done`;
* tape: the public digest is the `D_wrap` cells. -/
def WrapCompT (rdigest : Stmt (List Fp) → Dg) (wdigest : List Fp → DgW)
    (InnerAcc : Proof → List Fp → Prop) (pvDig : List Fp → Dg) (rootLevel : Fp) (cNode : Fin m → Fp)
    (pubDig : List Fp → DgW) (R : WrapReadT m Dg DgW Proof) (pub : List Fp) : Prop :=
  R.rootDig = rdigest (R.cell.stmt id) ∧ R.wrapDig = wdigest (wmsg (List.ofFn R.ctx) (R.sa 1)) ∧
    InnerAcc R.proof R.pv ∧ R.level = rootLevel ∧ R.root = cNode ∧ R.rootDig = pvDig R.pv ∧
    R.a = 0 ∧ R.sa 0 = phInit ∧ R.se 0 = phDone ∧ pubDig pub = R.wrapDig

/-- A collision of `wdigest` on wrap messages. -/
def WColl (wdigest : List Fp → DgW) : Prop :=
  ∃ c c' x x', c.length = c'.length ∧ (c ≠ c' ∨ x ≠ x') ∧ wdigest (wmsg c x) = wdigest (wmsg c' x')

/-- **Sub-obligation 6 for the new wrap.** V_d checks `pub = D_wrap(ctxOf s, clsOf s)` from the
claimed public statement. Then the native wrap program (`aggWrapV`, with `InitOK` = start phase
`init` and class `clsOf s`, `FinalOK` = end phase `done`) accepts, or `wdigest` collides. -/
theorem wrapT_composition {ParamsW : Type} (rdigest : Stmt (List Fp) → Dg)
    (wdigest : List Fp → DgW) (InnerAcc : Proof → List Fp → Prop) (pvDig : List Fp → Dg)
    (segStmt : List Fp → Stmt (List Fp)) (Acc : Stmt (List Fp) → Proof → Prop)
    (hAcc : AccNative rdigest InnerAcc pvDig segStmt Acc) (rootLevel : Fp) (cNode : Fin m → Fp)
    (pubDig : List Fp → DgW) (ctxOf : PublicStmt → List Fp) (clsOf : PublicStmt → Fp)
    (hctx : ∀ s, (ctxOf s).length = 18) (R : WrapReadT m Dg DgW Proof) (pub : List Fp)
    (s : PublicStmt) (q : ParamsW)
    (h : WrapCompT rdigest wdigest InnerAcc pvDig rootLevel cNode pubDig R pub)
    (hV : pubDig pub = wdigest (wmsg (ctxOf s) (clsOf s))) :
    (aggWrapV (Params := ParamsW) Acc ctxOf
        (fun s sa => sa.head? = some phInit ∧ sa[1]? = some (clsOf s))
        (fun _ se => se.head? = some phDone)).accepts s (R.cell.stmt id, R.proof) q PUnit.unit ∨
      WColl wdigest := by
  obtain ⟨hS, hW, hI, -, -, hL, -, hi, hd, hT⟩ := h
  have hacc : Acc (R.cell.stmt id) R.proof := hAcc.2 _ _ _ hI (hL.symm.trans hS)
  have hlen : (List.ofFn R.ctx).length = (ctxOf s).length := by rw [List.length_ofFn, hctx]
  by_cases hc : List.ofFn R.ctx = ctxOf s ∧ R.sa 1 = clsOf s
  · left
    refine ⟨hacc, hc.1, ⟨?_, ?_⟩, ?_⟩
    · show (List.ofFn R.sa).head? = some phInit
      simp [List.ofFn_succ, hi]
    · show (List.ofFn R.sa)[1]? = some (clsOf s)
      simp [List.ofFn_succ, hc.2]
    · show (List.ofFn R.se).head? = some phDone
      simp [List.ofFn_succ, hd]
  · right
    refine ⟨_, _, _, _, hlen, ?_, hW.symm.trans (hT.symm.trans hV)⟩
    by_cases h1 : List.ofFn R.ctx = ctxOf s
    · exact .inr fun h2 => hc ⟨h1, h2⟩
    · exact .inl h1

/-- **What remains for the new wrap**: the AIR executes `build_wrap` (open, as `WrapExec`). -/
def WrapExecT (PinW : NvPinned) (rdigest : Stmt (List Fp) → Dg) (wdigest : List Fp → DgW)
    (InnerAcc : Proof → List Fp → Prop) (pvDig : List Fp → Dg) (rootLevel : Fp)
    (cNode : Fin m → Fp) (pubDig : List Fp → DgW) (R : Trace Fp → WrapReadT m Dg DgW Proof) :
    Prop :=
  ∀ tr pub, HoldsLogUp PinW.air pub tr →
    WrapCompT rdigest wdigest InnerAcc pvDig rootLevel cNode pubDig (R tr) pub

/-! ## Non-vacuity -/

/-- A one-template, two-PAD leaf sequence passes `one_template`'s hypotheses. -/
example : let n : Stmt (List Fp) := ⟨[5], 0, 1, [phInit, 3], [phDone, 3]⟩
    let p1 : Stmt (List Fp) := ⟨[5], 1, 2, [phDone, 3], [phDone, 3]⟩
    let p2 : Stmt (List Fp) := ⟨[5], 2, 3, [phDone, 3], [phDone, 3]⟩
    Chainable [n, p1, p2] ∧ (∀ x ∈ [n, p1, p2], IsNorm x ∨ IsPad x) := by
  refine ⟨⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, trivial⟩, ?_⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact .inl ⟨3, rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

/-- Two templates in a row do not chain: the second starts at `init`, the first ends at `done`. -/
example : ¬ Chainable [(⟨[5], 0, 1, [phInit, 3], [phDone, 3]⟩ : Stmt (List Fp)),
    ⟨[5], 1, 2, [phInit, 3], [phDone, 3]⟩] := by
  rintro ⟨⟨-, -, h⟩, -⟩
  exact phInit_ne_phDone (List.cons.inj h).1

/-- The binding asserts are satisfiable at the anchor level: one child, set `{c}`, selector `[1]`. -/
example : NodeBindAsserts (k := 0) (m := 1) 1 [fun _ => 7] (fun _ => ⟨1, 0, [1], fun _ => 7⟩) := by
  refine ⟨fun _ => ⟨?_, rfl, ?_, ?_, ?_⟩, fun _ _ => ?_, fun _ => rfl⟩ <;>
    simp [KidB.flag, fsum, facc] <;> grind

#print axioms sel_mem
#print axioms node_bind
#print axioms tail_pads
#print axioms one_template
#print axioms wmsg_inj
#print axioms wrapT_composition

end ZkFormal.PQ.E2ETree
