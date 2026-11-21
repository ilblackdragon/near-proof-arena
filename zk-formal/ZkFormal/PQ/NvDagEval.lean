import ZkFormal.PQ.NvField

/-!
# ZkFormal.PQ.NvDagEval — evaluating an exported DAG on a concrete row, by kernel computation

Lane E (E2E M11g, item 1), 2026-11-04.

To check a concrete trace (`NvHonest.lean`) against the exported NvAir, every one of its 4,518
DAG nodes must be evaluated per row. Expanding the DAG into expression trees (`dag j`) per row is
too expensive for the kernel (M11f: 50 GB). This file evaluates the DAG **in topological order with
a value store** (`St`: blocks of 64 values, most recent first, so a child lookup costs about
`(distance / 64) + 64` steps instead of the distance) over `Nat` mod `p`, and proves the result
equal to the expression semantics:

* `run_toList`: the store after `run` is the specification `specVals` (each node's value from the
  values of its children, read by index);
* `dag_eval_spec`: for a topologically ordered DAG (`topoOK`, decidable), node `i`'s expression
  `toExprOf nodes (i + 1) i` evaluates on a row to the cast of `specVals`'s `i`-th entry, when the
  row's cells, public values and selectors are the casts of the environment's;
* `rowOK_sound`: `rowOK env = true` (all constraints' values are `0`) gives every exported
  constraint `= 0` on that row.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace ZkFormal.PQ.NvDagEval

open ZkFormal.Air ZkFormal.Algebra ZkFormal.PQ.NvAirExport ZkFormal.PQ.NvField

set_option maxRecDepth 100000

/-- A row environment over `Nat`: current and next row, public values, selectors. -/
structure Env where
  loc : List Nat
  nxt : List Nat
  pv : List Nat
  fst : Nat
  lst : Nat
  trn : Nat

/-- The value of a node from its children's values (`get`), reduced mod `p`. -/
def nval (env : Env) (get : Nat → Nat) : DagNode → Nat
  | .v c nx => (if nx then env.nxt else env.loc).getD c 0 % P
  | .p j => env.pv.getD j 0 % P
  | .k n => n % P
  | .add a b => (get a + get b) % P
  | .sub a b => (get a + (P - get b)) % P
  | .mul a b => (get a * get b) % P
  | .neg a => (P - get a) % P
  | .first => env.fst % P
  | .last => env.lst % P
  | .trans => env.trn % P

/-- The children of a node. -/
def kids : DagNode → List Nat
  | .add a b | .sub a b | .mul a b => [a, b]
  | .neg a => [a]
  | _ => []

/-- Topological order: every child index is smaller than its node's. -/
def topoOK : List DagNode → Nat → Bool
  | [], _ => true
  | x :: xs, i => (kids x).all (· < i) && topoOK xs (i + 1)

/-! ## The value store -/

structure St where
  blocks : List (List Nat)
  cur : List Nat
  n : Nat

def St.get (s : St) (i : Nat) : Nat :=
  if i / 64 = s.n / 64 then s.cur.getD (s.n % 64 - 1 - i % 64) 0
  else (s.blocks.getD (s.n / 64 - 1 - i / 64) []).getD (i % 64) 0

def St.push (s : St) (v : Nat) : St :=
  if s.n % 64 = 63 then ⟨(v :: s.cur).reverse :: s.blocks, [], s.n + 1⟩
  else ⟨s.blocks, v :: s.cur, s.n + 1⟩

def St.toList (s : St) : List Nat := s.blocks.reverse.flatten ++ s.cur.reverse

def St.Inv (s : St) : Prop :=
  s.blocks.length = s.n / 64 ∧ s.cur.length = s.n % 64 ∧ ∀ b ∈ s.blocks, b.length = 64

def St.empty : St := ⟨[], [], 0⟩

theorem empty_inv : St.empty.Inv := ⟨rfl, rfl, by simp [St.empty]⟩

theorem push_toList (s : St) (v : Nat) : (s.push v).toList = s.toList ++ [v] := by
  unfold St.push
  split <;> simp [St.toList]

theorem push_inv (s : St) (v : Nat) (h : s.Inv) : (s.push v).Inv ∧ (s.push v).n = s.n + 1 := by
  obtain ⟨hb, hc, hl⟩ := h
  unfold St.push
  split
  · next h63 =>
    refine ⟨⟨?_, ?_, ?_⟩, rfl⟩
    · show (_ :: s.blocks).length = (s.n + 1) / 64
      simp only [List.length_cons, hb]; omega
    · show ([] : List Nat).length = (s.n + 1) % 64
      simp only [List.length_nil]; omega
    · intro b hbm
      rcases List.mem_cons.1 hbm with rfl | hbm
      · simp only [List.length_reverse, List.length_cons, hc]; omega
      · exact hl b hbm
  · next h63 =>
    refine ⟨⟨?_, ?_, hl⟩, rfl⟩
    · show s.blocks.length = (s.n + 1) / 64
      rw [hb]; omega
    · show (v :: s.cur).length = (s.n + 1) % 64
      simp only [List.length_cons, hc]; omega

theorem flatten_getD (bs : List (List Nat)) (hl : ∀ b ∈ bs, b.length = 64) :
    ∀ i, i < 64 * bs.length → bs.flatten.getD i 0 = (bs.getD (i / 64) []).getD (i % 64) 0 := by
  induction bs with
  | nil => intro i h; simp at h
  | cons b bs ih =>
    intro i h
    have hb := hl b List.mem_cons_self
    simp only [List.flatten_cons, List.getD_eq_getElem?_getD]
    by_cases hi : i < 64
    · rw [List.getElem?_append_left (by omega), Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
      simp
    · rw [List.getElem?_append_right (by omega), hb]
      have := ih (fun b' hb' => hl b' (List.mem_cons_of_mem _ hb')) (i - 64)
        (by simp only [List.length_cons] at h; omega)
      simp only [List.getD_eq_getElem?_getD] at this
      rw [this]
      have h1 : i / 64 = (i - 64) / 64 + 1 := by omega
      have h2 : i % 64 = (i - 64) % 64 := by omega
      rw [h1, h2]
      simp

theorem toList_length (s : St) (h : s.Inv) : s.toList.length = s.n := by
  obtain ⟨hb, hc, hl⟩ := h
  have : s.blocks.reverse.flatten.length = 64 * s.blocks.length := by
    rw [List.length_flatten]
    have : ∀ bs : List (List Nat), (∀ b ∈ bs, b.length = 64) →
        (bs.map List.length).sum = 64 * bs.length := by
      intro bs
      induction bs with
      | nil => simp
      | cons b bs ih =>
        intro hl'
        simp only [List.map_cons, List.sum_cons, List.length_cons,
          hl' b List.mem_cons_self, ih (fun b' hb' => hl' b' (List.mem_cons_of_mem _ hb'))]
        omega
    rw [this _ (fun b hb => hl b (List.mem_reverse.1 hb)), List.length_reverse]
  simp only [St.toList, List.length_append, this, List.length_reverse, hb, hc]
  omega

/-- **The store's lookup is the list's.** -/
theorem get_eq (s : St) (h : s.Inv) {i : Nat} (hi : i < s.n) :
    s.get i = s.toList.getD i 0 := by
  obtain ⟨hb, hc, hl⟩ := h
  have hfl : s.blocks.reverse.flatten.length = 64 * (s.n / 64) := by
    have := toList_length s ⟨hb, hc, hl⟩
    simp only [St.toList, List.length_append, List.length_reverse, hc] at this
    omega
  unfold St.get St.toList
  split
  · next heq =>
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), hfl, List.getElem?_reverse (by rw [hc]; omega), hc]
    congr 2
    omega
  · next hne =>
    have hlt : i < 64 * (s.n / 64) := by omega
    have e1 : (s.blocks.reverse.flatten ++ s.cur.reverse).getD i 0 =
        s.blocks.reverse.flatten.getD i 0 := by
      simp only [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left (by omega)]
    rw [e1, flatten_getD _ (fun b hb' => hl b (List.mem_reverse.1 hb')) i
      (by rw [List.length_reverse, hb]; exact hlt)]
    congr 1
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_reverse (by rw [hb]; omega), hb]

/-! ## The evaluation and its specification -/

/-- Evaluate the nodes in order, pushing each value. -/
def run (env : Env) : List DagNode → St → St
  | [], s => s
  | x :: xs, s => run env xs (s.push (nval env s.get x))

/-- The specification: each node's value from the list of earlier values. -/
def specVals (env : Env) : List DagNode → List Nat → List Nat
  | [], acc => acc
  | x :: xs, acc => specVals env xs (acc ++ [nval env (fun i => acc.getD i 0) x])

theorem nval_congr (env : Env) (g1 g2 : Nat → Nat) (x : DagNode)
    (h : ∀ a ∈ kids x, g1 a = g2 a) : nval env g1 x = nval env g2 x := by
  cases x <;> simp_all [nval, kids]

theorem run_toList (env : Env) : ∀ (xs : List DagNode) (s : St), s.Inv →
    topoOK xs s.n = true →
      (run env xs s).toList = specVals env xs s.toList ∧ (run env xs s).Inv
  | [], s, h, _ => ⟨rfl, h⟩
  | x :: xs, s, h, ht => by
    simp only [topoOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
    have hv : nval env s.get x = nval env (fun i => s.toList.getD i 0) x :=
      nval_congr env _ _ x (fun a ha => get_eq s h (ht.1 a ha))
    obtain ⟨hi, hn⟩ := push_inv s (nval env s.get x) h
    have ih := run_toList env xs (s.push (nval env s.get x)) hi (by rw [hn]; exact ht.2)
    refine ⟨?_, ih.2⟩
    show (run env xs (s.push (nval env s.get x))).toList = _
    rw [ih.1, push_toList, hv]
    rfl

theorem specVals_prefix (env : Env) : ∀ (xs : List DagNode) (acc : List Nat),
    ∃ rest, specVals env xs acc = acc ++ rest ∧ rest.length = xs.length
  | [], acc => ⟨[], by simp [specVals]⟩
  | x :: xs, acc => by
    obtain ⟨rest, h, hl⟩ := specVals_prefix env xs (acc ++ [nval env (fun i => acc.getD i 0) x])
    refine ⟨nval env (fun i => acc.getD i 0) x :: rest, ?_, by simp [hl]⟩
    show specVals env xs _ = _
    rw [h]; simp

/-- Entry `i` of the specification: node `i`'s value from the final list (children are earlier). -/
theorem specVals_get (env : Env) : ∀ (xs : List DagNode) (acc : List Nat),
    topoOK xs acc.length = true → ∀ k, k < xs.length →
      (specVals env xs acc).getD (acc.length + k) 0 =
        nval env (fun i => (specVals env xs acc).getD i 0) (xs.getD k (.k 0))
  | [], _, _, k, hk => by simp at hk
  | x :: xs, acc, ht, k, hk => by
    simp only [topoOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ht
    have hx : ∀ a ∈ kids x, (specVals env (x :: xs) acc).getD a 0 = acc.getD a 0 := by
      intro a ha
      obtain ⟨rest, h, -⟩ := specVals_prefix env (x :: xs) acc
      rw [h]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (ht.1 a ha)]
    cases k with
    | zero =>
      obtain ⟨rest, h, -⟩ := specVals_prefix env xs (acc ++ [nval env (fun i => acc.getD i 0) x])
      have e : (specVals env (x :: xs) acc).getD (acc.length + 0) 0 =
          nval env (fun i => acc.getD i 0) x := by
        show (specVals env xs _).getD _ 0 = _
        rw [h]
        simp only [List.getD_eq_getElem?_getD, Nat.add_zero, List.append_assoc,
          List.singleton_append]
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      rw [e]
      show _ = nval env _ x
      exact (nval_congr env _ _ x hx).symm
    | succ k =>
      have := specVals_get env xs (acc ++ [nval env (fun i => acc.getD i 0) x])
        (by simpa using ht.2) k (by simpa using hk)
      simp only [List.length_append, List.length_singleton] at this
      show (specVals env xs _).getD _ 0 = nval env (fun i => (specVals env xs _).getD i 0) _
      rw [show acc.length + (k + 1) = acc.length + 1 + k by omega, this]
      rfl

/-! ## Agreement with the expression semantics -/

theorem cast_mod (a : Nat) : ((a % P : Nat) : Fp) = ((a : Nat) : Fp) := by
  apply Fp.ext
  show (Fp.ofNat (a % P)).toNat = (Fp.ofNat a).toNat
  simp only [Fp.toNat_ofNat, Nat.mod_mod]

theorem cast_P : ((P : Nat) : Fp) = 0 := by
  apply Fp.ext
  show (Fp.ofNat P).toNat = (0 : Fp).toNat
  simp only [Fp.toNat_ofNat, Nat.mod_self]
  rfl

theorem cast_sub (b : Nat) (hb : b ≤ P) : ((P - b : Nat) : Fp) = -((b : Nat) : Fp) := by
  have h : ((P - b : Nat) : Fp) + ((b : Nat) : Fp) = 0 := by
    rw [← Lean.Grind.Semiring.natCast_add, Nat.sub_add_cancel hb, cast_P]
  grind

theorem nval_lt (env : Env) (g : Nat → Nat) (x : DagNode) : nval env g x < P := by
  cases x <;> simp only [nval] <;> exact Nat.mod_lt _ (by decide)

/-- The row agrees with the environment. -/
def RowAgrees (env : Env) (tr : Trace Fp) (t r : Nat) (pub : List Fp) : Prop :=
  (∀ c, tr.cell t r c = ((env.loc.getD c 0 : Nat) : Fp)) ∧
  (∀ c, tr.cell t ((r + 1) % tr.height t) c = ((env.nxt.getD c 0 : Nat) : Fp)) ∧
  (∀ j, pub.getD j 0 = ((env.pv.getD j 0 : Nat) : Fp)) ∧
  (if r = 0 then (1 : Fp) else 0) = ((env.fst : Nat) : Fp) ∧
  (if r + 1 = tr.height t then (1 : Fp) else 0) = ((env.lst : Nat) : Fp) ∧
  (if r + 1 = tr.height t then (0 : Fp) else 1) = ((env.trn : Nat) : Fp)

/-- **The expression of node `i` evaluates to the specification's value.** -/
theorem dag_eval_spec (nodes : List DagNode) (env : Env) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (hra : RowAgrees env tr t r pub) (ht : topoOK nodes 0 = true) :
    ∀ f i, i < f → i < nodes.length →
      (toExprOf nodes f i).eval tr t r pub =
        (((specVals env nodes []).getD i 0 : Nat) : Fp)
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | f + 1, i, hi, hn => by
    have hs := specVals_get env nodes [] (by simpa using ht) i hn
    simp only [List.length_nil, Nat.zero_add] at hs
    rw [hs]
    have htopo : ∀ a ∈ kids (nodes.getD i (.k 0)), a < i := by
      have : ∀ (xs : List DagNode) (s : Nat), topoOK xs s = true → ∀ k, k < xs.length →
          ∀ a ∈ kids (xs.getD k (.k 0)), a < s + k := by
        intro xs
        induction xs with
        | nil => intro s _ k hk; simp at hk
        | cons x xs ih =>
          intro s h k hk a ha
          simp only [topoOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
          cases k with
          | zero => simpa using h.1 a ha
          | succ k =>
            have := ih (s + 1) h.2 k (by simpa using hk) a ha
            omega
      simpa using this nodes 0 ht i hn
    have ih : ∀ a ∈ kids (nodes.getD i (.k 0)),
        (toExprOf nodes f a).eval tr t r pub = (((specVals env nodes []).getD a 0 : Nat) : Fp) :=
      fun a ha => dag_eval_spec nodes env tr t r pub hra ht f a (by have := htopo a ha; omega)
        (by have := htopo a ha; omega)
    have lt : ∀ a, (specVals env nodes []).getD a 0 ≤ P := by
      intro a
      by_cases ha : a < nodes.length
      · have := specVals_get env nodes [] (by simpa using ht) a ha
        simp only [List.length_nil, Nat.zero_add] at this
        rw [this]; exact Nat.le_of_lt (nval_lt _ _ _)
      · obtain ⟨rest, h, hl⟩ := specVals_prefix env nodes []
        rw [h]; simp only [List.nil_append, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]; simp
    obtain ⟨hloc, hnxt, hpv, hf, hl, htr⟩ := hra
    simp only [toExprOf]
    cases hx : nodes.getD i (.k 0) with
    | v c nx =>
      cases nx with
      | false =>
        show tr.cell t r c = _
        simp only [nval, if_false, Bool.false_eq_true, cast_mod, hloc]
      | true =>
        show tr.cell t ((r + 1) % tr.height t) c = _
        simp only [nval, if_true, cast_mod, hnxt]
    | p j => show pub.getD j 0 = _; simp only [nval, cast_mod, hpv]
    | k n => show ((n : Nat) : Fp) = _; simp only [nval, cast_mod]
    | add a b =>
      rw [hx] at ih
      show (toExprOf nodes f a).eval tr t r pub + (toExprOf nodes f b).eval tr t r pub = _
      rw [ih a (by simp [kids]), ih b (by simp [kids])]
      simp only [nval, cast_mod, Lean.Grind.Semiring.natCast_add]
    | sub a b =>
      rw [hx] at ih
      show (toExprOf nodes f a).eval tr t r pub + -(toExprOf nodes f b).eval tr t r pub = _
      rw [ih a (by simp [kids]), ih b (by simp [kids])]
      simp only [nval, cast_mod, Lean.Grind.Semiring.natCast_add, cast_sub _ (lt b)]
    | mul a b =>
      rw [hx] at ih
      show (toExprOf nodes f a).eval tr t r pub * (toExprOf nodes f b).eval tr t r pub = _
      rw [ih a (by simp [kids]), ih b (by simp [kids])]
      simp only [nval, cast_mod, Lean.Grind.Semiring.natCast_mul]
    | neg a =>
      rw [hx] at ih
      show -(toExprOf nodes f a).eval tr t r pub = _
      rw [ih a (by simp [kids])]
      simp only [nval, cast_mod, cast_sub _ (lt a)]
    | first => show (if r = 0 then (1 : Fp) else 0) = _; simp only [nval, cast_mod, hf]
    | last => show (if r + 1 = tr.height t then (1 : Fp) else 0) = _; simp only [nval, cast_mod, hl]
    | trans => show (if r + 1 = tr.height t then (0 : Fp) else 1) = _; simp only [nval, cast_mod, htr]

/-- **A row check**: run the store over NvAir's nodes; every constraint's value is `0`. -/
def rowOK (env : Env) : Bool :=
  let s := run env nvNodes St.empty
  nvConstraintIdx.all fun j => s.get j == 0

theorem nv_topo : topoOK nvNodes 0 = true := by decide +kernel
theorem nv_len : nvNodes.length = 4518 := by decide +kernel
theorem nv_cons_lt : nvConstraintIdx.all (· < 4518) = true := by decide

/-- **`rowOK` is sound**: every exported constraint vanishes on the row. -/
theorem rowOK_sound (env : Env) (tr : Trace Fp) (r : Nat) (pub : List Fp)
    (hra : RowAgrees env tr 0 r pub) (h : rowOK env = true) :
    ∀ j ∈ nvConstraintIdx, (NvTape.dag j).eval tr 0 r pub = 0 := by
  intro j hj
  have hjl : j < nvNodes.length := by
    rw [nv_len]; exact of_decide_eq_true (List.all_eq_true.1 nv_cons_lt j hj)
  have hr := run_toList env nvNodes St.empty empty_inv (by exact nv_topo)
  have hn : (run env nvNodes St.empty).n = nvNodes.length := by
    rw [← toList_length _ hr.2, hr.1]
    obtain ⟨rest, h, hl⟩ := specVals_prefix env nvNodes []
    simp only [St.toList, St.empty, List.reverse_nil, List.flatten_nil, List.append_nil] at h ⊢
    rw [h, List.nil_append, hl]
  have hz := List.all_eq_true.1 h j hj
  simp only [beq_iff_eq] at hz
  rw [get_eq _ hr.2 (by rw [hn]; exact hjl), hr.1] at hz
  have e := dag_eval_spec nvNodes env tr 0 r pub hra nv_topo (j + 1) j (by omega) hjl
  rw [← dagOf_nv] at *
  show (dagOf nvNodes j).eval tr 0 r pub = 0
  unfold dagOf
  rw [e]
  have : St.empty.toList = [] := rfl
  rw [this] at hz
  rw [hz]; rfl

#print axioms run_toList
#print axioms dag_eval_spec
#print axioms rowOK_sound

end ZkFormal.PQ.NvDagEval
