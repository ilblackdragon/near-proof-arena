import NearSpecV3.Wasm.FuelDefs
namespace NearSpecV3.Wasm.FuelGas
open NearSpecV3.Wasm

/-! ## `optimizeWith` as a list recursion -/

def goOpt (merge : Pt → Pt → Option Pt) : Pt → List Pt → List Pt
  | prev, [] => [prev]
  | prev, c :: cs =>
    match merge prev c with
    | some m => goOpt merge m cs
    | none => prev :: goOpt merge c cs

def optL (merge : Pt → Pt → Option Pt) : List Pt → List Pt
  | [] => []
  | p :: ps => goOpt merge p ps

def optBody (merge : Pt → Pt → Option Pt) (pts : Array Pt) (st : Array Pt × Pt) (i : Nat) :
    Array Pt × Pt :=
  match merge st.2 pts[i]! with
  | some mm => (st.1, mm)
  | none => (st.1.push st.2, pts[i]!)

theorem forIn'_opt (merge : Pt → Pt → Option Pt) (pts : Array Pt) :
    ∀ (l : List Nat) (f : (a : Nat) → a ∈ l → Array Pt × Pt → Id (ForInStep (Array Pt × Pt)))
      (hf : ∀ a h st, f a h st = pure (ForInStep.yield (optBody merge pts st a)))
      (st : Array Pt × Pt),
    forIn' l st f = l.foldl (optBody merge pts) st := by
  intro l
  induction l with
  | nil => intro f hf st; rfl
  | cons a l ih =>
    intro f hf st
    rw [List.forIn'_cons, hf]
    simp only [List.foldl_cons]
    exact ih _ (fun b hb st => hf b _ st) _

theorem optimizeWith_foldl (merge : Pt → Pt → Option Pt) (pts : Array Pt) :
    ∀ m k (out : Array Pt) (prev : Pt), k + m = pts.size →
      (let st := List.foldl (optBody merge pts) (out, prev) (List.range' k m)
       (st.1.push st.2).toList) = out.toList ++ goOpt merge prev (pts.toList.drop k) := by
  intro m
  induction m with
  | zero =>
    intro k out prev h
    simp [show pts.toList.drop k = [] by simp; omega, goOpt]
  | succ m ih =>
    intro k out prev h
    have hk : k < pts.size := by omega
    have hd : pts.toList.drop k = pts[k] :: pts.toList.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]; simp
    simp only [List.range'_succ, List.foldl_cons, hd, goOpt]
    have hg : pts[k]! = pts[k] := by simp [hk]
    simp only [optBody, hg]
    cases hm : merge prev pts[k] with
    | some mm => simpa using ih (k + 1) out mm (by omega)
    | none => simpa using ih (k + 1) (out.push prev) pts[k] (by omega)

theorem optimizeWith_eq (merge : Pt → Pt → Option Pt) (pts : Array Pt) :
    (optimizeWith pts merge).toList = optL merge pts.toList := by
  unfold optimizeWith
  cases h0 : pts[0]? with
  | none =>
    have : pts.size = 0 := by
      rcases Nat.eq_zero_or_pos pts.size with h | h
      · exact h
      · simp [Array.getElem?_eq_getElem h] at h0
    have h2 : pts.toList = [] := by simpa using this
    simp [optL, h2]; exact Array.eq_empty_of_size_eq_zero this
  | some p0 =>
    have hpos : 0 < pts.size := by
      rcases Nat.eq_zero_or_pos pts.size with h | h
      · simp [h] at h0
      · exact h
    have hp0 : pts[0] = p0 := by simpa [Array.getElem?_eq_getElem hpos] using h0
    have hl : pts.toList = p0 :: pts.toList.drop 1 := by
      rcases pts with ⟨_ | ⟨x, l⟩⟩
      · simp at hpos
      · simp at hp0 ⊢; exact hp0
    simp only [Std.Legacy.Range.forIn'_eq_forIn'_range']
    rw [forIn'_opt merge pts]
    rotate_left
    · intro a h st
      have ha : a < pts.size := by simp at h; omega
      have hg : pts[a]! = pts[a] := by simp [ha]
      simp only [optBody, hg]
      split <;> rename_i heq <;> simp [heq]
    have := optimizeWith_foldl merge pts (pts.size - 1) 1 #[] p0 (by omega)
    rw [hl]
    simp only [optL]
    simp only [Id.run] at this ⊢
    simp only [Array.toList_push] at this
    refine Eq.trans ?_ this
    have hs : [1:pts.size].size = pts.size - 1 := by simp [Std.Legacy.Range.size]
    rw [hs]
    exact Array.toList_push


/-! ## Pass 1: one point per offset -/

def m1 (a b : Pt) : Option Pt :=
  if a.off = b.off then (mergeSame a.k b.k).map fun k => ⟨a.off, k, a.fee.add b.fee⟩ else none

def m2 (a b : Pt) : Option Pt :=
  (mergeAcross a.k b.k).map fun k => ⟨Nat.min a.off b.off, k, a.fee.add b.fee⟩

theorem optimize_eq (pts : Array Pt) :
    optimize pts true = optimizeWith (optimizeWith pts m1) m2 := rfl

def flatB (bs : List (Option Pt × Pt)) : List Pt := bs.flatMap (fun b => b.1.toList ++ [b.2])

def mBlk (b : Option Pt × Pt) : Pt :=
  match b.1 with
  | none => b.2
  | some s => ⟨s.off, (mergeSame s.k b.2.k).getD .pure, s.fee.add b.2.fee⟩

def BOK (b : Option Pt × Pt) : Prop :=
  ∀ s, b.1 = some s → s.off = b.2.off ∧ (mergeSame s.k b.2.k).isSome

theorem m1_blk (b : Option Pt × Pt) (s : Pt) (hs : b.1 = some s) (h : BOK b) :
    m1 s b.2 = some (mBlk b) := by
  obtain ⟨h1, h2⟩ := h s hs
  unfold m1 mBlk
  rw [if_pos h1, hs]
  cases hm : mergeSame s.k b.2.k with
  | none => simp [hm] at h2
  | some k => simp [hm]

theorem mBlk_off (b : Option Pt × Pt) (h : BOK b) : (mBlk b).off = b.2.off := by
  unfold mBlk
  cases hb : b.1 with
  | none => rfl
  | some s => exact (h s hb).1

theorem goOpt_blocks : ∀ (bs : List (Option Pt × Pt)) (a : Nat) (prev : Pt),
    (∀ t (h : t < bs.length), bs[t].2.off = a + t ∧ BOK bs[t]) → prev.off < a →
    goOpt m1 prev (flatB bs) = prev :: bs.map mBlk := by
  intro bs
  induction bs with
  | nil => intro a prev _ _; rfl
  | cons b bs ih =>
    intro a prev hb hp
    obtain ⟨hb0, hbok⟩ := hb 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hb0 hbok
    have hrest : ∀ t (h : t < bs.length), bs[t].2.off = (a + 1) + t ∧ BOK bs[t] := by
      intro t ht
      have := hb (t + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      exact ⟨by omega, this.2⟩
    have hfl : flatB (b :: bs) = b.1.toList ++ b.2 :: flatB bs := by simp [flatB]
    rw [hfl]
    cases hb1 : b.1 with
    | none =>
      have hm : m1 prev b.2 = none := by unfold m1; rw [if_neg (by omega)]
      simp only [Option.toList_none, List.nil_append, goOpt, hm]
      rw [ih (a + 1) b.2 hrest (by omega)]
      simp [mBlk, hb1]
    | some sp =>
      have hso := (hbok sp hb1).1
      have hm : m1 prev sp = none := by unfold m1; rw [if_neg (by omega)]
      simp only [Option.toList_some, List.cons_append, List.nil_append, goOpt, hm]
      rw [m1_blk b sp hb1 hbok]
      simp only
      rw [ih (a + 1) (mBlk b) hrest (by rw [mBlk_off b hbok]; omega)]
      simp

theorem optL_blocks (bs : List (Option Pt × Pt)) (a : Nat)
    (hb : ∀ t (h : t < bs.length), bs[t].2.off = a + t ∧ BOK bs[t]) :
    optL m1 (flatB bs) = bs.map mBlk := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    obtain ⟨hb0, hbok⟩ := hb 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hb0 hbok
    have hrest : ∀ t (h : t < bs.length), bs[t].2.off = (a + 1) + t ∧ BOK bs[t] := by
      intro t ht
      have := hb (t + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      exact ⟨by omega, this.2⟩
    have hfl : flatB (b :: bs) = b.1.toList ++ b.2 :: flatB bs := by simp [flatB]
    rw [hfl]
    cases hb1 : b.1 with
    | none =>
      simp only [Option.toList_none, List.nil_append, optL]
      rw [goOpt_blocks bs (a + 1) b.2 hrest (by omega)]
      simp [mBlk, hb1]
    | some sp =>
      simp only [Option.toList_some, List.cons_append, List.nil_append, optL, goOpt]
      rw [m1_blk b sp hb1 hbok]
      simp only
      rw [goOpt_blocks bs (a + 1) (mBlk b) hrest (by rw [mBlk_off b hbok]; omega)]
      simp

/-! ## Pass 2: groups -/

def sumL (fc : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | len + 1 => fc a + sumL fc (a + 1) len

theorem sumL_succ' (fc : Nat → Nat) : ∀ len a, sumL fc a (len + 1) = sumL fc a len + fc (a + len) := by
  intro len
  induction len with
  | zero => intro a; simp [sumL]
  | succ len ih => intro a; rw [sumL, ih (a + 1), sumL]; simp [Nat.add_assoc, Nat.add_comm 1]

theorem sumL_mono (fc : Nat → Nat) (a : Nat) : ∀ l1 l2, l1 ≤ l2 → sumL fc a l1 ≤ sumL fc a l2 := by
  intro l1 l2 h
  induction l2 with
  | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | succ l2 ih =>
    rcases Nat.lt_or_ge l1 (l2 + 1) with h' | h'
    · rw [sumL_succ']; have := ih (by omega); omega
    · rw [show l1 = l2 + 1 by omega]; exact Nat.le_refl _

def starter : IK → Bool
  | .post | .between | .linear => true
  | _ => false

theorem m2_none_of_starter (a b : Pt) (h : starter b.k = true) : m2 a b = none := by
  unfold m2
  cases ha : a.k <;> cases hb : b.k <;> simp_all [starter, mergeAcross]

theorem mergeAcross_unreach (x y : IK) (h : mergeAcross x y = some .unreach) : x = .unreach := by
  cases x <;> cases y <;> simp_all [mergeAcross]

def SegQ (fc : Nat → Nat) (K : Nat → IK) (N : Nat) : List Pt → Nat → Prop
  | [], _ => False
  | [q], s => q.off = s ∧ (q.k = .unreach → K s = .unreach) ∧ s < N ∧ q.fee.c = sumL fc s (N - s)
  | q :: q' :: rest, s => q.off = s ∧ (q.k = .unreach → K s = .unreach) ∧ s < q'.off ∧
      q.fee.c = sumL fc s (q'.off - s) ∧ SegQ fc K N (q' :: rest) q'.off

theorem SegQ_head (fc K N) : ∀ (Q : List Pt) s, SegQ fc K N Q s → ∃ q rest, Q = q :: rest ∧ q.off = s
  | [], _, h => h.elim
  | [q], _, h => ⟨q, [], rfl, h.1⟩
  | q :: q' :: rest, _, h => ⟨q, q' :: rest, rfl, h.1⟩

theorem pass2 (fc : Nat → Nat) (K : Nat → IK) (N : Nat) : ∀ (cs : List Pt) (a : Nat) (prev : Pt),
    (∀ t (h : t < cs.length), cs[t].off = a + t ∧ cs[t].fee.c = fc (a + t) ∧ cs[t].k = K (a + t)) →
    N = a + cs.length → prev.off < a → prev.fee.c = sumL fc prev.off (a - prev.off) →
    (prev.k = .unreach → K prev.off = .unreach) →
    SegQ fc K N (goOpt m2 prev cs) prev.off ∧
      ∀ t, a ≤ t → t < N → starter (K t) = true → ∃ q ∈ goOpt m2 prev cs, q.off = t := by
  intro cs
  induction cs with
  | nil =>
    intro a prev _ hN hp hf hk
    simp only [List.length_nil, Nat.add_zero] at hN
    subst hN
    refine ⟨⟨rfl, hk, hp, hf⟩, fun t h1 h2 => by omega⟩
  | cons c cs ih =>
    intro a prev hc hN hp hf hk
    obtain ⟨hc0, hc1, hc2⟩ := hc 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hc0 hc1 hc2
    have hrest : ∀ t (h : t < cs.length), cs[t].off = (a + 1) + t ∧ cs[t].fee.c = fc ((a + 1) + t) ∧
        cs[t].k = K ((a + 1) + t) := by
      intro t ht
      have := hc (t + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      refine ⟨by omega, by rw [this.2.1]; congr 1; omega, by rw [this.2.2]; congr 1; omega⟩
    have hN' : N = (a + 1) + cs.length := by simp at hN; omega
    simp only [goOpt]
    cases hm : m2 prev c with
    | some m =>
      simp only
      have hm' := hm
      unfold m2 at hm'
      cases hk' : mergeAcross prev.k c.k with
      | none => simp [hk'] at hm'
      | some k =>
        simp only [hk', Option.map_some, Option.some.injEq] at hm'
        subst hm'
        have hmo : Nat.min prev.off c.off = prev.off := by
          simp only [Nat.min_def]; rw [if_pos (by omega)]
        rw [hmo]
        have := ih (a + 1) ⟨prev.off, k, prev.fee.add c.fee⟩ hrest hN'
          (by simp only; omega)
          (by
            simp only [Fee.add]
            rw [show a + 1 - prev.off = (a - prev.off) + 1 by omega, sumL_succ', ← hf, hc1]
            congr 2; omega)
          (by
            intro hu
            simp only at hu ⊢
            subst hu
            exact hk (mergeAcross_unreach _ _ hk'))
        refine ⟨this.1, fun t h1 h2 h3 => ?_⟩
        by_cases hta : t = a
        · subst hta
          have : m2 prev c = none := m2_none_of_starter prev c (by rw [hc2]; exact h3)
          rw [hm] at this; cases this
        · exact this.2 t (by omega) h2 h3
    | none =>
      simp only
      have := ih (a + 1) c hrest hN' (by omega)
        (by rw [hc0, hc1, show a + 1 - a = 1 by omega]; simp [sumL])
        (by rw [hc0, hc2]; exact id)
      rw [hc0] at this
      obtain ⟨q, rest, hq, hqo⟩ := SegQ_head fc K N _ _ this.1
      refine ⟨?_, ?_⟩
      · rw [hq]; rw [hq] at this
        exact ⟨rfl, hk, by omega, by rw [hqo]; exact hf, by rw [hqo]; exact this.1⟩
      · intro t h1 h2 h3
        by_cases hta : t = a
        · exact ⟨q, by rw [hq]; simp, by omega⟩
        · obtain ⟨q', hq', hq'o⟩ := this.2 t (by omega) h2 h3
          exact ⟨q', List.mem_cons_of_mem _ hq', hq'o⟩


def SegP (fc : Nat → Nat) (K : Nat → IK) (N : Nat) (Q : List Pt) (s : Nat) : Prop :=
  (∀ q ∈ Q, s ≤ q.off ∧ q.off < N) ∧ Q.Pairwise (fun x y => x.off < y.off) ∧
  ∀ q ∈ Q, (q.k = .unreach → K q.off = .unreach) ∧ ∃ nx, q.off < nx ∧ nx ≤ N ∧
    q.fee.c = sumL fc q.off (nx - q.off) ∧ (∀ t, q.off < t → t < nx → ∀ q' ∈ Q, q'.off ≠ t) ∧
    (nx = N ∨ ∃ q' ∈ Q, q'.off = nx)

theorem SegQ_props (fc K N) : ∀ (Q : List Pt) s, SegQ fc K N Q s → SegP fc K N Q s
  | [], _, h => h.elim
  | [q], s, h => by
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨?_, by simp, ?_⟩
    · intro x hx; simp at hx; subst hx; omega
    · intro x hx; simp at hx; subst hx
      refine ⟨by rw [h1]; exact h2, N, by omega, Nat.le_refl _, by rw [h1]; exact h4, ?_⟩
      refine ⟨?_, Or.inl rfl⟩
      intro t ht1 ht2 q' hq'; simp at hq'; subst hq'; omega
  | q :: q' :: rest, s, h => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    obtain ⟨P1, P2, P3⟩ := SegQ_props fc K N (q' :: rest) q'.off h5
    have hq'N := (P1 q' (by simp)).2
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with hx | hx
      · subst hx; omega
      · have := P1 x hx; omega
    · refine List.Pairwise.cons ?_ P2
      intro x hx; have := P1 x hx; omega
    · intro x hx
      rcases List.mem_cons.mp hx with hx0 | hx1
      · subst hx0
        refine ⟨by rw [h1]; exact h2, q'.off, by omega, Nat.le_of_lt hq'N, by rw [h1]; exact h4, ?_,
          Or.inr ⟨q', by simp, rfl⟩⟩
        intro t ht1 ht2 y hy
        rcases List.mem_cons.mp hy with hy | hy
        · subst hy; omega
        · have := P1 y hy; omega
      · obtain ⟨u1, nx, u2, u3, u4, u5, u6⟩ := P3 x hx1
        refine ⟨u1, nx, u2, u3, u4, ?_, ?_⟩
        rotate_left
        · rcases u6 with u6 | ⟨q'', hq'', e⟩
          · exact Or.inl u6
          · exact Or.inr ⟨q'', List.mem_cons_of_mem _ hq'', e⟩
        intro t ht1 ht2 y hy
        rcases List.mem_cons.mp hy with hy | hy
        · rw [hy]; have := P1 x hx1; omega
        · exact u5 t ht1 ht2 y hy

/-! ## The table -/

def tStep (n : Nat) (tbl : Array (Option (IK × Fee))) (p : Pt) : Array (Option (IK × Fee)) :=
  if p.k ≠ .unreach ∧ p.fee ≠ Fee.zero ∧ p.off < n then tbl.set! p.off (some (p.k, p.fee)) else tbl

theorem tStep_get (n : Nat) (tbl : Array (Option (IK × Fee))) (p : Pt) (j : Nat) :
    (tStep n tbl p)[j]? = if p.k ≠ .unreach ∧ p.fee ≠ Fee.zero ∧ p.off < n ∧ j = p.off ∧ j < tbl.size
      then some (some (p.k, p.fee)) else tbl[j]? := by
  unfold tStep
  by_cases hc : p.k ≠ .unreach ∧ p.fee ≠ Fee.zero ∧ p.off < n
  · rw [if_pos hc]
    by_cases hj : j = p.off
    · rw [hj]
      by_cases hs : p.off < tbl.size
      · rw [if_pos ⟨hc.1, hc.2.1, hc.2.2, rfl, hs⟩]
        simp [Array.set!, Array.getElem?_setIfInBounds, hs]
      · rw [if_neg (by omega)]
        simp [Array.set!, Array.getElem?_setIfInBounds, hs]
    · rw [if_neg (by omega)]
      simp [Array.set!, Array.getElem?_setIfInBounds, Ne.symm hj]
  · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, h.2.1, h.2.2.1⟩)]

theorem tStep_size (n : Nat) (tbl : Array (Option (IK × Fee))) (p : Pt) :
    (tStep n tbl p).size = tbl.size := by
  unfold tStep; split <;> simp

theorem table_some (n : Nat) : ∀ (Q : List Pt) (init : Array (Option (IK × Fee))) j e,
    (Q.foldl (tStep n) init)[j]? = some (some e) →
    init[j]? = some (some e) ∨ ∃ q ∈ Q, q.off = j ∧ e = (q.k, q.fee) ∧ q.k ≠ .unreach ∧ q.fee ≠ Fee.zero := by
  intro Q
  induction Q with
  | nil => intro init j e h; left; exact h
  | cons p Q ih =>
    intro init j e h
    rcases ih (tStep n init p) j e h with h' | ⟨q, hq, h1, h2, h3, h4⟩
    · rw [tStep_get] at h'
      split at h'
      · rename_i hc
        right; refine ⟨p, by simp, hc.2.2.2.1.symm, ?_, hc.1, hc.2.1⟩
        simp at h'; exact h'.symm
      · left; exact h'
    · right; exact ⟨q, List.mem_cons_of_mem _ hq, h1, h2, h3, h4⟩

theorem table_keep (n : Nat) : ∀ (Q : List Pt) (init : Array (Option (IK × Fee))) j,
    (∀ q ∈ Q, q.off ≠ j) → (Q.foldl (tStep n) init)[j]? = init[j]? := by
  intro Q
  induction Q with
  | nil => intro init j _; rfl
  | cons p Q ih =>
    intro init j h
    simp only [List.foldl_cons]
    rw [ih _ j (fun q hq => h q (List.mem_cons_of_mem _ hq)), tStep_get]
    rw [if_neg (by have := h p (by simp); omega)]

theorem table_size (n : Nat) : ∀ (Q : List Pt) (init : Array (Option (IK × Fee))),
    (Q.foldl (tStep n) init).size = init.size := by
  intro Q
  induction Q with
  | nil => intro init; rfl
  | cons p Q ih => intro init; simp only [List.foldl_cons]; rw [ih, tStep_size]

theorem table_hit (n : Nat) : ∀ (Q : List Pt) (init : Array (Option (IK × Fee))),
    Q.Pairwise (fun x y => x.off < y.off) → init.size = n →
    ∀ q ∈ Q, q.k ≠ .unreach → q.fee ≠ Fee.zero → q.off < n →
      (Q.foldl (tStep n) init)[q.off]? = some (some (q.k, q.fee)) := by
  intro Q
  induction Q with
  | nil => intro _ _ _ q hq; simp at hq
  | cons p Q ih =>
    intro init hp hs q hq h1 h2 h3
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq
      rw [table_keep n Q _ q.off (fun x hx => by
        have := List.rel_of_pairwise_cons hp hx; omega)]
      rw [tStep_get, if_pos ⟨h1, h2, h3, rfl, by omega⟩]
    · exact ih _ (List.Pairwise.of_cons hp) (by rw [tStep_size]; exact hs) q hq h1 h2 h3

end NearSpecV3.Wasm.FuelGas
