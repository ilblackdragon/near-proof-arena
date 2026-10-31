import NearSpecV3.Wasm.FuelGasScan
namespace NearSpecV3.Wasm.FuelGas
open NearSpecV3.Wasm

/-! ## Basic facts on the scan -/

theorem scanS_succ (g : GasCfg) (code : Array Instr) (u : Nat) (h : u < code.size) :
    scanS g code (u + 1) = gstep g (scanS g code u) u code[u] := by
  simp only [scanS, gstep', h, dite_true]

theorem flushAt_cur (u : Nat) (s : GS) : (flushAt u s).cur = s.cur := by
  unfold flushAt; split <;> rfl

theorem flushAt_stack (u : Nat) (s : GS) : (flushAt u s).stack = s.stack := by
  unfold flushAt; split <;> rfl

theorem flushAt_frs (u : Nat) (s : GS) : frs (flushAt u s) = frs s := by
  simp [frs, flushAt_cur, flushAt_stack]

theorem flushAt_off (u : Nat) (s : GS) : (flushAt u s).off = u := by
  unfold flushAt; split <;> rfl

theorem flushAt_sched (u : Nat) (s : GS) : (flushAt u s).sched = none := by
  unfold flushAt; split
  · rfl
  · rename_i h; exact h

theorem flushAt_pts (u : Nat) (s : GS) :
    (flushAt u s).pts = match s.sched with
      | some (k, f) => s.pts.push ⟨u, k, f⟩
      | none => s.pts := by
  rcases hs : s.sched with _ | ⟨k, f⟩ <;> simp [flushAt, hs]

theorem flushAt_size (u : Nat) (s : GS) :
    (flushAt u s).pts.size = s.pts.size + (if s.sched.isSome then 1 else 0) := by
  rw [flushAt_pts]; split <;> simp_all

/-! ## The opener stack -/

theorem openAt_succ (code : Array Instr) (u : Nat) :
    openAt code (u + 1) = match code[u]? with
      | some i => openStep (openAt code u) u i
      | none => openAt code u := by
  unfold openAt
  rw [List.range_succ, List.foldl_append]
  rfl

theorem openAt_mem (code : Array Instr) : ∀ u x, x ∈ openAt code u →
    x < u ∧ ∃ i, code[x]? = some i ∧ isOpener i = true := by
  intro u
  induction u with
  | zero => intro x h; simp [openAt] at h
  | succ u ih =>
    intro x h
    rw [openAt_succ] at h
    split at h
    · rename_i i hi
      cases i <;> simp only [openStep] at h
      all_goals first
        | (rcases List.mem_cons.mp h with h | h
           · subst h; exact ⟨by omega, _, hi, rfl⟩
           · have := ih x h; exact ⟨by omega, this.2⟩)
        | (have := ih x (List.mem_of_mem_tail h); exact ⟨by omega, this.2⟩)
        | (have := ih x h; exact ⟨by omega, this.2⟩)
    · have := ih x h; exact ⟨by omega, this.2⟩

/-! ## The own point of a step -/

def ownReq (g : GasCfg) (s : GS) : Instr → IK × Fee
  | .unreachable => (.pre, .const g.regular)
  | .loop _ => (.pure, Fee.zero)
  | .end_ => (if isFwd s.cur.kind then .pre else .pure, Fee.zero)
  | .if_ _ => (.pre, .const g.regular)
  | .else_ => (.pre, Fee.zero)
  | .block _ => (.pure, Fee.zero)
  | .br _ | .brIf _ | .brTable _ _ | .ret => (.pre, .const g.regular)
  | i => ((plainE g i).1, (plainE g i).2.1)

def ownPoly (s : GS) : Instr → Bool
  | .else_ => (popF s).cur.poly
  | _ => s.cur.poly

def ownPt (g : GasCfg) (s : GS) (u : Nat) (ins : Instr) : Pt :=
  ⟨u, if ownPoly s ins then .unreach else (ownReq g s ins).1, (ownReq g s ins).2⟩

theorem ownReq_plain (g : GasCfg) (s : GS) (ins : Instr) (h : isCtl ins = false) :
    ownReq g s ins = ((plainE g ins).1, (plainE g ins).2.1) ∧ ownPoly s ins = s.cur.poly := by
  cases ins <;> simp only [isCtl, Bool.true_eq_false] at h <;> exact ⟨rfl, rfl⟩

theorem pushOwn_pts (s : GS) (k : IK) (f : Fee) :
    (pushOwn s k f).pts = s.pts.push ⟨s.off, if s.cur.poly then .unreach else k, f⟩ := rfl

def PtsStep (s1 s' : GS) (own : Pt) (F : List GF) : Prop :=
  s'.pts.size = s1.pts.size + 1 ∧
  ∀ x pt, (s1.pts.push own)[x]? = some pt → ∃ pt', s'.pts[x]? = some pt' ∧ pt'.off = pt.off ∧
    pt'.fee = pt.fee ∧ (pt'.k = pt.k ∨ MutOK F x pt'.k)

theorem PtsStep_exact (s1 s' : GS) (own : Pt) (F : List GF) (h : s'.pts = s1.pts.push own) :
    PtsStep s1 s' own F := by
  refine ⟨by rw [h]; simp, fun x pt hx => ⟨pt, by rw [h]; exact hx, rfl, rfl, Or.inl rfl⟩⟩

theorem PtsStep_adj (s1 : GS) (ls : List Nat) (own : Pt) (k : IK) (f : Fee)
    (ho : own = ⟨s1.off, if s1.cur.poly then .unreach else k, f⟩) :
    PtsStep s1 (adjSeq { pushOwn s1 k f with sched := some (.post, Fee.zero) } ls) own (frs s1) := by
  refine ⟨by rw [adjSeq_size]; simp [pushOwn], ?_⟩
  intro x pt hx
  have := adjSeq_pts ls { pushOwn s1 k f with sched := some (.post, Fee.zero) } x pt
    (by simp only [pushOwn_pts]; rw [← ho]; exact hx)
  exact this

theorem PtsStep_setPoly (s1 s' : GS) (own : Pt) (F : List GF) (h : PtsStep s1 s' own F) :
    PtsStep s1 (setPoly s') own F := h

theorem step_pts' (g : GasCfg) (s1 : GS) (ins : Instr) :
    PtsStep s1 ((gInstr g ins).run s1).2 (ownPt g s1 s1.off ins) (frs s1) := by
  by_cases hc : isCtl ins = false
  · obtain ⟨h1, h2⟩ := ownReq_plain g s1 ins hc
    rw [gInstr_plain g ins hc]
    apply PtsStep_exact
    simp only [plainRes, pushOwn, ownPt, h1, h2]
  · cases ins
    case unreachable => rw [gInstr_unreachable]; apply PtsStep_exact; rfl
    case loop bt => rw [gInstr_loop]; apply PtsStep_exact; rfl
    case if_ bt => rw [gInstr_if]; apply PtsStep_exact; rfl
    case else_ => rw [gInstr_else]; apply PtsStep_exact; rfl
    case end_ =>
      rw [gInstr_end]; apply PtsStep_exact
      unfold popF; split <;> (split <;> simp_all [ownPt, ownReq, ownPoly, baseSide, pushOwn])
    case br l => rw [gInstr_br]; exact PtsStep_setPoly _ _ _ _ (PtsStep_adj _ _ _ _ _ rfl)
    case brIf l => rw [gInstr_brIf]; exact PtsStep_adj _ _ _ _ _ rfl
    case brTable ls d => rw [gInstr_brTable]; exact PtsStep_setPoly _ _ _ _ (PtsStep_adj _ _ _ _ _ rfl)
    case ret => rw [gInstr_ret]; exact PtsStep_setPoly _ _ _ _ (PtsStep_adj _ _ _ _ _ rfl)
    case block bt => rw [gInstr_block]; apply PtsStep_exact; rfl
    all_goals simp [isCtl] at hc

theorem step_pts (g : GasCfg) (s : GS) (u : Nat) (ins : Instr) :
    PtsStep (flushAt u s) (gstep g s u ins) (ownPt g (flushAt u s) u ins) (frs s) := by
  have := step_pts' g (flushAt u s) ins
  rw [flushAt_off, flushAt_frs] at this
  exact this


/-! ## Frames after one step -/

theorem frs_plain (g : GasCfg) (s : GS) (u : Nat) (ins : Instr) (h : isCtl ins = false) :
    frs (gstep g s u ins) = frs s := by
  unfold gstep; rw [gInstr_plain g ins h, ← flushAt_frs u s]; rfl

theorem frs_unreach (g : GasCfg) (s : GS) (u : Nat) :
    frs (gstep g s u .unreachable) = { s.cur with poly := true } :: s.stack := by
  unfold gstep; rw [gInstr_unreachable]
  simp [frs, setPoly, pushOwn, flushAt_cur, flushAt_stack]

theorem frs_loop (g : GasCfg) (s : GS) (u : Nat) (bt : BT) :
    frs (gstep g s u (.loop bt)) =
      ⟨s.cur.poly, .loop (flushAt u s).pts.size ((flushAt u s).pts.size + 1)⟩ :: frs s := by
  unfold gstep; rw [gInstr_loop]
  simp [frs, pushOwn, flushAt_cur, flushAt_stack]

theorem frs_if (g : GasCfg) (s : GS) (u : Nat) (bt : BT) :
    frs (gstep g s u (.if_ bt)) = ⟨s.cur.poly, .forward⟩ :: frs s := by
  unfold gstep; rw [gInstr_if]
  simp [frs, baseSide, pushOwn, flushAt_cur, flushAt_stack]

theorem frs_block (g : GasCfg) (s : GS) (u : Nat) (bt : BT) :
    frs (gstep g s u (.block bt)) = ⟨s.cur.poly, .untaken⟩ :: frs s := by
  unfold gstep; rw [gInstr_block]
  simp [frs, pushOwn, flushAt_cur, flushAt_stack]

theorem frs_popF (s : GS) : frs (popF s) = match s.stack with | [] => frs s | _ :: _ => s.stack := by
  unfold popF; cases s.stack <;> rfl

theorem frs_end (g : GasCfg) (s : GS) (u : Nat) :
    frs (gstep g s u .end_) = match s.stack with | [] => frs s | _ :: _ => s.stack := by
  unfold gstep; rw [gInstr_end, frs_popF]
  have e1 : ∀ X : GS, X.cur = s.cur → X.stack = s.stack →
      (match X.stack with | [] => frs X | _ :: _ => X.stack) =
      (match s.stack with | [] => frs s | _ :: _ => s.stack) := by
    intro X h1 h2; simp only [frs, h1, h2]
  apply e1
  · split <;> simp [baseSide, pushOwn, flushAt_cur]
  · split <;> simp [baseSide, pushOwn, flushAt_stack]

theorem frs_else (g : GasCfg) (s : GS) (u : Nat) (f : GF) (rest : List GF) (hs : s.stack = f :: rest) :
    frs (gstep g s u .else_) = ⟨f.poly, .forward⟩ :: f :: rest := by
  unfold gstep; rw [gInstr_else]
  simp [frs, popF, flushAt_stack, hs]

theorem frs_baseSide (s : GS) (k : IK) (f : Fee) : frs (baseSide s k f) = frs s := rfl

theorem frs_setPoly_get (s : GS) (l : Nat) :
    (frs (setPoly s))[l]? = if l = 0 then some { s.cur with poly := true } else (frs s)[l]? := by
  cases l <;> simp [frs, setPoly]

/-- The labels a branch instruction adjusts (`ret` adjusts the function frame only). -/
def brLabels : Instr → List Nat
  | .br l => [l]
  | .brIf l => [l]
  | .brTable ls d => ls.toList ++ [d]
  | _ => []

def adjAt (L : List Nat) (j : Nat) (f : GF) : GF := if j ∈ L then adjF f else f

def polyAt (j : Nat) (f : GF) : GF := if j = 0 then { f with poly := true } else f

theorem frs_adjBase (s : GS) (u : Nat) (k : IK) (fe : Fee) (L : List Nat) (j : Nat) :
    (frs (adjSeq (baseSide (flushAt u s) k fe) L))[j]? = ((frs s)[j]?).map (adjAt L j) := by
  rw [frs_adjSeq_get, frs_baseSide, flushAt_frs]; rfl

theorem frs_spAdjBase (s : GS) (u : Nat) (k : IK) (fe : Fee) (L : List Nat) (j : Nat) :
    (frs (setPoly (adjSeq (baseSide (flushAt u s) k fe) L)))[j]? =
      ((frs s)[j]?).map (fun f => polyAt j (adjAt L j f)) := by
  rw [frs_setPoly_get]
  split
  · rename_i hj; subst hj
    have := frs_adjBase s u k fe L 0
    simp only [frs, List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at this ⊢
    rw [this]; rfl
  · rename_i hj
    rw [frs_adjBase]
    cases (frs s)[j]? <;> simp [polyAt, hj]

theorem frs_br (g : GasCfg) (s : GS) (u l j : Nat) :
    (frs (gstep g s u (.br l)))[j]? = ((frs s)[j]?).map (fun f => polyAt j (adjAt [l] j f)) := by
  unfold gstep; rw [gInstr_br, frs_spAdjBase]

theorem frs_brIf (g : GasCfg) (s : GS) (u l j : Nat) :
    (frs (gstep g s u (.brIf l)))[j]? = ((frs s)[j]?).map (adjAt [l] j) := by
  unfold gstep; rw [gInstr_brIf, frs_adjBase]

theorem frs_brTable (g : GasCfg) (s : GS) (u : Nat) (ls : Array Nat) (d j : Nat) :
    (frs (gstep g s u (.brTable ls d)))[j]? =
      ((frs s)[j]?).map (fun f => polyAt j (adjAt (ls.toList ++ [d]) j f)) := by
  unfold gstep; rw [gInstr_brTable, frs_spAdjBase]

theorem frs_ret (g : GasCfg) (s : GS) (u j : Nat) :
    (frs (gstep g s u .ret))[j]? = ((frs s)[j]?).map (fun f => polyAt j (adjAt [s.stack.length] j f)) := by
  unfold gstep; rw [gInstr_ret, frs_spAdjBase, flushAt_stack]

/-! ## The frame invariant -/

theorem openAt_sorted (code : Array Instr) : ∀ u, (openAt code u).Pairwise (fun a b => b < a) := by
  intro u
  induction u with
  | zero => simp [openAt]
  | succ u ih =>
    rw [openAt_succ]
    split
    · rename_i i hi
      cases i <;> simp only [openStep]
      all_goals first
        | exact List.Pairwise.cons (fun x hx => (openAt_mem code u x hx).1) ih
        | exact ih.tail
        | exact ih
    · exact ih

theorem pw_inj {L : List Nat} (h : L.Pairwise (fun a b => b < a)) {i j x : Nat}
    (hi : L[i]? = some x) (hj : L[j]? = some x) : i = j := by
  obtain ⟨hi', ei⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', ej⟩ := List.getElem?_eq_some_iff.mp hj
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · have := List.pairwise_iff_getElem.mp h i j hi' hj' hij; omega
  · exact hij
  · have := List.pairwise_iff_getElem.mp h j i hj' hi' hij; omega

def TgtB (code : Array Instr) (o u : Nat) : Prop :=
  ∃ pc, o < pc ∧ pc < u ∧ ∃ i l, code[pc]? = some i ∧ l ∈ brLabels i ∧ (openAt code pc)[l]? = some o

theorem TgtB_succ (code : Array Instr) (o u : Nat) (h : TgtB code o (u + 1)) :
    TgtB code o u ∨ (o < u ∧ ∃ i l, code[u]? = some i ∧ l ∈ brLabels i ∧ (openAt code u)[l]? = some o) := by
  obtain ⟨pc, h1, h2, i, l, h3, h4, h5⟩ := h
  by_cases hpc : pc = u
  · subst hpc; exact Or.inr ⟨h1, i, l, h3, h4, h5⟩
  · exact Or.inl ⟨pc, h1, by omega, i, l, h3, h4, h5⟩

theorem TgtB_nolab (code : Array Instr) (o u : Nat) (i : Instr) (hi : code[u]? = some i)
    (hl : brLabels i = []) (h : TgtB code o (u + 1)) : TgtB code o u := by
  rcases TgtB_succ code o u h with h | ⟨_, i', l, h3, h4, _⟩
  · exact h
  · rw [hi] at h3; cases h3; rw [hl] at h4; simp at h4

def FrK (g : GasCfg) (code : Array Instr) (u o : Nat) (k : BTK) : Prop :=
  match code[o]? with
  | some (.loop _) => k = .loop ((scanS g code (o + 1)).pts.size - 1) ((scanS g code (o + 1)).pts.size)
  | some (.if_ _) => k = .forward
  | some (.block _) => (k = .untaken ∨ k = .forward) ∧ (TgtB code o u → k = .forward)
  | _ => False

structure Inv (g : GasCfg) (code : Array Instr) (u : Nat) : Prop where
  len : (frs (scanS g code u)).length = (openAt code u).length + 1
  kind : ∀ (l o : Nat), (openAt code u)[l]? = some o →
    ∃ f : GF, (frs (scanS g code u))[l]? = some f ∧ FrK g code u o f.kind
  par : ∀ (l o : Nat), (openAt code u)[l]? = some o →
    ∃ f : GF, (frs (scanS g code u))[l + 1]? = some f ∧ f.poly = (scanS g code o).cur.poly
  inh : ∀ (l : Nat) (f f' : GF), (frs (scanS g code u))[l]? = some f → (frs (scanS g code u))[l + 1]? = some f' →
    f'.poly = true → f.poly = true
  fn : ∀ f : GF, (frs (scanS g code u))[(openAt code u).length]? = some f →
    f.kind = .untaken ∨ f.kind = .forward

theorem inv_zero (g : GasCfg) (code : Array Instr) : Inv g code 0 := by
  have hE : openAt code 0 = [] := rfl
  have hS : frs (scanS g code 0) = [⟨false, .untaken⟩] := rfl
  refine ⟨by rw [hE, hS]; rfl, ?_, ?_, ?_, ?_⟩
  · intro l o h; rw [hE] at h; simp at h
  · intro l o h; rw [hE] at h; simp at h
  · intro l f f' h1 h2 _; rw [hS] at h2; simp at h2
  · intro f h; rw [hE, hS] at h; simp at h; subst h; left; rfl

theorem get_of_len {α β : Type} {L : List α} {L' : List β} (h : L'.length = L.length) {l : Nat} {x : β}
    (hx : L'[l]? = some x) : ∃ y, L[l]? = some y := by
  have := (List.getElem?_eq_some_iff.mp hx).1
  exact ⟨L[l], List.getElem?_eq_getElem (by omega)⟩

theorem inv_same (g : GasCfg) (code : Array Instr) (u : Nat) (I : Inv g code u)
    (hE : openAt code (u + 1) = openAt code u)
    (hlen : (frs (scanS g code (u + 1))).length = (frs (scanS g code u)).length)
    (hk : ∀ (l : Nat) (f : GF), (frs (scanS g code u))[l]? = some f → ∃ f' : GF, (frs (scanS g code (u + 1)))[l]? = some f' ∧
      (f'.kind = f.kind ∨ f'.kind = adjK f.kind) ∧ (0 < l → f'.poly = f.poly) ∧
      (f.poly = true → f'.poly = true))
    (htgt : ∀ o : Nat, TgtB code o (u + 1) → TgtB code o u ∨ ∃ l : Nat, ∃ f f' : GF, (openAt code u)[l]? = some o ∧
      (frs (scanS g code u))[l]? = some f ∧ (frs (scanS g code (u + 1)))[l]? = some f' ∧
      f'.kind = adjK f.kind) :
    Inv g code (u + 1) := by
  refine ⟨by rw [hlen, hE]; exact I.len, ?_, ?_, ?_, ?_⟩
  · intro l o ho
    rw [hE] at ho
    obtain ⟨f, hf, hfk⟩ := I.kind l o ho
    obtain ⟨f', hf', hk1, _, _⟩ := hk l f hf
    refine ⟨f', hf', ?_⟩
    unfold FrK at hfk ⊢
    split at hfk
    · rename_i bt hc
      rcases hk1 with h | h <;> rw [h, hfk] <;> rfl
    · rename_i bt hc
      rcases hk1 with h | h <;> rw [h, hfk] <;> rfl
    · rename_i bt hc
      obtain ⟨h1, h2⟩ := hfk
      have hadj : adjK f.kind = .forward := by rcases h1 with h1 | h1 <;> rw [h1] <;> rfl
      refine ⟨?_, ?_⟩
      · rcases hk1 with h | h
        · rw [h]; exact h1
        · rw [h, hadj]; exact Or.inr rfl
      · intro ht
        rcases htgt o ht with ht | ⟨l2, f2, f2', h21, h22, h23, h24⟩
        · have := h2 ht
          rcases hk1 with h | h
          · rw [h, this]
          · rw [h, this]; rfl
        · have := pw_inj (openAt_sorted code u) ho h21
          subst this
          rw [hf] at h22; cases h22
          rw [hf'] at h23; cases h23
          rw [h24, hadj]
    · exact hfk.elim
  · intro l o ho
    rw [hE] at ho
    obtain ⟨f, hf, hp⟩ := I.par l o ho
    obtain ⟨f', hf', _, hp', _⟩ := hk (l + 1) f hf
    exact ⟨f', hf', by rw [hp' (by omega), hp]⟩
  · intro l f' g' h1 h2 h3
    obtain ⟨f, hf⟩ := get_of_len hlen h1
    obtain ⟨g0, hg⟩ := get_of_len hlen h2
    obtain ⟨f'', hf'', _, _, hfp⟩ := hk l f hf
    obtain ⟨g'', hg'', _, hgp, _⟩ := hk (l + 1) g0 hg
    rw [h1] at hf''; cases hf''
    rw [h2] at hg''; cases hg''
    exact hfp (I.inh l f g0 hf hg (by rw [← hgp (by omega)]; exact h3))
  · intro f' hf'
    rw [hE] at hf'
    obtain ⟨f, hf⟩ := get_of_len hlen hf'
    obtain ⟨f'', hf'', hk1, _, _⟩ := hk _ f hf
    rw [hf'] at hf''; cases hf''
    rcases I.fn f hf with h | h <;> rcases hk1 with h' | h' <;> rw [h', h] <;> simp [adjK]

theorem FrK_mono (g : GasCfg) (code : Array Instr) (u o : Nat) (k : BTK)
    (ht : TgtB code o (u + 1) → TgtB code o u) (h : FrK g code u o k) : FrK g code (u + 1) o k := by
  unfold FrK at h ⊢
  split at h
  · exact h
  · exact h
  · exact ⟨h.1, fun h' => h.2 (ht h')⟩
  · exact h.elim

theorem inv_push (g : GasCfg) (code : Array Instr) (u : Nat) (I : Inv g code u) (nf : GF)
    (hE : openAt code (u + 1) = u :: openAt code u)
    (hfr : frs (scanS g code (u + 1)) = nf :: frs (scanS g code u))
    (hnf : nf.poly = (scanS g code u).cur.poly)
    (hk0 : FrK g code (u + 1) u nf.kind)
    (ht : ∀ o, TgtB code o (u + 1) → TgtB code o u) : Inv g code (u + 1) := by
  refine ⟨by rw [hfr, hE]; simp [I.len], ?_, ?_, ?_, ?_⟩
  · intro l o ho
    rw [hE] at ho
    rw [hfr]
    cases l with
    | zero => simp at ho; subst ho; exact ⟨nf, rfl, hk0⟩
    | succ l =>
      simp only [List.getElem?_cons_succ] at ho ⊢
      obtain ⟨f, hf, hk⟩ := I.kind l o ho
      exact ⟨f, hf, FrK_mono g code u o _ (ht o) hk⟩
  · intro l o ho
    rw [hE] at ho
    rw [hfr]
    cases l with
    | zero => simp at ho; subst ho; exact ⟨(scanS g code u).cur, by simp [frs], rfl⟩
    | succ l =>
      simp only [List.getElem?_cons_succ] at ho ⊢
      exact I.par l o ho
  · intro l f f' h1 h2 h3
    rw [hfr] at h1 h2
    cases l with
    | zero =>
      simp [frs] at h1 h2; subst h1; subst h2; rw [hnf]; exact h3
    | succ l =>
      simp only [List.getElem?_cons_succ] at h1 h2
      exact I.inh l f f' h1 h2 h3
  · intro f hf
    rw [hE, hfr] at hf
    simp only [List.length_cons, List.getElem?_cons_succ] at hf
    exact I.fn f hf

theorem inv_pop (g : GasCfg) (code : Array Instr) (u : Nat) (I : Inv g code u) (o : Nat) (rest : List Nat)
    (hEu : openAt code u = o :: rest)
    (hE : openAt code (u + 1) = rest)
    (hfr : frs (scanS g code (u + 1)) = (frs (scanS g code u)).tail)
    (ht : ∀ o, TgtB code o (u + 1) → TgtB code o u) : Inv g code (u + 1) := by
  have hlen := I.len
  rw [hEu] at hlen
  obtain ⟨f0, L, hL⟩ : ∃ f0 L, frs (scanS g code u) = f0 :: L := ⟨_, _, rfl⟩
  rw [hL] at hfr hlen
  simp only [List.tail_cons] at hfr
  have gk : ∀ l, (frs (scanS g code u))[l + 1]? = (frs (scanS g code (u + 1)))[l]? := by
    intro l; rw [hL, hfr]; rfl
  refine ⟨by rw [hfr, hE]; simp at hlen; omega, ?_, ?_, ?_, ?_⟩
  · intro l o' ho
    rw [hE] at ho
    have ho' : (openAt code u)[l + 1]? = some o' := by rw [hEu]; exact ho
    obtain ⟨f, hf, hk⟩ := I.kind (l + 1) o' ho'
    rw [gk] at hf
    exact ⟨f, hf, FrK_mono g code u o' _ (ht o') hk⟩
  · intro l o' ho
    rw [hE] at ho
    have ho' : (openAt code u)[l + 1]? = some o' := by rw [hEu]; exact ho
    obtain ⟨f, hf, hk⟩ := I.par (l + 1) o' ho'
    rw [gk] at hf
    exact ⟨f, hf, hk⟩
  · intro l f f' h1 h2 h3
    rw [← gk] at h1 h2
    exact I.inh (l + 1) f f' h1 h2 h3
  · intro f hf
    rw [hE] at hf
    rw [← gk] at hf
    have := I.fn f
    rw [hEu] at this
    exact this hf

theorem inv_else (g : GasCfg) (code : Array Instr) (u : Nat) (I : Inv g code u) (o : Nat) (rest : List Nat)
    (bt : BT) (hEu : openAt code u = o :: rest) (ho : code[o]? = some (.if_ bt))
    (hE : openAt code (u + 1) = openAt code u) (f : GF) (L : List GF)
    (hst : (scanS g code u).stack = f :: L)
    (hfr : frs (scanS g code (u + 1)) = ⟨f.poly, .forward⟩ :: f :: L)
    (ht : ∀ o, TgtB code o (u + 1) → TgtB code o u) : Inv g code (u + 1) := by
  have hL : frs (scanS g code u) = (scanS g code u).cur :: f :: L := by simp [frs, hst]
  have gk : ∀ l, (frs (scanS g code u))[l + 1]? = (frs (scanS g code (u + 1)))[l + 1]? := by
    intro l; rw [hL, hfr]; rfl
  refine ⟨by rw [hfr, hE]; have := I.len; rw [hL] at this; simpa using this, ?_, ?_, ?_, ?_⟩
  · intro l o' ho'
    rw [hE] at ho'
    cases l with
    | zero =>
      rw [hEu] at ho'; simp at ho'; subst ho'
      refine ⟨⟨f.poly, .forward⟩, by rw [hfr]; rfl, ?_⟩
      unfold FrK; rw [ho]
    | succ l =>
      obtain ⟨f1, hf1, hk⟩ := I.kind (l + 1) o' ho'
      rw [gk] at hf1
      exact ⟨f1, hf1, FrK_mono g code u o' _ (ht o') hk⟩
  · intro l o' ho'
    rw [hE] at ho'
    obtain ⟨f1, hf1, hk⟩ := I.par l o' ho'
    rw [gk] at hf1
    exact ⟨f1, hf1, hk⟩
  · intro l f1 f1' h1 h2 h3
    cases l with
    | zero =>
      rw [hfr] at h1 h2; simp at h1 h2; subst h1; subst h2; exact h3
    | succ l =>
      rw [← gk] at h1 h2
      exact I.inh (l + 1) f1 f1' h1 h2 h3
  · intro f1 hf1
    rw [hE, hEu] at hf1
    simp only [List.length_cons] at hf1
    rw [← gk] at hf1
    have := I.fn f1
    rw [hEu] at this
    exact this hf1

theorem len_of_get {α β : Type} {L : List α} {L' : List β} (F : Nat → α → β)
    (h : ∀ j, L'[j]? = (L[j]?).map (F j)) : L'.length = L.length := by
  have : L' = L.mapIdx F := by
    apply List.ext_getElem?; intro j; rw [h, List.getElem?_mapIdx]
  rw [this, List.length_mapIdx]

theorem inv_map (g : GasCfg) (code : Array Instr) (u : Nat) (I : Inv g code u)
    (hE : openAt code (u + 1) = openAt code u) (Φ : Nat → GF → GF)
    (hfr : ∀ j, (frs (scanS g code (u + 1)))[j]? = ((frs (scanS g code u))[j]?).map (Φ j))
    (hΦ : ∀ j f, ((Φ j f).kind = f.kind ∨ (Φ j f).kind = adjK f.kind) ∧ (0 < j → (Φ j f).poly = f.poly) ∧
      (f.poly = true → (Φ j f).poly = true))
    (hlab : ∀ o, TgtB code o (u + 1) → TgtB code o u ∨
      ∃ l, (openAt code u)[l]? = some o ∧ ∀ f, (Φ l f).kind = adjK f.kind) : Inv g code (u + 1) := by
  apply inv_same g code u I hE (len_of_get Φ hfr)
  · intro l f hf
    exact ⟨Φ l f, by rw [hfr, hf]; rfl, hΦ l f⟩
  · intro o ht
    rcases hlab o ht with h | ⟨l, hl, hk⟩
    · exact Or.inl h
    · right
      have hlt := (List.getElem?_eq_some_iff.mp hl).1
      have hlen := I.len
      obtain ⟨f, hf⟩ : ∃ f, (frs (scanS g code u))[l]? = some f :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      exact ⟨l, f, Φ l f, hl, hf, by rw [hfr, hf]; rfl, hk f⟩

theorem adjAt_props (L : List Nat) (j : Nat) (f : GF) :
    ((adjAt L j f).kind = f.kind ∨ (adjAt L j f).kind = adjK f.kind) ∧
    (0 < j → (adjAt L j f).poly = f.poly) ∧ (f.poly = true → (adjAt L j f).poly = true) ∧
    (j ∈ L → (adjAt L j f).kind = adjK f.kind) := by
  unfold adjAt
  split
  · rename_i h; exact ⟨Or.inr rfl, fun _ => rfl, id, fun _ => rfl⟩
  · rename_i h; exact ⟨Or.inl rfl, fun _ => rfl, id, fun h' => absurd h' h⟩

theorem polyAt_props (j : Nat) (f : GF) :
    (polyAt j f).kind = f.kind ∧ (0 < j → (polyAt j f).poly = f.poly) ∧
    (f.poly = true → (polyAt j f).poly = true) := by
  unfold polyAt
  split
  · rename_i h; exact ⟨rfl, fun h' => by omega, fun _ => rfl⟩
  · exact ⟨rfl, fun _ => rfl, id⟩

theorem pa_props (L : List Nat) (j : Nat) (f : GF) :
    (((polyAt j (adjAt L j f)).kind = f.kind ∨ (polyAt j (adjAt L j f)).kind = adjK f.kind) ∧
    (0 < j → (polyAt j (adjAt L j f)).poly = f.poly) ∧
    (f.poly = true → (polyAt j (adjAt L j f)).poly = true)) ∧
    (j ∈ L → (polyAt j (adjAt L j f)).kind = adjK f.kind) := by
  obtain ⟨a1, a2, a3, a4⟩ := adjAt_props L j f
  obtain ⟨b1, b2, b3⟩ := polyAt_props j (adjAt L j f)
  refine ⟨⟨by rw [b1]; exact a1, fun h => by rw [b2 h, a2 h], fun h => b3 (a3 h)⟩, fun h => by rw [b1, a4 h]⟩

theorem hlab_of (code : Array Instr) (u : Nat) (ins : Instr) (hi : code[u]? = some ins) (L : List Nat)
    (hL : ∀ x ∈ brLabels ins, x ∈ L) (Φ : Nat → GF → GF) (hΦ : ∀ j f, j ∈ L → (Φ j f).kind = adjK f.kind) :
    ∀ o, TgtB code o (u + 1) → TgtB code o u ∨
      ∃ l, (openAt code u)[l]? = some o ∧ ∀ f, (Φ l f).kind = adjK f.kind := by
  intro o ht
  rcases TgtB_succ code o u ht with h | ⟨_, i, l, h1, h2, h3⟩
  · exact Or.inl h
  · rw [hi] at h1; cases h1
    exact Or.inr ⟨l, h3, fun f => hΦ l f (hL l h2)⟩

theorem openStep_plain (os : List Nat) (u : Nat) (ins : Instr) (h : isCtl ins = false) :
    openStep os u ins = os := by
  cases ins <;> simp_all [isCtl, openStep]

theorem brLabels_plain (ins : Instr) (h : isCtl ins = false) : brLabels ins = [] := by
  cases ins <;> simp_all [isCtl, brLabels]

theorem inv_step (g : GasCfg) (code : Array Instr) (u : Nat) (hu : u < code.size) (I : Inv g code u)
    (helse : code[u]? = some .else_ → ∃ o rest bt, openAt code u = o :: rest ∧ code[o]? = some (.if_ bt)) :
    Inv g code (u + 1) := by
  have hS := scanS_succ g code u hu
  have hE := openAt_succ code u
  have hci : code[u]? = some code[u] := by simp [hu]
  rw [hci] at hE
  simp only at hE
  generalize hins : code[u] = ins at hS hE hci
  generalize hs : scanS g code u = s at hS
  by_cases hc : isCtl ins = false
  · rw [openStep_plain _ _ _ hc] at hE
    apply inv_map g code u I hE (fun _ f => f)
    · intro j; rw [hS, frs_plain g s u ins hc, hs]; simp
    · intro j f; exact ⟨Or.inl rfl, fun _ => rfl, id⟩
    · intro o ht; exact Or.inl (TgtB_nolab code o u ins hci (brLabels_plain ins hc) ht)
  · cases ins
    case unreachable =>
      apply inv_map g code u I hE polyAt
      · intro j; rw [hS, frs_unreach, ← hs]
        cases j with
        | zero => simp [frs, polyAt]
        | succ n =>
          simp only [frs, List.getElem?_cons_succ]
          cases (scanS g code u).stack[n]? <;> simp [polyAt]
      · intro j f; obtain ⟨a, b, c⟩ := polyAt_props j f; exact ⟨Or.inl a, b, c⟩
      · intro o ht; exact Or.inl (TgtB_nolab code o u _ hci rfl ht)
    case br l =>
      apply inv_map g code u I hE (fun j f => polyAt j (adjAt [l] j f))
      · intro j; rw [hS, frs_br, hs]
      · intro j f; exact (pa_props [l] j f).1
      · exact hlab_of code u _ hci [l] (fun x hx => hx) _ (fun j f h => (pa_props [l] j f).2 h)
    case brIf l =>
      apply inv_map g code u I hE (adjAt [l])
      · intro j; rw [hS, frs_brIf, hs]
      · intro j f; obtain ⟨a, b, c, _⟩ := adjAt_props [l] j f; exact ⟨a, b, c⟩
      · exact hlab_of code u _ hci [l] (fun x hx => hx) _ (fun j f h => (adjAt_props [l] j f).2.2.2 h)
    case brTable ls d =>
      apply inv_map g code u I hE (fun j f => polyAt j (adjAt (ls.toList ++ [d]) j f))
      · intro j; rw [hS, frs_brTable, hs]
      · intro j f; exact (pa_props _ j f).1
      · exact hlab_of code u _ hci _ (fun x hx => hx) _ (fun j f h => (pa_props _ j f).2 h)
    case ret =>
      apply inv_map g code u I hE (fun j f => polyAt j (adjAt [s.stack.length] j f))
      · intro j; rw [hS, frs_ret, hs]
      · intro j f; exact (pa_props _ j f).1
      · intro o ht; exact Or.inl (TgtB_nolab code o u _ hci rfl ht)
    case loop bt =>
      have hsz := (step_pts g s u (.loop bt)).1
      apply inv_push g code u I _ hE (by rw [hS, frs_loop, hs]) (by rw [hs])
      · unfold FrK; rw [hci]; simp only; rw [hS, hsz]; simp
      · intro o ht; exact TgtB_nolab code o u _ hci rfl ht
    case if_ bt =>
      apply inv_push g code u I _ hE (by rw [hS, frs_if, hs]) (by rw [hs])
      · unfold FrK; rw [hci]
      · intro o ht; exact TgtB_nolab code o u _ hci rfl ht
    case block bt =>
      apply inv_push g code u I _ hE (by rw [hS, frs_block, hs]) (by rw [hs])
      · unfold FrK; rw [hci]
        exact ⟨Or.inl rfl, fun ⟨pc, h1, h2, _⟩ => by omega⟩
      · intro o ht; exact TgtB_nolab code o u _ hci rfl ht
    case end_ =>
      have hlen := I.len
      rw [hs] at hlen
      cases hEu : openAt code u with
      | nil =>
        rw [hEu] at hE hlen
        simp only [openStep, List.tail_nil] at hE
        have hst : s.stack = [] := by simpa [frs] using hlen
        apply inv_map g code u I (by rw [hE, hEu]) (fun _ f => f)
        · intro j; rw [hS, frs_end, hst, hs]; simp [frs, hst]
        · intro j f; exact ⟨Or.inl rfl, fun _ => rfl, id⟩
        · intro o ht; exact Or.inl (TgtB_nolab code o u _ hci rfl ht)
      | cons o rest =>
        rw [hEu] at hE hlen
        simp only [openStep, List.tail_cons] at hE
        obtain ⟨f, L, hst⟩ : ∃ f L, s.stack = f :: L := by
          cases h : s.stack with
          | nil => simp [frs, h] at hlen
          | cons f L => exact ⟨f, L, rfl⟩
        apply inv_pop g code u I o rest hEu hE
        · rw [hS, frs_end, hst, hs]; simp [frs, hst]
        · intro o ht; exact TgtB_nolab code o u _ hci rfl ht
    case else_ =>
      obtain ⟨o, rest, bt, hEu, ho⟩ := helse hci
      have hlen := I.len
      rw [hs, hEu] at hlen
      obtain ⟨f, L, hst⟩ : ∃ f L, s.stack = f :: L := by
        cases h : s.stack with
        | nil => simp [frs, h] at hlen
        | cons f L => exact ⟨f, L, rfl⟩
      simp only [openStep] at hE
      apply inv_else g code u I o rest bt hEu ho hE f L (by rw [hs]; exact hst)
      · rw [hS, frs_else g s u f L hst]
      · intro o ht; exact TgtB_nolab code o u _ hci rfl ht
    all_goals simp [isCtl] at hc

theorem inv_all (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) :
    ∀ u, u ≤ pf.code.size → Inv g pf.code u := by
  intro u
  induction u with
  | zero => intro _; exact inv_zero g pf.code
  | succ u ih =>
    intro hu
    apply inv_step g pf.code u (by omega) (ih (by omega))
    intro hc
    obtain ⟨o, rest, bt, h1, h2, _⟩ := hn.else_ u hc
    exact ⟨o, rest, bt, h1, h2⟩

/-! ## Sizes -/

theorem sz_succ (g : GasCfg) (code : Array Instr) (u : Nat) (hu : u < code.size) :
    (scanS g code (u + 1)).pts.size =
      (scanS g code u).pts.size + (if (scanS g code u).sched.isSome then 1 else 0) + 1 := by
  rw [scanS_succ g code u hu, (step_pts g _ u _).1, flushAt_size]

theorem sz_ge (g : GasCfg) (code : Array Instr) : ∀ d u, u + d ≤ code.size →
    (scanS g code u).pts.size + d ≤ (scanS g code (u + d)).pts.size := by
  intro d
  induction d with
  | zero => intro u _; simp
  | succ d ih =>
    intro u h
    have := ih u (by omega)
    have h2 := sz_succ g code (u + d) (by omega)
    rw [show u + (d + 1) = u + d + 1 by omega, h2]
    split <;> omega

theorem sz_mono (g : GasCfg) (code : Array Instr) (u v : Nat) (h : u ≤ v) (hv : v ≤ code.size) :
    (scanS g code u).pts.size ≤ (scanS g code v).pts.size := by
  have := sz_ge g code (v - u) u (by omega)
  rw [show u + (v - u) = v by omega] at this; omega

theorem sz_lt (g : GasCfg) (code : Array Instr) (u v : Nat) (h : u < v) (hv : v ≤ code.size) :
    (scanS g code u).pts.size < (scanS g code v).pts.size := by
  have := sz_ge g code (v - u) u (by omega)
  rw [show u + (v - u) = v by omega] at this; omega

/-! ## Global mutations -/

def MutG (g : GasCfg) (code : Array Instr) (x : Nat) (k : IK) : Prop :=
  (k = .pre ∧ ∃ o bt, code[o]? = some (.loop bt) ∧ o < code.size ∧ x = (scanS g code (o + 1)).pts.size - 1) ∨
  (k = .post ∧ ∃ o bt, code[o]? = some (.loop bt) ∧ o < code.size ∧ x = (scanS g code (o + 1)).pts.size)

theorem mutOK_G (g : GasCfg) (code : Array Instr) (u : Nat) (I : Inv g code u) (x : Nat) (k : IK)
    (h : MutOK (frs (scanS g code u)) x k) : MutG g code x k := by
  obtain ⟨f, hf, p, q, hk, hx⟩ := h
  obtain ⟨l, hl, hlf⟩ := List.getElem_of_mem hf
  have hl' : (frs (scanS g code u))[l]? = some f := by rw [List.getElem?_eq_getElem hl, hlf]
  have hlen := I.len
  by_cases hlE : l < (openAt code u).length
  · obtain ⟨o, ho⟩ : ∃ o, (openAt code u)[l]? = some o := ⟨_, List.getElem?_eq_getElem hlE⟩
    obtain ⟨f', hf', hfk⟩ := I.kind l o ho
    rw [hl'] at hf'; cases hf'
    have hmem := openAt_mem code u o (List.mem_of_getElem? ho)
    obtain ⟨i, hi, _⟩ := hmem.2
    have ho_lt : o < code.size := by
      rcases Nat.lt_or_ge o code.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hi; cases hi
    unfold FrK at hfk
    split at hfk
    · rename_i bt hc
      rw [hk] at hfk
      simp only [BTK.loop.injEq] at hfk
      obtain ⟨rfl, rfl⟩ := hfk
      rcases hx with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, o, bt, hc, ho_lt, rfl⟩
      · exact Or.inr ⟨rfl, o, bt, hc, ho_lt, rfl⟩
    · rw [hk] at hfk; cases hfk
    · rw [hk] at hfk; rcases hfk.1 with h | h <;> cases h
    · exact hfk.elim
  · have hlE' : l = (openAt code u).length := by
      have : l < (openAt code u).length + 1 := by rw [← hlen]; exact hl
      omega
    rw [hlE'] at hl'
    rcases I.fn f hl' with h | h <;> rw [hk] at h <;> cases h

/-- Points only change kind, and only by a global mutation. -/
theorem track (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) :
    ∀ d t, t + d ≤ pf.code.size → ∀ x pt, (scanS g pf.code t).pts[x]? = some pt →
      ∃ pt', (scanS g pf.code (t + d)).pts[x]? = some pt' ∧ pt'.off = pt.off ∧ pt'.fee = pt.fee ∧
        (pt'.k = pt.k ∨ MutG g pf.code x pt'.k) := by
  intro d
  induction d with
  | zero => intro t _ x pt h; exact ⟨pt, h, rfl, rfl, Or.inl rfl⟩
  | succ d ih =>
    intro t ht x pt h
    obtain ⟨p1, h1, o1, f1, k1⟩ := ih t (by omega) x pt h
    have hu : t + d < pf.code.size := by omega
    have I := inv_all g pf hn (t + d) (by omega)
    have hst := step_pts g (scanS g pf.code (t + d)) (t + d) pf.code[t + d]
    rw [← scanS_succ g pf.code _ hu] at hst
    have hx : ((flushAt (t + d) (scanS g pf.code (t + d))).pts.push
        (ownPt g (flushAt (t + d) (scanS g pf.code (t + d))) (t + d) pf.code[t + d]))[x]? = some p1 := by
      rw [Array.getElem?_push, flushAt_pts]
      have hxl : x < (scanS g pf.code (t + d)).pts.size := (Array.getElem?_eq_some_iff.mp h1).1
      split
      · rename_i k f hs
        rw [if_neg (by simp; omega), Array.getElem?_push, if_neg (by omega)]; exact h1
      · rw [if_neg (by omega)]; exact h1
    obtain ⟨p2, h2, o2, f2, k2⟩ := hst.2 x p1 hx
    refine ⟨p2, by rw [show t + (d + 1) = t + d + 1 by omega]; exact h2, by rw [o2, o1], by rw [f2, f1], ?_⟩
    rcases k2 with k2 | k2
    · rw [k2]; exact k1
    · exact Or.inr (mutOK_G g pf.code (t + d) I x _ k2)

end NearSpecV3.Wasm.FuelGas
