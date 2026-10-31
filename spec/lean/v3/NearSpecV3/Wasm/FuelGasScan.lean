import NearSpecV3.Wasm.FuelGasOpt
namespace NearSpecV3.Wasm.FuelGas
open NearSpecV3.Wasm

def flushAt (i : Nat) (s : GS) : GS :=
  match s.sched with
  | some (k, f) => { s with pts := s.pts.push ⟨i, k, f⟩, sched := none, off := i }
  | none => { s with off := i }

def gstep (g : GasCfg) (s : GS) (i : Nat) (ins : Instr) : GS :=
  ((gInstr g ins).run (flushAt i s)).2

def gstep' (g : GasCfg) (code : Array Instr) (s : GS) (i : Nat) : GS :=
  if h : i < code.size then gstep g s i code[i] else s

def scanS (g : GasCfg) (code : Array Instr) : Nat → GS
  | 0 => {}
  | u + 1 => gstep' g code (scanS g code u) u

theorem forIn'_scan (g : GasCfg) (code : Array Instr) :
    ∀ (l : List Nat) (f : (a : Nat) → a ∈ l → PUnit → StateM GS (ForInStep PUnit))
      (hf : ∀ a h u s, (f a h u).run s = (ForInStep.yield PUnit.unit, gstep' g code s a))
      (u : PUnit) (s : GS),
    (forIn' l u f).run s = (PUnit.unit, l.foldl (gstep' g code) s) := by
  intro l
  induction l with
  | nil => intro f hf u s; rfl
  | cons a l ih =>
    intro f hf u s
    rw [List.forIn'_cons]
    simp only [StateT.run_bind, hf]
    exact ih _ (fun b hb u s => hf b _ u s) _ _

theorem scanS_foldl (g : GasCfg) (code : Array Instr) :
    ∀ m, (List.range m).foldl (gstep' g code) {} = scanS g code m := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem forIn_tbl (n : Nat) : ∀ (l : List Pt)
    (f : Pt → Array (Option (IK × Fee)) → Id (ForInStep (Array (Option (IK × Fee)))))
    (hf : ∀ p t, f p t = pure (ForInStep.yield (tStep n t p))) init,
    forIn l init f = pure (l.foldl (tStep n) init) := by
  intro l
  induction l with
  | nil => intro f hf init; rfl
  | cons a l ih =>
    intro f hf init
    rw [List.forIn_cons, hf]
    exact ih f hf _

theorem gasTable_eq (g : GasCfg) (code : Array Instr) :
    gasTable g code true =
      (optimize (scanS g code code.size).pts true).toList.foldl (tStep code.size)
        (Array.replicate code.size none) := by
  unfold gasTable
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range']
  split
  rename_i x s heq
  have hs : s = scanS g code code.size := by
    have := congrArg Prod.snd heq
    simp only [StateT.run_bind] at this
    rw [forIn'_scan g code] at this
    · rw [← this, ← scanS_foldl]
      simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
      rw [List.range_eq_range']
      rfl
    · intro a h u s
      have ha : a < code.size := by simp [Std.Legacy.Range.size] at h; omega
      simp only [gstep', ha, dite_true, gstep, flushAt]
      simp only [StateT.run_bind, StateT.run_modify]
      cases s.sched <;> rfl
  subst hs
  rw [← Array.forIn_toList, forIn_tbl code.size _ _ (fun p t => by unfold tStep; split <;> rfl)]
  rfl


/-! ## Frames and `gAdjust` -/

def frs (s : GS) : List GF := s.cur :: s.stack

def adjK : BTK → BTK
  | .loop p q => .loop p q
  | _ => .forward

def mutP (pts : Array Pt) : BTK → Array Pt
  | .loop p q => (pts.modify q fun x => { x with k := .post }).modify p fun x => { x with k := .pre }
  | _ => pts

def adjF (f : GF) : GF := { f with kind := adjK f.kind }

theorem adjustKind_eq (s : GS) (k : BTK) : adjustKind s k = ({ s with pts := mutP s.pts k }, adjK k) := by
  cases k <;> rfl

theorem gAdjust_run (fi : Nat) (s : GS) :
    ((gAdjust fi).run s).2 =
      if h : fi < (frs s).length then
        { s with pts := mutP s.pts ((frs s)[fi]).kind,
                 cur := ((frs s).set fi (adjF (frs s)[fi]))[0]'(by simp [frs]),
                 stack := ((frs s).set fi (adjF (frs s)[fi])).tail }
      else s := by
  unfold gAdjust
  simp only [StateT.run_modify]
  rcases fi with _ | fi
  · simp [frs, adjustKind_eq, adjF]; rfl
  · simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    by_cases h : fi < s.stack.length
    · rw [List.getElem?_eq_getElem h]
      simp only [adjustKind_eq]
      rw [dif_pos (by simp [frs]; omega)]
      simp [frs, adjF]; rfl
    · rw [List.getElem?_eq_none (by omega)]
      rw [dif_neg (by simp [frs]; omega)]; rfl


def adj1 (s : GS) (l : Nat) : GS := ((gAdjust l).run s).2

def adjSeq (s : GS) (ls : List Nat) : GS := ls.foldl adj1 s

theorem cons_get0_tail {α : Type} : ∀ (L : List α) (h : 0 < L.length), L[0] :: L.tail = L
  | _ :: _, _ => rfl

theorem frs_adj1 (s : GS) (fi : Nat) :
    frs (adj1 s fi) = if h : fi < (frs s).length then (frs s).set fi (adjF (frs s)[fi]) else frs s := by
  unfold adj1; rw [gAdjust_run]
  split
  · exact cons_get0_tail _ _
  · rfl

theorem adj1_pts (s : GS) (fi : Nat) :
    (adj1 s fi).pts = if h : fi < (frs s).length then mutP s.pts ((frs s)[fi]).kind else s.pts := by
  unfold adj1; rw [gAdjust_run]; split <;> rfl

theorem adj1_sched (s : GS) (fi : Nat) : (adj1 s fi).sched = s.sched := by
  unfold adj1; rw [gAdjust_run]; split <;> rfl

theorem adj1_off (s : GS) (fi : Nat) : (adj1 s fi).off = s.off := by
  unfold adj1; rw [gAdjust_run]; split <;> rfl

theorem adjK_idem (k : BTK) : adjK (adjK k) = adjK k := by cases k <;> rfl

theorem frs_adj1_get (s : GS) (fi j : Nat) :
    (frs (adj1 s fi))[j]? = ((frs s)[j]?).map (fun f => if j = fi then adjF f else f) := by
  rw [frs_adj1]
  split
  · rename_i h
    rw [List.getElem?_set]
    by_cases hj : fi = j
    · subst hj; simp [h]
    · rw [if_neg hj]; simp [Ne.symm hj]
  · rename_i h
    by_cases hj : j = fi
    · subst hj; simp [List.getElem?_eq_none (Nat.le_of_not_lt h)]
    · simp [hj]

theorem frs_adjSeq_get : ∀ (ls : List Nat) (s : GS) (j : Nat),
    (frs (adjSeq s ls))[j]? = ((frs s)[j]?).map (fun f => if j ∈ ls then adjF f else f) := by
  intro ls
  induction ls with
  | nil => intro s j; simp [adjSeq]
  | cons l ls ih =>
    intro s j
    simp only [adjSeq, List.foldl_cons] at ih ⊢
    rw [ih, frs_adj1_get]
    cases (frs s)[j]? with
    | none => rfl
    | some f =>
      simp only [Option.map_some, List.mem_cons]
      by_cases h1 : j = l <;> by_cases h2 : j ∈ ls <;> simp [h1, h2, adjF, adjK_idem]

theorem frs_adjSeq_length (ls : List Nat) (s : GS) : (frs (adjSeq s ls)).length = (frs s).length := by
  induction ls generalizing s with
  | nil => rfl
  | cons l ls ih =>
    simp only [adjSeq, List.foldl_cons] at ih ⊢
    rw [ih, frs_adj1]; split <;> simp


def mutPt (k : BTK) (x : Nat) (pt : Pt) : Pt :=
  match k with
  | .loop p q => if p = x then { pt with k := .pre } else if q = x then { pt with k := .post } else pt
  | _ => pt

theorem mutP_get (pts : Array Pt) (k : BTK) (x : Nat) :
    (mutP pts k)[x]? = (pts[x]?).map (mutPt k x) := by
  cases k with
  | loop p q =>
    simp only [mutP, Array.getElem?_modify]
    cases h : pts[x]? <;> by_cases hp : p = x <;> by_cases hq : q = x <;> simp [hp, hq, mutPt, h]
  | _ => simp only [mutP]; cases pts[x]? <;> rfl

theorem mutPt_props (k : BTK) (x : Nat) (pt : Pt) :
    (mutPt k x pt).off = pt.off ∧ (mutPt k x pt).fee = pt.fee ∧
    ((mutPt k x pt).k = pt.k ∨ ∃ p q, k = .loop p q ∧
      ((x = p ∧ (mutPt k x pt).k = .pre) ∨ (x = q ∧ (mutPt k x pt).k = .post))) := by
  cases k with
  | loop p q =>
    by_cases hp : p = x
    · have e : mutPt (.loop p q) x pt = { pt with k := .pre } := by simp [mutPt, hp]
      rw [e]; exact ⟨rfl, rfl, Or.inr ⟨p, q, rfl, Or.inl ⟨hp.symm, rfl⟩⟩⟩
    · by_cases hq : q = x
      · have e : mutPt (.loop p q) x pt = { pt with k := .post } := by simp [mutPt, hp, hq]
        rw [e]; exact ⟨rfl, rfl, Or.inr ⟨p, q, rfl, Or.inr ⟨hq.symm, rfl⟩⟩⟩
      · have e : mutPt (.loop p q) x pt = pt := by simp [mutPt, hp, hq]
        rw [e]; exact ⟨rfl, rfl, Or.inl rfl⟩
  | _ => exact ⟨rfl, rfl, Or.inl rfl⟩

theorem mutP_size (pts : Array Pt) (k : BTK) : (mutP pts k).size = pts.size := by
  cases k <;> simp [mutP]

def MutOK (F : List GF) (x : Nat) (k : IK) : Prop :=
  ∃ f ∈ F, ∃ p q, f.kind = .loop p q ∧ ((x = p ∧ k = .pre) ∨ (x = q ∧ k = .post))

/-- Loop frames of `adjSeq` are loop frames of the start. -/
theorem adjSeq_loop (ls : List Nat) (s : GS) (f : GF) (hf : f ∈ frs (adjSeq s ls)) (p q : Nat)
    (hk : f.kind = .loop p q) : ∃ f0 ∈ frs s, f0.kind = .loop p q := by
  obtain ⟨j, hj, hjf⟩ := List.getElem_of_mem hf
  have h1 := frs_adjSeq_get ls s j
  rw [List.getElem?_eq_getElem hj, hjf] at h1
  cases h2 : (frs s)[j]? with
  | none => rw [h2] at h1; cases h1
  | some f0 =>
    rw [h2] at h1
    simp only [Option.map_some, Option.some.injEq] at h1
    refine ⟨f0, List.mem_of_getElem? h2, ?_⟩
    split at h1
    · subst h1; simp only [adjF] at hk; cases hk0 : f0.kind <;> simp_all [adjK]
    · subst h1; exact hk

theorem adjSeq_size (ls : List Nat) (s : GS) : (adjSeq s ls).pts.size = s.pts.size := by
  induction ls generalizing s with
  | nil => rfl
  | cons l ls ih =>
    simp only [adjSeq, List.foldl_cons] at ih ⊢
    rw [ih, adj1_pts]; split <;> simp [mutP_size]

theorem adjSeq_sched (ls : List Nat) (s : GS) : (adjSeq s ls).sched = s.sched := by
  induction ls generalizing s with
  | nil => rfl
  | cons l ls ih => simp only [adjSeq, List.foldl_cons] at ih ⊢; rw [ih, adj1_sched]

theorem adjSeq_pts (ls : List Nat) : ∀ (s : GS) x pt, s.pts[x]? = some pt →
    ∃ pt', (adjSeq s ls).pts[x]? = some pt' ∧ pt'.off = pt.off ∧ pt'.fee = pt.fee ∧
      (pt'.k = pt.k ∨ MutOK (frs s) x pt'.k) := by
  induction ls with
  | nil => intro s x pt h; exact ⟨pt, h, rfl, rfl, Or.inl rfl⟩
  | cons l ls ih =>
    intro s x pt h
    simp only [adjSeq, List.foldl_cons] at ih ⊢
    -- one step
    have step : ∃ pt1, (adj1 s l).pts[x]? = some pt1 ∧ pt1.off = pt.off ∧ pt1.fee = pt.fee ∧
        (pt1.k = pt.k ∨ MutOK (frs s) x pt1.k) := by
      rw [adj1_pts]
      split
      · rename_i hl
        rw [mutP_get, h]
        refine ⟨_, rfl, ?_⟩
        obtain ⟨a1, a2, a3⟩ := mutPt_props (frs s)[l].kind x pt
        refine ⟨a1, a2, ?_⟩
        rcases a3 with a3 | ⟨p, q, hk, hx⟩
        · exact Or.inl a3
        · exact Or.inr ⟨(frs s)[l], List.getElem_mem hl, p, q, hk, hx⟩
      · exact ⟨pt, h, rfl, rfl, Or.inl rfl⟩
    obtain ⟨pt1, h1, o1, f1, k1⟩ := step
    obtain ⟨pt', h', o', f', k'⟩ := ih (adj1 s l) x pt1 h1
    refine ⟨pt', h', by rw [o', o1], by rw [f', f1], ?_⟩
    rcases k' with k' | ⟨f, hf, p, q, hk, hx⟩
    · rw [k']; exact k1
    · right
      have : f ∈ frs (adjSeq s [l]) := hf
      obtain ⟨f0, hf0, hk0⟩ := adjSeq_loop [l] s f this p q hk
      exact ⟨f0, hf0, p, q, hk0, hx⟩

def NoClash (F : List GF) (q : Nat) : Prop := ∀ f ∈ F, ∀ p' q', f.kind = .loop p' q' → p' ≠ q

theorem adjSeq_post (p q : Nat) : ∀ (ls : List Nat) (s : GS), NoClash (frs s) q → q < s.pts.size →
    ((∃ pt, s.pts[q]? = some pt ∧ pt.k = .post) ∨
      ∃ j ∈ ls, ∃ f, (frs s)[j]? = some f ∧ f.kind = .loop p q) →
    ∃ pt, (adjSeq s ls).pts[q]? = some pt ∧ pt.k = .post := by
  intro ls
  induction ls with
  | nil =>
    intro s _ _ h
    rcases h with h | ⟨j, hj, _⟩
    · exact h
    · simp at hj
  | cons l ls ih =>
    intro s hnc hq h
    simp only [adjSeq, List.foldl_cons] at ih ⊢
    apply ih
    · intro f hf p' q' hk
      obtain ⟨f0, hf0, hk0⟩ := adjSeq_loop [l] s f hf p' q' hk
      exact hnc f0 hf0 p' q' hk0
    · rw [adj1_pts]; split <;> simp [mutP_size, hq]
    · rw [adj1_pts]
      by_cases hl : l < (frs s).length
      · rw [dif_pos hl, mutP_get]
        have hmut : ∀ pt, s.pts[q]? = some pt → (∀ p', (frs s)[l].kind ≠ .loop p' q) → pt.k = .post →
            ∃ pt, (Option.map (mutPt (frs s)[l].kind q) s.pts[q]?) = some pt ∧ pt.k = .post := by
          intro pt hpt hne hk
          rw [hpt]
          refine ⟨_, rfl, ?_⟩
          cases hkl : (frs s)[l].kind with
          | loop p' q' =>
            have := hnc (frs s)[l] (List.getElem_mem hl) p' q' hkl
            simp only [mutPt, if_neg this]
            split
            · rfl
            · exact hk
          | _ => simpa [mutPt] using hk
        rcases h with ⟨pt, hpt, hk⟩ | ⟨j, hj, f, hjf, hfk⟩
        · left
          cases hkl : (frs s)[l].kind with
          | loop p' q' =>
            have := hnc (frs s)[l] (List.getElem_mem hl) p' q' hkl
            rw [hpt]; refine ⟨_, rfl, ?_⟩
            simp only [mutPt, if_neg this]
            split
            · rfl
            · exact hk
          | _ => rw [hpt]; exact ⟨_, rfl, by simpa [mutPt] using hk⟩
        · rcases List.mem_cons.mp hj with hj | hj
          · subst hj
            left
            have hf : (frs s)[j] = f := by
              rw [List.getElem?_eq_getElem hl] at hjf; exact Option.some.inj hjf
            obtain ⟨pt, hpt⟩ : ∃ pt, s.pts[q]? = some pt := ⟨s.pts[q], by simp [hq]⟩
            rw [hpt, hf, hfk]
            have := hnc f (by rw [← hf]; exact List.getElem_mem hl) p q hfk
            exact ⟨_, rfl, by simp [mutPt, this]⟩
          · right
            refine ⟨j, hj, ?_⟩
            rw [frs_adj1_get, hjf]
            refine ⟨if j = l then adjF f else f, by simp, ?_⟩
            split
            · simp [adjF, hfk, adjK]
            · exact hfk
      · rw [dif_neg hl]
        rcases h with h | ⟨j, hj, f, hjf, hfk⟩
        · left; exact h
        · rcases List.mem_cons.mp hj with hj | hj
          · subst hj; rw [List.getElem?_eq_none (by omega)] at hjf; cases hjf
          · right
            refine ⟨j, hj, f, ?_, hfk⟩
            rw [frs_adj1, dif_neg hl]; exact hjf


/-! ## One instruction -/

def isCtl : Instr → Bool
  | .unreachable | .loop _ | .end_ | .if_ _ | .else_ | .block _ | .br _ | .brIf _ | .brTable _ _
  | .ret => true
  | _ => false

def sideE (g : GasCfg) : IK × Fee × Option (IK × Fee) := (.pre, .const g.regular, some (.post, Fee.zero))
def pureE (g : GasCfg) : IK × Fee × Option (IK × Fee) := (.pure, .const g.regular, none)

def plainE (g : GasCfg) : Instr → IK × Fee × Option (IK × Fee)
  | .memGrow | .memCopy | .memFill | .memInit _
  | .tableGrow _ | .tableFill _ | .tableCopy _ _ | .tableInit _ _ =>
    (.linear, ⟨g.linearBase, g.linearUnit⟩, some (.post, Fee.zero))
  | .load .. | .store .. | .call _ | .callIndirect .. | .tableGet _ | .tableSet _ => sideE g
  | .num op => if partialNum op then sideE g else pureE g
  | .float op => if floatPartial op then sideE g else pureE g
  | .floatLoad .. | .floatStore .. => sideE g
  | _ => pureE g

def pushOwn (s : GS) (k : IK) (f : Fee) : GS :=
  { s with pts := s.pts.push ⟨s.off, if s.cur.poly then .unreach else k, f⟩ }

def plainRes (s : GS) (e : IK × Fee × Option (IK × Fee)) : GS :=
  { pushOwn s e.1 e.2.1 with sched := match e.2.2 with | some x => some x | none => s.sched }

theorem gInstr_plain (g : GasCfg) (ins : Instr) (h : isCtl ins = false) (s : GS) :
    ((gInstr g ins).run s).2 = plainRes s (plainE g ins) := by
  cases ins <;> simp only [isCtl, Bool.true_eq_false] at h
  all_goals first | rfl | skip
  case num op =>
    by_cases hp : partialNum op = true
    · simp only [gInstr, plainE, hp, if_true]; rfl
    · simp only [gInstr, plainE, hp, if_false, Bool.false_eq_true]; rfl
  case float op =>
    by_cases hp : floatPartial op = true
    · simp only [gInstr, plainE, hp, if_true]; rfl
    · simp only [gInstr, plainE, hp, if_false, Bool.false_eq_true]; rfl

def setPoly (s : GS) : GS := { s with cur := { s.cur with poly := true } }

def baseSide (s : GS) (k : IK) (f : Fee) : GS :=
  { pushOwn s k f with sched := some (.post, Fee.zero) }

theorem forIn_adj : ∀ (l : List Nat) (s : GS),
    (forIn (m := StateM GS) l PUnit.unit (fun a _ => do gAdjust a; pure (ForInStep.yield PUnit.unit))).run s =
      (PUnit.unit, adjSeq s l) := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih =>
    intro s
    rw [List.forIn_cons]
    simp only [StateT.run_bind]
    exact ih _

theorem gInstr_unreachable (g : GasCfg) (s : GS) :
    ((gInstr g .unreachable).run s).2 =
      setPoly { pushOwn s .pre (.const g.regular) with sched := some (.unreach, Fee.zero) } := rfl

theorem gInstr_loop (g : GasCfg) (bt : BT) (s : GS) :
    ((gInstr g (.loop bt)).run s).2 =
      { pushOwn s .pure Fee.zero with
        sched := some (.pure, .const g.regular),
        stack := s.cur :: s.stack, cur := ⟨s.cur.poly, .loop s.pts.size (s.pts.size + 1)⟩ } := by
  simp [gInstr, gBefore, gAfter, gNewFrame, pushOwn]; rfl

def isFwd : BTK → Bool
  | .forward => true
  | _ => false

def popF (s : GS) : GS :=
  match s.stack with
  | f :: rest => { s with cur := f, stack := rest }
  | [] => s

theorem gInstr_end (g : GasCfg) (s : GS) :
    ((gInstr g .end_).run s).2 =
      popF (if isFwd s.cur.kind then baseSide s .pre Fee.zero else pushOwn s .pure Fee.zero) := by
  simp only [gInstr]
  cases h : s.cur.kind <;> simp [h, isFwd, gSide, gPure, gBefore, gAfter, gEndFrame, popF, baseSide,
    pushOwn] <;> cases s.stack <;> rfl

theorem gInstr_if (g : GasCfg) (bt : BT) (s : GS) :
    ((gInstr g (.if_ bt)).run s).2 =
      { baseSide s .pre (.const g.regular) with stack := s.cur :: s.stack, cur := ⟨s.cur.poly, .forward⟩ } := by
  rfl

theorem gInstr_block (g : GasCfg) (bt : BT) (s : GS) :
    ((gInstr g (.block bt)).run s).2 =
      { pushOwn s .pure Fee.zero with stack := s.cur :: s.stack, cur := ⟨s.cur.poly, .untaken⟩ } := by
  rfl

theorem gInstr_else (g : GasCfg) (s : GS) :
    ((gInstr g .else_).run s).2 =
      { popF s with
        pts := s.pts.push ⟨s.off, if (popF s).cur.poly then .unreach else .pre, Fee.zero⟩,
        sched := some (.post, Fee.zero), cur := ⟨(popF s).cur.poly, .forward⟩,
        stack := (popF s).cur :: (popF s).stack } := by
  cases hs : s.stack <;> simp [gInstr, gEndFrame, gNewFrame, gSide, gBefore, gAfter, hs, popF] <;> rfl

theorem gInstr_br (g : GasCfg) (l : Nat) (s : GS) :
    ((gInstr g (.br l)).run s).2 = setPoly (adjSeq (baseSide s .pre (.const g.regular)) [l]) := by
  rfl

theorem gInstr_brIf (g : GasCfg) (l : Nat) (s : GS) :
    ((gInstr g (.brIf l)).run s).2 = adjSeq (baseSide s .pre (.const g.regular)) [l] := by
  rfl

theorem gInstr_ret (g : GasCfg) (s : GS) :
    ((gInstr g .ret).run s).2 =
      setPoly (adjSeq (baseSide s .pre (.const g.regular)) [s.stack.length]) := by
  rfl

theorem gInstr_brTable (g : GasCfg) (ls : Array Nat) (d : Nat) (s : GS) :
    ((gInstr g (.brTable ls d)).run s).2 =
      setPoly (adjSeq (baseSide s .pre (.const g.regular)) (ls.toList ++ [d])) := by
  simp only [gInstr, StateT.run_bind]
  rw [← Array.forIn_toList]
  simp only [forIn_adj]
  simp only [adjSeq, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

end NearSpecV3.Wasm.FuelGas
