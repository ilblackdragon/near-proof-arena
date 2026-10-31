import NearSpecV3.Wasm.FuelGasInv
namespace NearSpecV3.Wasm.FuelGas
open NearSpecV3.Wasm

/-! ## Scheduled points -/

def schedOf (g : GasCfg) (s : GS) : Instr → Option (IK × Fee)
  | .unreachable => some (.unreach, Fee.zero)
  | .loop _ => some (.pure, .const g.regular)
  | .end_ => if isFwd s.cur.kind then some (.post, Fee.zero) else none
  | .block _ => none
  | .if_ _ | .else_ | .br _ | .brIf _ | .brTable _ _ | .ret => some (.post, Fee.zero)
  | i => (plainE g i).2.2

theorem plain_schedOf (g : GasCfg) (s : GS) (ins : Instr) (h : isCtl ins = false) :
    schedOf g s ins = (plainE g ins).2.2 := by
  cases ins <;> simp only [isCtl, Bool.true_eq_false] at h <;> rfl

theorem sched_step (g : GasCfg) (s : GS) (u : Nat) (ins : Instr) :
    (gstep g s u ins).sched = schedOf g s ins := by
  unfold gstep
  by_cases hc : isCtl ins = false
  · rw [gInstr_plain g ins hc, plain_schedOf g s ins hc]
    simp only [plainRes]
    split <;> simp_all [flushAt_sched]
  · cases ins
    case unreachable => rw [gInstr_unreachable]; rfl
    case loop bt => rw [gInstr_loop]; rfl
    case if_ bt => rw [gInstr_if]; rfl
    case else_ => rw [gInstr_else]; rfl
    case end_ =>
      rw [gInstr_end]; simp only [schedOf, flushAt_cur]
      unfold popF
      split <;> split <;> simp_all [baseSide, pushOwn, flushAt_sched]
    case br l => rw [gInstr_br]; simp [setPoly, adjSeq_sched, baseSide]; rfl
    case brIf l => rw [gInstr_brIf]; simp [adjSeq_sched, baseSide]; rfl
    case brTable ls d => rw [gInstr_brTable]; simp [setPoly, adjSeq_sched, baseSide]; rfl
    case ret => rw [gInstr_ret]; simp [setPoly, adjSeq_sched, baseSide]; rfl
    case block bt => rw [gInstr_block]; simp [pushOwn, flushAt_sched]; rfl
    all_goals simp [isCtl] at hc

theorem schedOf_kind (g : GasCfg) (s : GS) (ins : Instr) (k : IK) (f : Fee)
    (h : schedOf g s ins = some (k, f)) :
    k = .post ∨ (k = .unreach ∧ ins = .unreachable) ∨ (k = .pure ∧ ∃ bt, ins = .loop bt) := by
  by_cases hc : isCtl ins = false
  · rw [plain_schedOf g s ins hc] at h
    left
    cases ins <;> simp only [isCtl, Bool.true_eq_false] at hc <;>
      simp only [plainE, sideE, pureE] at h <;> (try split at h) <;> simp_all
  · cases ins <;> simp only [isCtl, not_true_eq_false] at hc <;> simp only [schedOf] at h
    all_goals first
      | (simp at h; obtain ⟨rfl, _⟩ := h; simp)
      | (split at h <;> simp at h; obtain ⟨rfl, _⟩ := h; simp)
      | simp at h

theorem schedOf_call (g : GasCfg) (s : GS) (ins : Instr) (h : isCallI ins = true) :
    schedOf g s ins = some (.post, Fee.zero) := by
  cases ins <;> simp_all [isCallI] <;> rfl

theorem sched_zero (g : GasCfg) (code : Array Instr) : (scanS g code 0).sched = none := rfl

theorem sched_scan (g : GasCfg) (code : Array Instr) (u : Nat) (hu : u < code.size) :
    (scanS g code (u + 1)).sched = schedOf g (scanS g code u) code[u] := by
  rw [scanS_succ g code u hu, sched_step]

/-! ## Final points -/

theorem popF_flush (u : Nat) (s : GS) : (popF (flushAt u s)).cur = (popF s).cur := by
  unfold popF; rw [flushAt_stack]; split <;> simp [flushAt_cur]

theorem ownPt_flush (g : GasCfg) (u : Nat) (s : GS) (ins : Instr) :
    ownPt g (flushAt u s) u ins = ownPt g s u ins := by
  unfold ownPt
  have h1 : ownReq g (flushAt u s) ins = ownReq g s ins := by
    cases ins <;> simp [ownReq, flushAt_cur]
  have h2 : ownPoly (flushAt u s) ins = ownPoly s ins := by
    cases ins <;> simp [ownPoly, flushAt_cur, popF_flush]
  rw [h1, h2]

theorem own_final (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (t : Nat)
    (ht : t < pf.code.size) :
    ∃ pt, (scanS g pf.code pf.code.size).pts[(scanS g pf.code (t + 1)).pts.size - 1]? = some pt ∧
      pt.off = t ∧ pt.fee = (ownReq g (scanS g pf.code t) pf.code[t]).2 ∧
      (pt.k = (if ownPoly (scanS g pf.code t) pf.code[t] then .unreach
        else (ownReq g (scanS g pf.code t) pf.code[t]).1) ∨
       MutG g pf.code ((scanS g pf.code (t + 1)).pts.size - 1) pt.k) := by
  have hst := step_pts g (scanS g pf.code t) t pf.code[t]
  rw [← scanS_succ g pf.code t ht, ownPt_flush] at hst
  have hx : ((flushAt t (scanS g pf.code t)).pts.push (ownPt g (scanS g pf.code t) t pf.code[t]))[
      (scanS g pf.code (t + 1)).pts.size - 1]? = some (ownPt g (scanS g pf.code t) t pf.code[t]) := by
    rw [hst.1]; simp
  obtain ⟨p1, h1, o1, f1, k1⟩ := hst.2 _ _ hx
  have hk1 : p1.k = (ownPt g (scanS g pf.code t) t pf.code[t]).k ∨
      MutG g pf.code ((scanS g pf.code (t + 1)).pts.size - 1) p1.k := by
    rcases k1 with k1 | k1
    · exact Or.inl k1
    · exact Or.inr (mutOK_G g pf.code t (inv_all g pf hn t (by omega)) _ _ k1)
  obtain ⟨p2, h2, o2, f2, k2⟩ := track g pf hn (pf.code.size - (t + 1)) (t + 1) (by omega) _ p1 h1
  rw [show t + 1 + (pf.code.size - (t + 1)) = pf.code.size by omega] at h2
  refine ⟨p2, h2, by rw [o2, o1]; rfl, by rw [f2, f1]; rfl, ?_⟩
  rcases k2 with k2 | k2
  · rw [k2]; exact hk1
  · exact Or.inr k2

theorem sched_final (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (t : Nat)
    (ht : t < pf.code.size) (k : IK) (f : Fee) (hs : (scanS g pf.code t).sched = some (k, f)) :
    ∃ pt, (scanS g pf.code pf.code.size).pts[(scanS g pf.code t).pts.size]? = some pt ∧
      pt.off = t ∧ pt.fee = f ∧ (pt.k = k ∨ MutG g pf.code (scanS g pf.code t).pts.size pt.k) := by
  have hst := step_pts g (scanS g pf.code t) t pf.code[t]
  rw [← scanS_succ g pf.code t ht] at hst
  have hx : ((flushAt t (scanS g pf.code t)).pts.push (ownPt g (flushAt t (scanS g pf.code t)) t pf.code[t]))[
      (scanS g pf.code t).pts.size]? = some ⟨t, k, f⟩ := by
    rw [flushAt_pts, hs]; simp only
    rw [Array.getElem?_push, if_neg (by simp), Array.getElem?_push, if_pos rfl]
  obtain ⟨p1, h1, o1, f1, k1⟩ := hst.2 _ _ hx
  have hk1 : p1.k = k ∨ MutG g pf.code (scanS g pf.code t).pts.size p1.k := by
    rcases k1 with k1 | k1
    · exact Or.inl k1
    · exact Or.inr (mutOK_G g pf.code t (inv_all g pf hn t (by omega)) _ _ k1)
  obtain ⟨p2, h2, o2, f2, k2⟩ := track g pf hn (pf.code.size - (t + 1)) (t + 1) (by omega) _ p1 h1
  rw [show t + 1 + (pf.code.size - (t + 1)) = pf.code.size by omega] at h2
  refine ⟨p2, h2, by rw [o2, o1], by rw [f2, f1], ?_⟩
  rcases k2 with k2 | k2
  · rw [k2]; exact hk1
  · exact Or.inr k2

/-- A scheduled point is never the own point of a loop. -/
theorem sched_not_pre (g : GasCfg) (code : Array Instr) (t : Nat) (ht : t < code.size)
    (hs : (scanS g code t).sched.isSome = true) (o : Nat) (ho : o < code.size) :
    (scanS g code t).pts.size ≠ (scanS g code (o + 1)).pts.size - 1 := by
  have h1 := sz_succ g code t ht
  rw [if_pos hs] at h1
  rcases Nat.lt_or_ge o t with h | h
  · have := sz_mono g code (o + 1) t (by omega) (by omega)
    have := sz_lt g code o (o + 1) (by omega) (by omega)
    omega
  · have := sz_mono g code (t + 1) (o + 1) (by omega) (by omega)
    omega

theorem sched_final_k (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (t : Nat)
    (ht : t < pf.code.size) (k : IK) (f : Fee) (hs : (scanS g pf.code t).sched = some (k, f)) :
    ∃ pt, (scanS g pf.code pf.code.size).pts[(scanS g pf.code t).pts.size]? = some pt ∧
      pt.off = t ∧ pt.fee = f ∧ (pt.k = k ∨ pt.k = .post) := by
  obtain ⟨pt, h1, h2, h3, h4⟩ := sched_final g pf hn t ht k f hs
  refine ⟨pt, h1, h2, h3, ?_⟩
  rcases h4 with h4 | ⟨_, o, bt, _, ho, hx⟩ | ⟨h4, _⟩
  · exact Or.inl h4
  · exact absurd hx (sched_not_pre g pf.code t ht (by rw [hs]; rfl) o ho)
  · exact Or.inr h4

/-! ## Liveness and the poly flag -/

theorem cur_get0 (s : GS) : (frs s)[0]? = some s.cur := rfl

theorem inh_iter (g : GasCfg) (code : Array Instr) (u : Nat) (I : Inv g code u) :
    ∀ (l : Nat) (f : GF), (frs (scanS g code u))[l]? = some f → f.poly = true → (scanS g code u).cur.poly = true := by
  intro l
  induction l with
  | zero => intro f h hp; rw [cur_get0] at h; cases h; exact hp
  | succ l ih =>
    intro f h hp
    have hl : l < (frs (scanS g code u)).length := by
      have := (List.getElem?_eq_some_iff.mp h).1; omega
    exact ih _ (List.getElem?_eq_getElem hl) (I.inh l _ f (List.getElem?_eq_getElem hl) h hp)

theorem poly_plain (g : GasCfg) (s : GS) (u : Nat) (ins : Instr) (h : isCtl ins = false) :
    (gstep g s u ins).cur.poly = s.cur.poly := by
  have := congrArg (fun L => L[0]?) (frs_plain g s u ins h)
  simp [frs] at this; rw [this]

theorem poly_open (g : GasCfg) (s : GS) (u : Nat) (ins : Instr) (h : isOpener ins = true) :
    (gstep g s u ins).cur.poly = s.cur.poly := by
  cases ins <;> simp [isOpener] at h
  · have := congrArg (fun L => L[0]?) (frs_block g s u ‹_›); simp [frs] at this; rw [this]
  · have := congrArg (fun L => L[0]?) (frs_loop g s u ‹_›); simp [frs] at this; rw [this]
  · have := congrArg (fun L => L[0]?) (frs_if g s u ‹_›); simp [frs] at this; rw [this]

theorem poly_brIf (g : GasCfg) (s : GS) (u l : Nat) : (gstep g s u (.brIf l)).cur.poly = s.cur.poly := by
  have := frs_brIf g s u l 0
  simp only [frs, List.getElem?_cons_zero, Option.map_some, Option.some.injEq] at this
  rw [this]; exact (adjAt_props [l] 0 s.cur).2.2.1 |> fun _ => by unfold adjAt; split <;> rfl

theorem cur_end (g : GasCfg) (s : GS) (u : Nat) (f : GF) (L : List GF) (hs : s.stack = f :: L) :
    (gstep g s u .end_).cur = f := by
  have := congrArg (fun L => L[0]?) (frs_end g s u)
  simp [frs, hs] at this; exact this

theorem stack_ne (g : GasCfg) (code : Array Instr) (u : Nat) (I : Inv g code u) (o : Nat) (rest : List Nat)
    (h : openAt code u = o :: rest) : ∃ f L, (scanS g code u).stack = f :: L ∧
      (frs (scanS g code u))[1]? = some f := by
  have hlen := I.len
  rw [h] at hlen
  cases hs : (scanS g code u).stack with
  | nil => simp [frs, hs] at hlen
  | cons f L => exact ⟨f, L, rfl, by simp [frs, hs]⟩

/-- Leaving a block at its `end`: the outer frame is current again. -/
theorem poly_after_end (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (e o : Nat)
    (rest : List Nat) (he : pf.code[e]? = some .end_) (henc : openAt pf.code e = o :: rest) :
    (scanS g pf.code (e + 1)).cur.poly = (scanS g pf.code o).cur.poly := by
  have hlt : e < pf.code.size := by
    rcases Nat.lt_or_ge e pf.code.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at he; cases he
  have I := inv_all g pf hn e (by omega)
  obtain ⟨f, L, hs, h1⟩ := stack_ne g pf.code e I o rest henc
  obtain ⟨f', h1', hp⟩ := I.par 0 o (by rw [henc]; rfl)
  rw [h1] at h1'; cases h1'
  have hc : pf.code[e] = .end_ := by simpa [hlt] using he
  rw [scanS_succ g pf.code e hlt, hc, cur_end g _ e f L hs, hp]

theorem lt_of_get (code : Array Instr) (x : Nat) (i : Instr) (h : code[x]? = some i) : x < code.size := by
  rcases Nat.lt_or_ge x code.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at h; cases h

/-- A label target of an enclosing opener of a non-poly position is non-poly. -/
theorem poly_target (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (pc l o : Nat)
    (hpc : pc < pf.code.size) (hl : (openAt pf.code pc)[l]? = some o)
    (hp : (scanS g pf.code pc).cur.poly = false) :
    (scanS g pf.code o).cur.poly = false ∧
      (labTarget pf o < pf.code.size → (scanS g pf.code (labTarget pf o)).cur.poly = false) := by
  have I := inv_all g pf hn pc (by omega)
  obtain ⟨f, hf, hfp⟩ := I.par l o hl
  have ho : (scanS g pf.code o).cur.poly = false := by
    cases h : (scanS g pf.code o).cur.poly
    · rfl
    · rw [← hfp] at h; rw [inh_iter g pf.code pc I (l + 1) f hf h] at hp; cases hp
  refine ⟨ho, fun _ => ?_⟩
  obtain ⟨_, i, hi, hop⟩ := openAt_mem pf.code pc o (List.mem_of_getElem? hl)
  have hot := lt_of_get pf.code o i hi
  obtain ⟨_, _, hend, _, henc⟩ := hn.opener o i hi hop
  unfold labTarget
  rw [hi]
  split
  · rename_i bt hbt
    cases hbt
    rw [scanS_succ g pf.code o hot]
    have : pf.code[o] = .loop bt := by simpa [hot] using hi
    rw [this, poly_open g _ o _ rfl]; exact ho
  · rw [poly_after_end g pf hn _ o _ hend henc]; exact ho

theorem live_poly (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) :
    ∀ pc, Live pf (openAt pf.code) pc → pc < pf.code.size → (scanS g pf.code pc).cur.poly = false := by
  intro pc hl
  induction hl with
  | entry => intro _; rfl
  | step pc q j hl hs ih =>
    intro hq
    cases hs with
    | fall i hc hft hend =>
      have hpc := lt_of_get pf.code pc i hc
      have hp := ih hpc
      have hci : pf.code[pc] = i := by simpa [hpc] using hc
      rw [scanS_succ g pf.code pc hpc, hci]
      by_cases hct : isCtl i = false
      · rw [poly_plain g _ pc i hct]; exact hp
      · cases i <;> simp [isCtl, fallsThrough] at hct hft
        case loop bt => rw [poly_open g _ pc _ rfl]; exact hp
        case block bt => rw [poly_open g _ pc _ rfl]; exact hp
        case if_ bt => rw [poly_open g _ pc _ rfl]; exact hp
        case brIf l => rw [poly_brIf]; exact hp
        case end_ =>
          have hne := hend rfl
          obtain ⟨o, rest, henc⟩ : ∃ o rest, openAt pf.code pc = o :: rest := by
            cases h : openAt pf.code pc with
            | nil => exact absurd h hne
            | cons o rest => exact ⟨o, rest, rfl⟩
          have I := inv_all g pf hn pc (by omega)
          obtain ⟨f, L, hst, h1⟩ := stack_ne g pf.code pc I o rest henc
          rw [cur_end g _ pc f L hst]
          cases h : f.poly
          · rfl
          · rw [inh_iter g pf.code pc I 1 f h1 h] at hp; cases hp
    | ifElse bt hc hne =>
      have hpc := lt_of_get pf.code pc _ hc
      have hp := ih hpc
      rcases (hn.if_ pc bt hc).2 with h | ⟨_, _, hel, henc1⟩
      · exact absurd h hne
      · obtain ⟨o, rest, bt', henc, ho, _, _, henc2⟩ := hn.else_ _ hel
        rw [← henc2, henc1] at henc
        cases henc
        have hlt := lt_of_get pf.code _ _ hel
        have I := inv_all g pf hn (elseAt pf pc) (by omega)
        obtain ⟨f, L, hst, h1⟩ := stack_ne g pf.code _ I pc _ (by rw [← henc2, henc1])
        obtain ⟨f', h1', hfp⟩ := I.par 0 pc (by rw [← henc2, henc1]; rfl)
        rw [h1] at h1'; cases h1'
        have hc' : pf.code[elseAt pf pc] = .else_ := by simpa [hlt] using hel
        rw [scanS_succ g pf.code _ hlt, hc']
        have := congrArg (fun L => L[0]?) (frs_else g _ (elseAt pf pc) f L hst)
        simp [frs] at this
        rw [this, hfp]; exact hp
    | ifEnd bt hc heq =>
      have hpc := lt_of_get pf.code pc _ hc
      have hp := ih hpc
      obtain ⟨_, _, hend, _, henc⟩ := hn.opener pc _ hc rfl
      rw [poly_after_end g pf hn _ pc _ hend henc]; exact hp
    | else_ o rest hc henc =>
      have hpc := lt_of_get pf.code pc _ hc
      have hp := ih hpc
      obtain ⟨o', rest', bt, henc', ho, _, _, _⟩ := hn.else_ pc hc
      rw [henc] at henc'; cases henc'
      obtain ⟨_, _, hend, _, henc2⟩ := hn.opener o _ ho rfl
      rw [poly_after_end g pf hn _ o _ hend henc2]
      exact (poly_target g pf hn pc 0 o hpc (by rw [henc]; rfl) hp).1
    | br l q hc hbt =>
      have hpc := lt_of_get pf.code pc _ hc
      unfold brTarget at hbt
      cases ho : (openAt pf.code pc)[l]? with
      | none => rw [ho] at hbt; cases hbt
      | some o =>
        rw [ho] at hbt; cases hbt
        exact (poly_target g pf hn pc l o hpc ho (ih hpc)).2 hq
    | brIf l q hc hbt =>
      have hpc := lt_of_get pf.code pc _ hc
      unfold brTarget at hbt
      cases ho : (openAt pf.code pc)[l]? with
      | none => rw [ho] at hbt; cases hbt
      | some o =>
        rw [ho] at hbt; cases hbt
        exact (poly_target g pf hn pc l o hpc ho (ih hpc)).2 hq
    | brTable ls d l q hc _ hbt =>
      have hpc := lt_of_get pf.code pc _ hc
      unfold brTarget at hbt
      cases ho : (openAt pf.code pc)[l]? with
      | none => rw [ho] at hbt; cases hbt
      | some o =>
        rw [ho] at hbt; cases hbt
        exact (poly_target g pf hn pc l o hpc ho (ih hpc)).2 hq

/-- The label target of an enclosing opener follows a `loop` or an `end`. -/
theorem labTarget_prev (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (pc l o : Nat)
    (hl : (openAt pf.code pc)[l]? = some o) :
    0 < labTarget pf o ∧ pf.code[labTarget pf o - 1]? ≠ some .unreachable := by
  obtain ⟨_, i, hi, hop⟩ := openAt_mem pf.code pc o (List.mem_of_getElem? hl)
  obtain ⟨_, _, hend, _, _⟩ := hn.opener o i hi hop
  unfold labTarget
  rw [hi]
  split
  · rename_i bt hbt; cases hbt
    refine ⟨by omega, ?_⟩; rw [show o + 1 - 1 = o by omega, hi]; simp
  · refine ⟨by omega, ?_⟩; rw [show endAt pf o + 1 - 1 = endAt pf o by omega, hend]; simp

theorem live_prev (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (q : Nat)
    (hl : Live pf (openAt pf.code) q) (hq : 0 < q) : pf.code[q - 1]? ≠ some .unreachable := by
  cases hl with
  | entry => omega
  | step pc _ j _ hs =>
    cases hs with
    | fall i hc hft _ =>
      rw [show pc + 1 - 1 = pc by omega, hc]
      intro h; cases h; simp [fallsThrough] at hft
    | ifElse bt hc hne =>
      rcases (hn.if_ pc bt hc).2 with h | ⟨_, _, hel, _⟩
      · exact absurd h hne
      · rw [show elseAt pf pc + 1 - 1 = elseAt pf pc by omega, hel]; simp
    | ifEnd bt hc _ =>
      obtain ⟨_, _, hend, _, _⟩ := hn.opener pc _ hc rfl
      rw [show endAt pf pc + 1 - 1 = endAt pf pc by omega, hend]; simp
    | else_ o rest hc henc =>
      obtain ⟨o', rest', bt, henc', ho, _, _, _⟩ := hn.else_ pc hc
      rw [henc] at henc'; cases henc'
      obtain ⟨_, _, hend, _, _⟩ := hn.opener o _ ho rfl
      rw [show endAt pf o + 1 - 1 = endAt pf o by omega, hend]; simp
    | br l _ hc hbt =>
      unfold brTarget at hbt
      cases ho : (openAt pf.code pc)[l]? with
      | none => rw [ho] at hbt; cases hbt
      | some o => rw [ho] at hbt; cases hbt; exact (labTarget_prev pf hn pc l o ho).2
    | brIf l _ hc hbt =>
      unfold brTarget at hbt
      cases ho : (openAt pf.code pc)[l]? with
      | none => rw [ho] at hbt; cases hbt
      | some o => rw [ho] at hbt; cases hbt; exact (labTarget_prev pf hn pc l o ho).2
    | brTable ls d l _ hc _ hbt =>
      unfold brTarget at hbt
      cases ho : (openAt pf.code pc)[l]? with
      | none => rw [ho] at hbt; cases hbt
      | some o => rw [ho] at hbt; cases hbt; exact (labTarget_prev pf hn pc l o ho).2

/-! ## A branch to a loop marks the loop header point `.post` -/

theorem gstep_pts_branch (g : GasCfg) (s : GS) (u : Nat) (ins : Instr) (h : brLabels ins ≠ []) :
    (gstep g s u ins).pts = (adjSeq (baseSide (flushAt u s) .pre (.const g.regular)) (brLabels ins)).pts := by
  cases ins <;> simp [brLabels] at h <;> unfold gstep
  · rw [gInstr_br]; rfl
  · rw [gInstr_brIf]; rfl
  · rw [gInstr_brTable]; rfl

theorem loop_post (g : GasCfg) (pf : PFunc) (hn : NestOK pf (openAt pf.code)) (pc j o : Nat) (bt : BT)
    (hpc : pc < pf.code.size) (hj : j ∈ brLabels pf.code[pc]) (ho : (openAt pf.code pc)[j]? = some o)
    (hlo : pf.code[o]? = some (.loop bt)) :
    ∃ pt, (scanS g pf.code pf.code.size).pts[(scanS g pf.code (o + 1)).pts.size]? = some pt ∧
      pt.k = .post := by
  have I := inv_all g pf hn pc (by omega)
  have hopc := (openAt_mem pf.code pc o (List.mem_of_getElem? ho)).1
  have hot : o < pf.code.size := by omega
  -- the loop's header point is a scheduled point
  have hsch : (scanS g pf.code (o + 1)).sched.isSome = true := by
    have hc : pf.code[o] = .loop bt := by simpa [hot] using hlo
    rw [sched_scan g pf.code o hot, hc]; rfl
  obtain ⟨f, hf, hfk⟩ := I.kind j o ho
  unfold FrK at hfk
  rw [hlo] at hfk
  simp only at hfk
  have hnc : NoClash (frs (baseSide (flushAt pc (scanS g pf.code pc)) .pre (.const g.regular))) (scanS g pf.code (o + 1)).pts.size := by
    rw [frs_baseSide, flushAt_frs]
    intro f' hf' p' q' hk'
    have := mutOK_G g pf.code pc I p' .pre ⟨f', hf', p', q', hk', Or.inl ⟨rfl, rfl⟩⟩
    rcases this with ⟨_, o', bt', _, ho', hx⟩ | ⟨h, _⟩
    · rw [hx]; exact fun h => sched_not_pre g pf.code (o + 1) (by omega) hsch o' ho' h.symm
    · cases h
  have hqs : (scanS g pf.code (o + 1)).pts.size < (baseSide (flushAt pc (scanS g pf.code pc)) .pre (.const g.regular)).pts.size := by
    simp only [baseSide, pushOwn, Array.size_push]
    have := sz_mono g pf.code (o + 1) pc (by omega) (by omega)
    rw [flushAt_size]; split <;> omega
  have hne : brLabels pf.code[pc] ≠ [] := by intro h; rw [h] at hj; simp at hj
  obtain ⟨pt, hpt, hk⟩ := adjSeq_post ((scanS g pf.code (o + 1)).pts.size - 1) (scanS g pf.code (o + 1)).pts.size (brLabels pf.code[pc]) _ hnc hqs
    (Or.inr ⟨j, hj, f, by rw [frs_baseSide, flushAt_frs]; exact hf, hfk⟩)
  rw [← gstep_pts_branch g _ pc _ hne, ← scanS_succ g pf.code pc hpc] at hpt
  obtain ⟨p2, h2, _, _, k2⟩ := track g pf hn (pf.code.size - (pc + 1)) (pc + 1) (by omega) _ pt hpt
  rw [show pc + 1 + (pf.code.size - (pc + 1)) = pf.code.size by omega] at h2
  refine ⟨p2, h2, ?_⟩
  rcases k2 with k2 | ⟨_, o', bt', _, ho', hx⟩ | ⟨k2, _⟩
  · rw [k2, hk]
  · exact absurd hx (sched_not_pre g pf.code (o + 1) (by omega) hsch o' ho')
  · exact k2

end NearSpecV3.Wasm.FuelGas
