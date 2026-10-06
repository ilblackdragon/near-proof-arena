import ZkFormal.NearV3.Extract.HeadProof
import ZkFormal.NearV3.Render.UniqLocal

/-!
# ZkFormal.NearV3.Render.HeadRender — completeness of the `headV3` table

Honest rows: one 32-row head per `HeadE` (table order), then zero padding.  Row
`q = 32·t + i` of head `h = hs[t]`: `act = 1`, `hf = [i = 0]`, `hl = [i = 31]`, the head
constants `τ, rid, rlen, rres, mE`, `i`, and the shift registers
`reg m = pre[m + i]`, `preg m = post[m + i]` (`0` past the end), so `reg 0` on row `i` is
`pre[i]` and the first row holds the whole digests.

* `head_render_local`: `TableLocal HeadV3.table`;
* `head_render_traffic`: traffic `headTraffic hs`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl
open ZkFormal.NearV3.HeadV3 (act hf hl tau rid rlen rres i mE reg preg headConst)
open UniqLocal (ofNat0 ofNat1 boolF ofNat_succ)

/-- What the honest `headV3` trace needs. -/
structure HeadOk (hs : List HeadE) : Prop where
  wf : HeadWf hs
  pos : 0 < hs.length
  cap : 32 * hs.length ≤ 2 ^ 11

namespace HeadGen

def hd (hs : List HeadE) (t : Nat) : HeadE := hs.getD t default

/-- Active cells (row `q < 32·|hs|`). -/
def actCell (hs : List HeadE) (q : Nat) : Nat → Nat
  | 0 => 1
  | 1 => if q % 32 = 0 then 1 else 0
  | 2 => if q % 32 = 31 then 1 else 0
  | 3 => (hd hs (q / 32)).tau
  | 4 => (hd hs (q / 32)).rid
  | 5 => (hd hs (q / 32)).rlen
  | 6 => (hd hs (q / 32)).rres
  | 7 => q % 32
  | 8 => (hd hs (q / 32)).mE
  | j + 9 =>
    if j < 32 then (hd hs (q / 32)).pre.getD (j + q % 32) 0
    else if j < 64 then (hd hs (q / 32)).post.getD (j - 32 + q % 32) 0 else 0

def cell (hs : List HeadE) (_H q col : Nat) : Nat := if q < 32 * hs.length then actCell hs q col else 0

theorem cReg (hs : List HeadE) (q : Nat) {m : Nat} (hm : m < 32) :
    actCell hs q (reg m) = (hd hs (q / 32)).pre.getD (m + q % 32) 0 := by
  rw [show reg m = m + 9 by simp only [reg]; omega]; simp only [actCell, if_pos hm]

theorem cPreg (hs : List HeadE) (q : Nat) {m : Nat} (hm : m < 32) :
    actCell hs q (preg m) = (hd hs (q / 32)).post.getD (m + q % 32) 0 := by
  rw [show preg m = (m + 32) + 9 by simp only [preg]; omega]
  simp only [actCell, if_neg (show ¬ m + 32 < 32 by omega), if_pos (show m + 32 < 64 by omega),
    Nat.add_sub_cancel]

end HeadGen

/-- The honest `headV3` rows. -/
def headRows (hs : List HeadE) : Array Row :=
  mkTab (2 ^ logOf (32 * hs.length)) HeadV3.width (HeadGen.cell hs (2 ^ logOf (32 * hs.length)))

namespace HeadLocal
open HeadGen

section rows
variable {hs : List HeadE} (hok : HeadOk hs) {tr : Trace Fp} {tt : Nat} {pub : List Fp} {H : Nat}
  (hH : tr.height tt = H) (hHS : 32 * hs.length ≤ H)
  (hc : ∀ q col, q < H → col < 73 → tr.cell tt q col = Fp.ofNat (HeadGen.cell hs H q col))
include hok hH hHS hc

theorem cA {q : Nat} (hq : q < H) (ha : q < 32 * hs.length) {x : Nat} (hx : x < 73) :
    tr.cell tt q x = Fp.ofNat (actCell hs q x) := by
  rw [hc q x hq hx]; simp [HeadGen.cell, ha]

theorem cP {q : Nat} (hq : q < H) (ha : ¬ q < 32 * hs.length) {x : Nat} (hx : x < 73) : tr.cell tt q x = 0 := by
  rw [hc q x hq hx]; simp [HeadGen.cell, ha]; rfl

theorem rowC {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [act, hf, hl].map (fun x => Dsl.bool (c x)) ++
      [ .mul (c hf) (Dsl.not (c act)), .mul (c hl) (Dsl.not (c act)),
        .mul .isFirst (Dsl.not (c hf)),
        .mul .isLast (.mul (c act) (Dsl.not (c hl))),
        .mul (c hf) (c i), .mul (c hl) (sub (c i) (k 31)) ]) :
    e.eval tr tt q pub = 0 := by
  have hn := hok.pos
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at he
  by_cases ha : q < 32 * hs.length
  · have cq := fun (x : Nat) (hx : x < 73) => cA hok hH hHS hc hq ha hx
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_bool, eval_mul, eval_c, eval_not, eval_sub, eval_k, eval_isFirst, eval_isLast, hH,
      act, hf, hl, i, cq, Nat.reduceLT, actCell, natCast_eq] <;>
    repeat' split
    all_goals first | omega | (simp only [ofNat0, ofNat1]; grind) | (rename_i h; simp only [h, ofNat0]; grind)
  · have cq := fun (x : Nat) (hx : x < 73) => cP hok hH hHS hc hq ha hx
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [eval_bool, eval_mul, eval_c, eval_not, eval_sub, eval_k, eval_isFirst, eval_isLast, hH,
      act, hf, hl, i, cq, Nat.reduceLT] <;>
    repeat' split
    all_goals first | omega | grind

/-- Constraints gated by `act·(1 − hl)` (within a head). -/
theorem within {q : Nat} (hq : q < H) {E : Expr}
    (hE : E ∈ [Dsl.not (n act), n hf, sub (n i) (.add (c i) (k 1))] ∨ (∃ x ∈ headConst, E = sub (n x) (c x)) ∨
      ∃ j, j < 31 ∧ (E = sub (n (reg j)) (c (reg (j + 1))) ∨ E = sub (n (preg j)) (c (preg (j + 1))))) :
    (mul3 (c act) (Dsl.not (c hl)) E).eval tr tt q pub = 0 := by
  simp only [eval_mul3, eval_c, eval_not]
  by_cases ha : q < 32 * hs.length
  · rw [cA hok hH hHS hc hq ha (by decide : act < 73), cA hok hH hHS hc hq ha (by decide : hl < 73)]
    simp only [act, hl, actCell]
    by_cases hs31 : q % 32 = 31
    · simp only [hs31, if_true, ofNat1]; grind
    · simp only [hs31, if_false, ofNat0, ofNat1]
      have ha' : q + 1 < 32 * hs.length := by omega
      have hdiv : (q + 1) / 32 = q / 32 := by omega
      have hmod : (q + 1) % 32 = q % 32 + 1 := by omega
      have hnx : (q + 1) % H = q + 1 := Nat.mod_eq_of_lt (by omega)
      have cq := fun (x : Nat) (hx : x < 73) => cA hok hH hHS hc hq ha hx
      have cn := fun (x : Nat) (hx : x < 73) => cA hok hH hHS hc (q := q + 1) (by omega) ha' hx
      suffices E.eval tr tt q pub = 0 by rw [this]; grind
      simp only [headConst, List.mem_cons, List.not_mem_nil, or_false] at hE
      rcases hE with (rfl | rfl | rfl) | ⟨x, hx, rfl⟩ | ⟨j, hj, rfl | rfl⟩
      · simp only [eval_not, eval_n, hH, hnx, cn, act, Nat.reduceLT, actCell, ofNat1]; grind
      · simp only [eval_n, hH, hnx, cn, hf, Nat.reduceLT, actCell, hmod]; rfl
      · simp only [eval_sub, eval_add, eval_n, eval_c, eval_k, hH, hnx, cn, cq, i, Nat.reduceLT, actCell, hmod,
          ofNat_succ, natCast_eq]; simp only [ofNat0, ofNat1]; grind
      · rcases hx with rfl | rfl | rfl | rfl <;>
        simp only [eval_sub, eval_n, eval_c, hH, hnx, cn, cq, tau, rid, rlen, rres, Nat.reduceLT, actCell,
          hdiv] <;> grind
      · simp only [eval_sub, eval_n, eval_c, hH, hnx]
        rw [cn _ (by simp only [reg]; omega), cq _ (by simp only [reg]; omega), cReg hs _ (by omega),
          cReg hs _ (by omega), hdiv, hmod, show j + (q % 32 + 1) = j + 1 + q % 32 by omega]; grind
      · simp only [eval_sub, eval_n, eval_c, hH, hnx]
        rw [cn _ (by simp only [preg]; omega), cq _ (by simp only [preg]; omega), cPreg hs _ (by omega),
          cPreg hs _ (by omega), hdiv, hmod, show j + (q % 32 + 1) = j + 1 + q % 32 by omega]; grind
  · rw [cP hok hH hHS hc hq ha (by decide : act < 73)]; grind

theorem bound {q : Nat} (hq : q < H) {e : Expr}
    (he : e ∈ [ mul3 (c hl) (n act) (Dsl.not (n hf)), mul3 .isTransition (Dsl.not (c act)) (n act) ]) :
    e.eval tr tt q pub = 0 := by
  have hn := hok.pos
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  by_cases ha : q < 32 * hs.length
  · have cq := fun (x : Nat) (hx : x < 73) => cA hok hH hHS hc hq ha hx
    rcases he with rfl | rfl
    · simp only [eval_mul3, eval_c, eval_n, eval_not, hH, hl, act, hf, cq, Nat.reduceLT, actCell]
      split
      · rename_i h31
        by_cases h1 : q + 1 < 32 * hs.length
        · rw [Nat.mod_eq_of_lt (show q + 1 < H by omega), cA hok hH hHS hc (by omega) h1 (by decide),
            cA hok hH hHS hc (by omega) h1 (by decide)]
          simp only [actCell, show (q + 1) % 32 = 0 by omega, if_true, ofNat1]; grind
        · by_cases h2 : q + 1 < H
          · rw [Nat.mod_eq_of_lt h2, cP hok hH hHS hc (q := q + 1) h2 h1 (by decide : (0 : Nat) < 73)]; grind
          · rw [show (q + 1) % H = 0 by rw [show q + 1 = H by omega]; exact Nat.mod_self H,
              cA hok hH hHS hc (q := 0) (by omega) (by omega) (by decide : (0 : Nat) < 73),
              cA hok hH hHS hc (q := 0) (by omega) (by omega) (by decide : (1 : Nat) < 73)]
            simp only [actCell, Nat.zero_mod, if_true, ofNat1]; grind
      · simp only [ofNat0]; grind
    · simp only [eval_mul3, eval_c, eval_n, eval_not, act, cq, Nat.reduceLT, actCell, ofNat1]; grind
  · rcases he with rfl | rfl
    · simp only [eval_mul3, eval_c, hl, cP hok hH hHS hc hq ha (by decide : (2 : Nat) < 73)]; grind
    · simp only [eval_mul3, eval_c, eval_n, eval_not, eval_isTransition, act, hH]
      split
      · grind
      · rw [Nat.mod_eq_of_lt (show q + 1 < H by omega),
          cP hok hH hHS hc (q := q + 1) (by omega) (by omega) (by decide : (0 : Nat) < 73)]
        grind

theorem constr {q : Nat} (hq : q < H) {e : Expr} (he : e ∈ HeadV3.constraints) : e.eval tr tt q pub = 0 := by
  simp only [HeadV3.constraints] at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · rcases List.mem_append.1 he with he | he
      · rcases List.mem_append.1 he with he | he
        · exact rowC hok hH hHS hc hq (List.mem_append_left _ he)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact rowC hok hH hHS hc hq (List.mem_append_right _ (by simp))
          · exact rowC hok hH hHS hc hq (List.mem_append_right _ (by simp))
          · exact rowC hok hH hHS hc hq (List.mem_append_right _ (by simp))
          · exact rowC hok hH hHS hc hq (List.mem_append_right _ (by simp))
          · exact rowC hok hH hHS hc hq (List.mem_append_right _ (by simp))
          · exact rowC hok hH hHS hc hq (List.mem_append_right _ (by simp))
          · exact within hok hH hHS hc hq (Or.inl (by simp))
          · exact within hok hH hHS hc hq (Or.inl (by simp))
          · exact within hok hH hHS hc hq (Or.inl (by simp))
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
        exact within hok hH hHS hc hq (Or.inr (Or.inl ⟨x, hx, rfl⟩))
    · simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at he
      obtain ⟨j, hj, rfl | rfl⟩ := he
      · exact within hok hH hHS hc hq (Or.inr (Or.inr ⟨j, hj, Or.inl rfl⟩))
      · exact within hok hH hHS hc hq (Or.inr (Or.inr ⟨j, hj, Or.inr rfl⟩))
  · exact bound hok hH hHS hc hq he

theorem multBits {q : Nat} (hq : q < H) {it : Interaction} (hi : it ∈ HeadV3.interactions) {b : Expr}
    (hb : b ∈ it.mult) : b.eval tr tt q pub = 0 ∨ b.eval tr tt q pub = 1 := by
  simp only [HeadV3.interactions, recv, send, List.mem_cons, List.not_mem_nil, or_false] at hi
  by_cases ha : q < 32 * hs.length
  · have cq := fun (x : Nat) (hx : x < 73) => cA hok hH hHS hc hq ha hx
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb <;>
      simp only [eval_c, act, hf, cq, Nat.reduceLT, actCell] <;> (repeat' split) <;>
      first | (left; rfl) | (right; rfl)
  · have cq := fun (x : Nat) (hx : x < 73) => cP hok hH hHS hc hq ha hx
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb <;>
      simp only [eval_c, act, hf, cq, Nat.reduceLT] <;> simp

end rows

end HeadLocal

open HeadLocal in
/-- **The honest `headV3` table is locally legal.**  Hypotheses on the trace as for
`uniq_render_local`: `log₂` height `logOf (32·|hs|)`, and cells `Fp.ofNat (HeadGen.cell hs height r x)`
on rows `r < height`, columns `x < HeadV3.width`. -/
theorem head_render_local (hs : List HeadE) (hok : HeadOk hs) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf (32 * hs.length))
    (hcell : ∀ r x, r < tr.height t → x < HeadV3.width →
      tr.cell t r x = Fp.ofNat (HeadGen.cell hs (tr.height t) r x)) :
    TableLocal HeadV3.table tr t pub := by
  have hHS : 32 * hs.length ≤ tr.height t := by
    simp only [Trace.height, hlog]; exact le_pow_logOf _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hlog]; exact one_le_logOf _
  · rw [hlog]; exact logOf_le (by decide) hok.cap
  · intro r hr e he
    exact constr hok rfl hHS hcell hr he
  · intro r hr it hi b hb
    exact multBits hok rfl hHS hcell hr hi hb

namespace HeadTraffic
open HeadGen HeadLocal

/-- First-row messages of head `h` (as naturals). -/
def firstN (h : HeadE) (b : Nat) (sd : Bool) : List ZkFormal.Near.Msg :=
  (if b = B_DIGEST ∧ sd = false then [digMsg (msgId K_NPRE h.rid) h.rlen h.pre] else []) ++
  (if b = B_DIGEST ∧ sd = false then [digMsg (msgId K_NPOST h.rid) h.rlen h.post] else []) ++
  (if b = B_ROOT ∧ sd = false then [[h.tau] ++ h.pre] else []) ++
  (if b = B_MIDROOT ∧ sd = true then [[h.tau, h.rid] ++ h.post] else []) ++
  (if b = B_PARENT ∧ sd = true then [[h.rid, h.tau, 0, h.rlen, h.rres]] else []) ++
  (if b = B_EDGE ∧ sd = true then [startEdgeMsg h 0] else []) ++
  (if b = B_EDGE ∧ sd = false then [startEdgeMsg h h.mE] else [])

def digN (h : HeadE) (j : Nat) : ZkFormal.Near.Msg := [msgId K_NPRE h.rid, h.tau, j, h.pre.getD j 0]

def headMsgs (h : HeadE) (b : Nat) (sd : Bool) : List ZkFormal.Near.Msg :=
  firstN h b sd ++ (if b = B_DIGS ∧ sd = true then (List.range 32).map (digN h) else [])

theorem headMsgs_all (hs : List HeadE) (b : Nat) (sd : Bool) :
    hs.flatMap (fun h => headMsgs h b sd) = if sd then headSends hs b else headRecvs hs b := by
  cases sd
  · simp only [headMsgs, firstN, headRecvs, Bool.false_eq_true, ↓reduceIte, and_false, and_true, false_and,
      List.append_nil]
    by_cases h1 : b = B_DIGEST
    · subst h1; simp [B_DIGEST, B_ROOT, B_EDGE] <;> first | exact ZkFormal.Near.Render.flatMap_single (fun _ _ => rfl) | rfl | (congr 1; funext h; congr 1; funext j; simp [digN, List.getD_eq_getElem?_getD])
    · by_cases h2 : b = B_ROOT
      · subst h2; simp [B_DIGEST, B_ROOT, B_EDGE] <;> first | exact ZkFormal.Near.Render.flatMap_single (fun _ _ => rfl) | rfl | (congr 1; funext h; congr 1; funext j; simp [digN, List.getD_eq_getElem?_getD])
      · by_cases h3 : b = B_EDGE
        · subst h3; simp [B_DIGEST, B_ROOT, B_EDGE] <;> first | exact ZkFormal.Near.Render.flatMap_single (fun _ _ => rfl) | rfl | (congr 1; funext h; congr 1; funext j; simp [digN, List.getD_eq_getElem?_getD])
        · simp [h1, h2, h3]
  · simp only [headMsgs, firstN, headSends, ↓reduceIte, and_false, and_true, false_and, List.append_nil,
      List.nil_append]
    by_cases h1 : b = B_MIDROOT
    · subst h1; simp [B_MIDROOT, B_PARENT, B_EDGE, B_DIGS] <;> first | exact ZkFormal.Near.Render.flatMap_single (fun _ _ => rfl) | rfl | (congr 1; funext h; congr 1; funext j; simp [digN, List.getD_eq_getElem?_getD])
    · by_cases h2 : b = B_PARENT
      · subst h2; simp [B_MIDROOT, B_PARENT, B_EDGE, B_DIGS] <;> first | exact ZkFormal.Near.Render.flatMap_single (fun _ _ => rfl) | rfl | (congr 1; funext h; congr 1; funext j; simp [digN, List.getD_eq_getElem?_getD])
      · by_cases h3 : b = B_EDGE
        · subst h3; simp [B_MIDROOT, B_PARENT, B_EDGE, B_DIGS] <;> first | exact ZkFormal.Near.Render.flatMap_single (fun _ _ => rfl) | rfl | (congr 1; funext h; congr 1; funext j; simp [digN, List.getD_eq_getElem?_getD])
        · by_cases h4 : b = B_DIGS
          · subst h4; simp [B_MIDROOT, B_PARENT, B_EDGE, B_DIGS] <;> first | exact ZkFormal.Near.Render.flatMap_single (fun _ _ => rfl) | rfl | (congr 1; funext h; congr 1; funext j; simp [digN, List.getD_eq_getElem?_getD])
          · simp [h1, h2, h3, h4]

theorem regs_eq (l : List Nat) (hl : l.length = 32) :
    (List.range 32).map (fun j => Fp.ofNat (l.getD (j + 0) 0)) = l.map Fp.ofNat := by
  apply List.ext_getElem (by simp [hl])
  intro n h1 h2
  simp [List.getD_eq_getElem?_getD, show n < l.length by simp at h1; omega]

theorem mid_eq (kk x : Nat) : (kk : Fp) + 16 * Fp.ofNat x = Fp.ofNat (msgId kk x) := by
  unfold msgId; rw [natCast_eq, show (16 : Fp) = Fp.ofNat 16 from rfl, ofNat_mul', ofNat_add']

section rows
variable {hs : List HeadE} (hok : HeadOk hs) {tr : Trace Fp} {tt : Nat} {pub : List Fp} {H : Nat}
  (hH : tr.height tt = H) (hHS : 32 * hs.length ≤ H)
  (hc : ∀ q col, q < H → col < 73 → tr.cell tt q col = Fp.ofNat (HeadGen.cell hs H q col))
include hok hH hHS hc

theorem rowAct {q : Nat} (hq : q < H) (ha : q < 32 * hs.length) (b : Nat) (sd : Bool) :
    rowTraffic HeadV3.interactions tr tt q pub b sd =
      (if q % 32 = 0 then (firstN (hd hs (q / 32)) b sd).map Msg.toFp else []) ++
      (if b = B_DIGS ∧ sd = true then [Msg.toFp (digN (hd hs (q / 32)) (q % 32))] else []) := by
  have cq := fun (x : Nat) (hx : x < 73) => cA hok hH hHS hc hq ha hx
  have hmem : hd hs (q / 32) ∈ hs := by
    simp only [hd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show q / 32 < hs.length by omega),
      Option.getD_some]; exact List.getElem_mem _
  have hlen := hok.wf.len _ hmem
  rw [HeadProof.rowT' q b sd (by rw [cq _ (by decide)]; rfl)
    (by rw [cq _ (by decide)]; simp only [hf, actCell]; split; exact Or.inr rfl; exact Or.inl rfl)]
  congr 1
  · rw [cq _ (by decide)]; simp only [hf, actCell]
    by_cases h0 : q % 32 = 0
    · simp only [h0, if_true, ofNat1]
      have hr : HeadProof.regsAt tr tt q = (hd hs (q / 32)).pre.map Fp.ofNat := by
        rw [← regs_eq _ hlen.1]; simp only [HeadProof.regsAt]
        apply List.map_congr_left; intro j hj
        rw [cq _ (by simp only [reg]; have := List.mem_range.1 hj; omega), cReg hs q (List.mem_range.1 hj), h0]
      have hp : HeadProof.pregsAt tr tt q = (hd hs (q / 32)).post.map Fp.ofNat := by
        rw [← regs_eq _ hlen.2]; simp only [HeadProof.pregsAt]
        apply List.map_congr_left; intro j hj
        rw [cq _ (by simp only [preg]; have := List.mem_range.1 hj; omega), cPreg hs q (List.mem_range.1 hj), h0]
      simp only [HeadProof.firstMsgs, firstN, hr, hp, cq, tau, rid, rlen, rres, mE, Nat.reduceLT, actCell,
        List.map_append, mid_eq]
      have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
        intro a b c d h1 h2; rw [h1, h2]
      refine ap (ap (ap (ap (ap (ap ?_ ?_) ?_) ?_) ?_) ?_) ?_ <;> split <;>
        simp [Msg.toFp, digMsg, startEdgeMsg, natCast_eq] <;> rfl
    · simp only [h0, if_false, ofNat0]
      have : ¬ ((0 : Fp) = 1) := by decide
      simp [this]
  · split
    · simp only [HeadProof.digsMsg, digN, Msg.toFp, List.map_cons, List.map_nil, cq, rid, tau, i, Nat.reduceLT,
        actCell, mid_eq]
      rw [cq _ (by simp only [reg]; omega), cReg hs q (by omega), Nat.zero_add]
    · rfl

theorem rowPad {q : Nat} (hq : q < H) (ha : ¬ q < 32 * hs.length) (b : Nat) (sd : Bool) :
    rowTraffic HeadV3.interactions tr tt q pub b sd = [] := by
  have cq := fun (x : Nat) (hx : x < 73) => cP hok hH hHS hc hq ha hx
  rw [HeadProof.rowT]
  simp [cq, hf, act]

end rows

end HeadTraffic

open HeadTraffic HeadLocal in
/-- **The honest `headV3` table has the traffic of `hs`.**  Same hypotheses as `head_render_local`. -/
theorem head_render_traffic (hs : List HeadE) (hok : HeadOk hs) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf (32 * hs.length))
    (hcell : ∀ r x, r < tr.height t → x < HeadV3.width →
      tr.cell t r x = Fp.ofNat (HeadGen.cell hs (tr.height t) r x)) :
    TableTraffic HeadV3.interactions tr t pub (headTraffic hs) := by
  have hle : 32 * hs.length ≤ tr.height t := by
    simp only [Trace.height, hlog]; exact le_pow_logOf _
  have hall : ∀ sd b, (List.range (tr.height t)).flatMap (fun r => rowTraffic HeadV3.interactions tr t r pub b sd) =
      (if sd then headSends hs b else headRecvs hs b).map Msg.toFp := by
    intro sd b
    rw [range_split hle, List.flatMap_append,
      flatMap_nil' (l := List.map _ _) (fun q hq => by
        obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        exact rowPad hok rfl hle hcell (by have := List.mem_range.1 hq'; omega) (by omega) b sd),
      List.append_nil, range_flatMap_chunks 32, ← headMsgs_all, List.map_flatMap,
      flatMap_getD default hs]
    apply ZkFormal.Near.Render.flatMap_congr'
    intro t' ht'
    have ht := List.mem_range.1 ht'
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      rowAct hok rfl hle hcell (by omega) (by omega),
      ZkFormal.Near.Render.flatMap_congr' (g := fun j =>
        if b = B_DIGS ∧ sd = true then [Msg.toFp (digN (HeadGen.hd hs t') (j + 1))] else []) (fun j hj => by
          have := List.mem_range.1 hj
          rw [rowAct hok rfl hle hcell (by omega) (by omega), if_neg (by omega),
            show (32 * t' + (j + 1)) / 32 = t' by omega, show (32 * t' + (j + 1)) % 32 = j + 1 by omega]; rfl)]
    simp only [show 32 * t' + 0 = 32 * t' by omega, show 32 * t' % 32 = 0 by omega, show 32 * t' / 32 = t' by omega,
      if_true, headMsgs, List.map_append, HeadGen.hd, List.append_assoc]
    congr 1
    split
    · rw [List.range_succ_eq_map (n := 31), List.map_cons, List.map_map, List.map_cons, List.map_map]
      simp only [List.singleton_append, List.cons.injEq, true_and]
      rw [flatMap_single (g := fun j => Msg.toFp (digN (hs.getD t' default) (j + 1))) (fun j _ => by simp)]
      rfl
    · simp
  apply traffic_of
  · intro b; rw [hall true b]; exact List.Perm.refl _
  · intro b; rw [hall false b]; exact List.Perm.refl _

end ZkFormal.NearV3.Render
