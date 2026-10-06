import ZkFormal.NearV3.Rcpt.Extract.AkeyProof
import ZkFormal.Near.Render.Proof.Base

/-!
# ZkFormal.NearV3.Rcpt.Render.AkeyRender — completeness of the `akeyV3` table

Honest rows (`akeyRows es`): record `es[s]` on rows `9s … 9s+8` (lane `p`: `act = 1`,
`af = [p = 0]`, `al = [p = 8]`, `vid`, `pos = p`, `b = bytes[p]`, `uu = U`), then zero padding to
`2^logOf (9·|es|)` rows.  Given `AkeyOk es` (last byte `1`, `9·|es| ≤ 2^16`):
* `akey_render_local`: `TableLocal AkeyV3.table`;
* `akey_render_traffic`: traffic `akeyTraffic es` (no hypothesis needed).
-/

namespace ZkFormal.NearV3.Render

open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

structure AkeyOk (es : List AkeyE) : Prop where
  last : ∀ e ∈ es, e.bytes.getD 8 0 = 1
  rows : 9 * es.length ≤ 2 ^ AkeyV3.maxLog

namespace AkeyGen

def actCell (e : AkeyE) (p : Nat) : Nat → Nat
  | 0 => 1
  | 1 => if p = 0 then 1 else 0
  | 2 => if p = 8 then 1 else 0
  | 3 => e.vid
  | 4 => p
  | 5 => e.bytes.getD p 0
  | 6 => e.U
  | _ => 0

def cell (es : List AkeyE) (q col : Nat) : Nat :=
  if q < 9 * es.length then actCell (es.getD (q / 9) default) (q % 9) col else 0

end AkeyGen

/-- The honest `akeyV3` rows. -/
def akeyRows (es : List AkeyE) : Array Row :=
  mkTab (2 ^ logOf (9 * es.length)) AkeyV3.width (AkeyGen.cell es)

namespace AkeyRender

theorem ofNat0 : Fp.ofNat 0 = 0 := rfl
theorem ofNat1 : Fp.ofNat 1 = 1 := rfl
theorem ofNat8 : Fp.ofNat 8 = 8 := rfl
theorem ofNatAdd (a b : Nat) : Fp.ofNat (a + b) = Fp.ofNat a + Fp.ofNat b := (ofNat_add' a b).symm
theorem ofNat_mod (x : Nat) : Fp.ofNat (x % ZkFormal.Algebra.P) = Fp.ofNat x :=
  Fp.ext (by rw [Fp.toNat_ofNat, Fp.toNat_ofNat, Nat.mod_mod])

section rows
variable {es : List AkeyE} {tr : Trace Fp} {tt : Nat} {H : Nat}
  (hH : tr.height tt = H) (hHS : 9 * es.length ≤ H)
  (hc : ∀ q x, q < H → x < AkeyV3.width → tr.cell tt q x = Fp.ofNat (AkeyGen.cell es q x))
include hH hHS hc

theorem cA {q : Nat} (hq : q < 9 * es.length) {x : Nat} (hx : x < 7) :
    tr.cell tt q x = Fp.ofNat (AkeyGen.actCell (es.getD (q / 9) default) (q % 9) x) := by
  rw [hc q x (by omega) hx]; simp [AkeyGen.cell, hq]

theorem cP {q : Nat} (hqH : q < H) (hq : ¬ q < 9 * es.length) {x : Nat} (hx : x < 7) : tr.cell tt q x = 0 := by
  rw [hc q x hqH hx]; simp [AkeyGen.cell, hq]; rfl

end rows

end AkeyRender

/-- Close a field goal after normalising small `Fp.ofNat` literals. -/
local macro "akfin" : tactic => `(tactic| ((try simp only [AkeyRender.ofNat0, AkeyRender.ofNat1,
  AkeyRender.ofNat8] at *) <;> grind))

open AkeyRender in
/-- **The honest `akeyV3` table is locally legal.** -/
theorem akey_render_local (es : List AkeyE) (ok : AkeyOk es) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf (9 * es.length))
    (hcell : ∀ r x, r < tr.height t → x < AkeyV3.width → tr.cell t r x = Fp.ofNat (AkeyGen.cell es r x)) :
    TableLocal AkeyV3.table tr t pub := by
  have hHS : 9 * es.length ≤ tr.height t := by simp only [Trace.height, hlog]; exact le_pow_logOf _
  have hH2 : 2 ≤ tr.height t := by
    simp only [Trace.height, hlog]
    have := one_le_logOf (9 * es.length)
    calc 2 = 2 ^ 1 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by omega) this
  have cA' := fun {q} (hq : q < 9 * es.length) {x} (hx : x < 7) => cA rfl hHS hcell hq hx
  have cP' := fun {q} (hqH : q < tr.height t) (hq : ¬ q < 9 * es.length) {x} (hx : x < 7) =>
    cP rfl hHS hcell hqH hq hx
  -- active rows: the flags
  have actv : ∀ q, q < 9 * es.length → tr.cell t q AkeyV3.act = 1 := fun q hq => cA' hq (by decide)
  have padv : ∀ q, q < tr.height t → ¬ q < 9 * es.length → ∀ x, x < 7 → tr.cell t q x = 0 :=
    fun q hq h x hx => cP' hq h hx
  have bool01 : ∀ q, q < tr.height t → ∀ x ∈ [AkeyV3.act, AkeyV3.af, AkeyV3.al],
      tr.cell t q x = 0 ∨ tr.cell t q x = 1 := by
    intro q hq x hx
    simp only [AkeyV3.act, AkeyV3.af, AkeyV3.al, List.mem_cons, List.not_mem_nil, or_false] at hx
    by_cases ha : q < 9 * es.length
    · rcases hx with rfl | rfl | rfl <;> rw [cA' ha (by decide)] <;> simp only [AkeyGen.actCell] <;>
        (try split) <;> simp [ofNat0, ofNat1]
    · left; exact padv q hq ha x (by rcases hx with rfl | rfl | rfl <;> decide)
  refine ⟨by rw [hlog]; exact one_le_logOf _, by rw [hlog]; exact logOf_le (by decide) ok.rows, ?_, ?_⟩
  · intro r hr e he
    unfold AkeyV3.table AkeyV3.constraints at he
    rcases List.mem_append.1 he with he' | he'
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he'
      simp only [eval_bool, eval_c]
      rcases bool01 r hr y hy with h | h <;> rw [h] <;> akfin
    · clear he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he'
      have ent_mem : es.getD (r / 9) default ∈ es → (es.getD (r / 9) default).bytes.getD 8 0 = 1 := ok.last _
      rcases he' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      -- af ⇒ act, al ⇒ act
      · simp only [eval_mul, eval_c, eval_not]
        by_cases ha : r < 9 * es.length
        · rw [actv r ha]; akfin
        · rw [padv r hr ha _ (by decide)]; akfin
      · simp only [eval_mul, eval_c, eval_not]
        by_cases ha : r < 9 * es.length
        · rw [actv r ha]; akfin
        · rw [padv r hr ha _ (by decide)]; akfin
      -- isFirst ⇒ act = af
      · simp only [eval_mul, eval_c, eval_sub, eval_isFirst]
        by_cases h0 : r = 0
        · subst h0
          by_cases ha : 0 < 9 * es.length
          · rw [cA' ha (x := AkeyV3.act) (by decide), cA' ha (x := AkeyV3.af) (by decide)]
            simp only [AkeyGen.actCell, AkeyV3.act, AkeyV3.af, Nat.zero_mod, if_true]; akfin
          · rw [padv 0 hr ha _ (by decide), padv 0 hr ha _ (by decide)]; akfin
        · rw [if_neg h0]; akfin
      -- isLast ⇒ act → al
      · simp only [eval_mul, eval_c, eval_not, eval_isLast]
        by_cases hl : r + 1 = tr.height t
        · by_cases ha : r < 9 * es.length
          · rw [actv r ha, cA' ha (x := AkeyV3.al) (by decide)]
            simp only [AkeyGen.actCell, AkeyV3.al, if_pos (show r % 9 = 8 by omega), ofNat1]; akfin
          · rw [padv r hr ha AkeyV3.act (by decide)]; akfin
        · rw [if_neg hl]; akfin
      -- af ⇒ pos = 0; al ⇒ pos = 8; al ⇒ b = 1
      · simp only [eval_mul, eval_c]
        by_cases ha : r < 9 * es.length
        · rw [cA' ha (x := AkeyV3.af) (by decide), cA' ha (x := AkeyV3.pos) (by decide)]
          simp only [AkeyGen.actCell, AkeyV3.af, AkeyV3.pos]
          split
          · rename_i h; rw [h]; akfin
          · rw [ofNat0]; akfin
        · rw [padv r hr ha AkeyV3.af (by decide)]; akfin
      · simp only [eval_mul, eval_c, eval_sub, eval_k]
        by_cases ha : r < 9 * es.length
        · rw [cA' ha (x := AkeyV3.al) (by decide), cA' ha (x := AkeyV3.pos) (by decide)]
          simp only [AkeyGen.actCell, AkeyV3.al, AkeyV3.pos]
          split
          · rename_i h; rw [h, natCast_eq, ofNat8]; akfin
          · rw [ofNat0]; akfin
        · rw [padv r hr ha AkeyV3.al (by decide)]; akfin
      · simp only [eval_mul, eval_c, eval_sub, eval_k]
        by_cases ha : r < 9 * es.length
        · rw [cA' ha (x := AkeyV3.al) (by decide), cA' ha (x := AkeyV3.b) (by decide)]
          simp only [AkeyGen.actCell, AkeyV3.al, AkeyV3.b]
          split
          · rename_i h
            rw [h, ent_mem (by
              simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show r / 9 < es.length by omega),
                Option.getD_some]
              exact List.getElem_mem _), natCast_eq]; akfin
          · rw [ofNat0]; akfin
        · rw [padv r hr ha AkeyV3.al (by decide)]; akfin
      -- within a segment (gate act·(1 − al))
      · simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k]
        by_cases ha : r < 9 * es.length
        · by_cases h8 : r % 9 = 8
          · rw [cA' ha (x := AkeyV3.al) (by decide)]
            simp only [AkeyGen.actCell, AkeyV3.al, if_pos h8]; akfin
          · have h1 : r + 1 < 9 * es.length := by omega
            have hmod : (r + 1) % tr.height t = r + 1 := Nat.mod_eq_of_lt (by omega)
            rw [hmod, cA' h1 (x := AkeyV3.act) (by decide), cA' ha (x := AkeyV3.act) (by decide),
              cA' ha (x := AkeyV3.al) (by decide)]
            simp only [AkeyGen.actCell, AkeyV3.act, AkeyV3.al, if_neg h8]; akfin
        · rw [padv r hr ha AkeyV3.act (by decide)]; akfin
      · simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k]
        by_cases ha : r < 9 * es.length
        · by_cases h8 : r % 9 = 8
          · rw [cA' ha (x := AkeyV3.al) (by decide)]
            simp only [AkeyGen.actCell, AkeyV3.al, if_pos h8]; akfin
          · have h1 : r + 1 < 9 * es.length := by omega
            have hmod : (r + 1) % tr.height t = r + 1 := Nat.mod_eq_of_lt (by omega)
            rw [hmod, cA' ha (x := AkeyV3.act) (by decide), cA' ha (x := AkeyV3.al) (by decide)]
            simp only [AkeyGen.actCell, AkeyV3.act, AkeyV3.al, if_neg h8]
            rw [cA' h1 (x := AkeyV3.af) (by decide)]
            simp only [AkeyGen.actCell, AkeyV3.af, if_neg (show ¬ (r + 1) % 9 = 0 by omega)]; akfin
        · rw [padv r hr ha AkeyV3.act (by decide)]; akfin
      · simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k]
        by_cases ha : r < 9 * es.length
        · by_cases h8 : r % 9 = 8
          · rw [cA' ha (x := AkeyV3.al) (by decide)]
            simp only [AkeyGen.actCell, AkeyV3.al, if_pos h8]; akfin
          · have h1 : r + 1 < 9 * es.length := by omega
            have hmod : (r + 1) % tr.height t = r + 1 := Nat.mod_eq_of_lt (by omega)
            rw [hmod, cA' ha (x := AkeyV3.act) (by decide), cA' ha (x := AkeyV3.al) (by decide)]
            simp only [AkeyGen.actCell, AkeyV3.act, AkeyV3.al, if_neg h8]
            rw [cA' h1 (x := AkeyV3.vid) (by decide), cA' ha (x := AkeyV3.vid) (by decide)]
            simp only [AkeyGen.actCell, AkeyV3.vid, show (r + 1) / 9 = r / 9 by omega]; akfin
        · rw [padv r hr ha AkeyV3.act (by decide)]; akfin
      · simp only [eval_mul3, eval_c, eval_not, eval_n, eval_sub, eval_add, eval_k]
        by_cases ha : r < 9 * es.length
        · by_cases h8 : r % 9 = 8
          · rw [cA' ha (x := AkeyV3.al) (by decide)]
            simp only [AkeyGen.actCell, AkeyV3.al, if_pos h8]; akfin
          · have h1 : r + 1 < 9 * es.length := by omega
            have hmod : (r + 1) % tr.height t = r + 1 := Nat.mod_eq_of_lt (by omega)
            rw [hmod, cA' ha (x := AkeyV3.act) (by decide), cA' ha (x := AkeyV3.al) (by decide)]
            simp only [AkeyGen.actCell, AkeyV3.act, AkeyV3.al, if_neg h8]
            rw [cA' h1 (x := AkeyV3.pos) (by decide), cA' ha (x := AkeyV3.pos) (by decide)]
            simp only [AkeyGen.actCell, AkeyV3.pos, show (r + 1) % 9 = r % 9 + 1 by omega, ofNatAdd]
            akfin
        · rw [padv r hr ha AkeyV3.act (by decide)]; akfin
      · simp only [eval_mul3, eval_c, eval_not, eval_n]
        by_cases ha : r < 9 * es.length
        · by_cases h8 : r % 9 = 8
          · by_cases hl : r + 1 = tr.height t
            · rw [hl, Nat.mod_self]
              by_cases h0 : 0 < 9 * es.length
              · rw [cA' h0 (x := AkeyV3.af) (by decide)]
                simp only [AkeyGen.actCell, AkeyV3.af, Nat.zero_mod, if_true]; akfin
              · rw [padv 0 (by omega) h0 AkeyV3.act (by decide)]; akfin
            · rw [Nat.mod_eq_of_lt (by omega)]
              by_cases h1 : r + 1 < 9 * es.length
              · rw [cA' h1 (x := AkeyV3.af) (by decide)]
                simp only [AkeyGen.actCell, AkeyV3.af, show (r + 1) % 9 = 0 by omega, if_true]; akfin
              · rw [padv (r + 1) (by omega) h1 AkeyV3.act (by decide)]; akfin
          · rw [cA' ha (x := AkeyV3.al) (by decide)]
            simp only [AkeyGen.actCell, AkeyV3.al, if_neg h8, ofNat0]; akfin
        · rw [padv r hr ha AkeyV3.al (by decide)]; akfin
      · simp only [eval_mul3, eval_c, eval_not, eval_n, eval_isTransition]
        by_cases hl : r + 1 = tr.height t
        · rw [if_pos hl]; akfin
        · rw [if_neg hl, Nat.mod_eq_of_lt (by omega)]
          by_cases ha : r < 9 * es.length
          · rw [actv r ha]; akfin
          · rw [padv (r + 1) (by omega) (by omega) AkeyV3.act (by decide)]; akfin
  · intro r hr it hi bb hb
    simp only [AkeyV3.table, AkeyV3.interactions, Dsl.send, Dsl.recv, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      simp only [eval_c]
      exact bool01 r hr _ (by simp)

open AkeyRender in
/-- **The honest `akeyV3` table has the traffic of `es`.** -/
theorem akey_render_traffic (es : List AkeyE) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hlog : tr.log t = logOf (9 * es.length))
    (hcell : ∀ r x, r < tr.height t → x < AkeyV3.width → tr.cell t r x = Fp.ofNat (AkeyGen.cell es r x)) :
    TableTraffic AkeyV3.interactions tr t pub (akeyTraffic es) := by
  have hHS : 9 * es.length ≤ tr.height t := by simp only [Trace.height, hlog]; exact le_pow_logOf _
  have cA' := fun {q} (hq : q < 9 * es.length) {x} (hx : x < 7) => cA rfl hHS hcell hq hx
  have cP' := fun {q} (hqH : q < tr.height t) (hq : ¬ q < 9 * es.length) {x} (hx : x < 7) =>
    cP rfl hHS hcell hqH hq hx
  -- messages of the record rows, in order
  have hrow : ∀ b sd q, q < 9 * es.length → rowTraffic AkeyV3.interactions tr t q pub b sd =
      (((if sd then akeySends [es.getD (q / 9) default] b else akeyRecvs [es.getD (q / 9) default] b).drop
        (if b = B_VBYTES ∧ sd = true then q % 9 else 0)).take
        (if b = B_VBYTES ∧ sd = true then 1 else if q % 9 = 0 then 1 else 0)).map Msg.toFp := by
    intro b sd q hq
    rw [AkeyProof.rowT]
    simp only [cA' hq (x := AkeyV3.act) (by decide), cA' hq (x := AkeyV3.af) (by decide),
      cA' hq (x := AkeyV3.vid) (by decide), cA' hq (x := AkeyV3.pos) (by decide),
      cA' hq (x := AkeyV3.b) (by decide), cA' hq (x := AkeyV3.uu) (by decide)]
    simp only [AkeyGen.actCell, AkeyV3.act, AkeyV3.af, AkeyV3.vid, AkeyV3.pos, AkeyV3.b, AkeyV3.uu, ofNat1]
    have hp : q % 9 < 9 := Nat.mod_lt _ (by decide)
    by_cases hV : b = B_VBYTES
    · subst hV
      cases sd
      · simp [akeyRecvs, B_VBYTES, B_AKC]
      · simp only [akeySends, if_true, true_and, and_self, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, if_pos rfl, show B_VBYTES ≠ B_AKC by decide, false_and, if_false]
        rw [List.drop_eq_getElem_cons (by simp; omega)]
        simp [Msg.toFp, List.getElem_range]
    · by_cases hK : b = B_AKC
      · subst hK
        by_cases h0 : q % 9 = 0
        · cases sd <;> simp [akeySends, akeyRecvs, h0, Msg.toFp, B_AKC, B_VBYTES, ofNat0, ofNat1]
        · cases sd <;> simp [akeySends, akeyRecvs, h0, B_AKC, B_VBYTES, ofNat0]
      · cases sd <;> simp [akeySends, akeyRecvs, hV, hK]
  -- per record
  have hrec : ∀ b sd s, s < es.length →
      (List.range 9).flatMap (fun p => rowTraffic AkeyV3.interactions tr t (9 * s + p) pub b sd) =
      (if sd then akeySends [es.getD s default] b else akeyRecvs [es.getD s default] b).map Msg.toFp := by
    intro b sd s hs
    rw [Render.flatMap_congr' (fun p hp => hrow b sd (9 * s + p) (by have := List.mem_range.1 hp; omega))]
    have e1 : ∀ p, p < 9 → (9 * s + p) / 9 = s := fun p hp => by omega
    have e2 : ∀ p, p < 9 → (9 * s + p) % 9 = p := fun p hp => by omega
    rw [Render.flatMap_congr' (fun p hp => by rw [e1 p (List.mem_range.1 hp), e2 p (List.mem_range.1 hp)])]
    by_cases hV : b = B_VBYTES ∧ sd = true
    · obtain ⟨rfl, rfl⟩ := hV
      simp only [true_and, if_true, and_self]
      rw [← List.map_flatMap]
      congr 1
      try simp only [akeySends, if_true, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      try simp [show List.range 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from rfl]
    · simp only [if_neg hV]
      rw [show List.range 9 = [0] ++ List.range' 1 8 from rfl, List.flatMap_append,
        Render.flatMap_nil' (l := List.range' 1 8) (fun p hp => by
          have := List.mem_range'.1 hp
          simp [show p ≠ 0 by omega]),
        List.append_nil, List.flatMap_singleton]
      simp only [if_true, List.drop_zero]
      cases sd
      · simp only [akeyRecvs, Bool.false_eq_true, if_false]; split <;> simp
      · have hb : b ≠ B_VBYTES := fun h => hV ⟨h, rfl⟩
        simp only [akeySends, if_true, hb, if_false]; split <;> simp
  apply traffic_of
  all_goals
    intro b
    refine List.Perm.of_eq ?_
    rw [range_split hHS, List.flatMap_append,
      Render.flatMap_nil' (l := List.map _ _) (fun q hq => by
        obtain ⟨q', hq'', rfl⟩ := List.mem_map.1 hq
        have hq3 := List.mem_range.1 hq''
        rw [AkeyProof.rowT]
        have hq' : ¬ 9 * es.length + q' < 9 * es.length := by omega
        rw [cP' (by omega) hq' (x := AkeyV3.act) (by decide), cP' (by omega) hq' (x := AkeyV3.af) (by decide)]
        simp),
      List.append_nil, range_flatMap_chunks,
      Render.flatMap_congr' (fun s hs => hrec b _ s (List.mem_range.1 hs)), ← List.map_flatMap]
  · simp only [↓reduceIte]
    rw [← flatMap_getD default es (fun e => akeySends [e] b), ← AkeyProof.akeySends_flat]; rfl
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← flatMap_getD default es (fun e => akeyRecvs [e] b), ← AkeyProof.akeyRecvs_flat]; rfl

end ZkFormal.NearV3.Render
