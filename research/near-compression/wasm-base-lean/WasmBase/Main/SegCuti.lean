import WasmBase.Main.SegIface

/-!
# WasmBase.Main.SegCuti — the in-boundary of a segment: CUTI's digest and productions (E2E M4c, CUTI)

CUTI (table 30 of `wasmBaseSegAir`) produces the small-state messages of the in-boundary at
`tp = t_in` and hashes them; it has **no range or order checks** (`SegAir.lean` header): its rows are
pinned only through the digest.  This file decodes CUTI as a function of the hashed words and
closes the CUTI side of `seg_sound`'s in-boundary premises.

1. **`cuti_stream`** (the CUTI analogue of `ctx_out_sha`): under `HoldsX` + `ChipIf compressW`, CUTI
   has `2N` data rows, row `r` hashes the 8 words `B[r]` (`streamW`, all `< 2^64`), the public `ctx_in`
   limbs are those of `d` with `wbytes d = sha384 (wbytes B.flatten)`, and CUTI's CH productions are
   exactly `ofFields (decFs b) t_in` for the blocks `b ∈ B` whose mark (`b[0] / 2^42`) is 1, in row
   order.  The decoding `decF w = w mod 2^21 + 2^16·((w / 2^21) mod 2^21)` is a function of the word:
   the chip contract puts each limb below `2^21`, and a data row's limbs are `act·lo`, `act·hi`,
   `act` (word 0) — so `act` is the mark and, on an active row, `lo + 2^16·hi = decF w`.
2. **`cuti_view`**: if the public `ctx_in` is `cutDigest L` (`PubDigIs`) for a list `L` of `MsgWF`
   messages, then either SHA-384 collides (`Sha384Coll`) or CUTI's productions are exactly
   `L.map (ofFields · t_in)` (as a list: one production per entry).  `cutDigest` hashes
   `cutWords L = L.flatMap msgWords ++ filler`; equal 8-word blocks give `B = L.map msgWords ++ filler`;
   the filler has mark 0 and `decFs (msgWords y) = y` (`decF_cutWord`).
3. **`initS_nodup`**: `(initS tr pub).Nodup` from item 2 with `L = cutView X s`, `RegWF s`
   (`cutView_nodup`), MEMB's distinct byte addresses (`memb_slots_nodup`) and SEGB's single gas
   message; the three parts are in disjoint spaces (view: never 3 or 7; MEMB: 3; SEGB: 7).
-/

namespace WasmBase
namespace Cuti

open ZkFormal.Algebra Chips Seg SegSha
open NearSpecV3.Wasm hiding P
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. Decoding a CUT word -/

/-- A CUT word's message field: `lo + 2^16·hi` (as a field element, read back as a natural) with
`lo`, `hi` its first two chip limbs. -/
def decF (w : Nat) : Nat := (w % 2 ^ 21 + 65536 * (w / 2 ^ 21 % 2 ^ 21)) % P

/-- The 7 message fields of an 8-word block. -/
def decFs (b : List Nat) : List Nat := (b.take 7).map decF

/-- The mark of an 8-word block (word 0's top limb): 1 on a real message, 0 on the filler. -/
def markOf (b : List Nat) : Nat := b.getD 0 0 / 2 ^ 42

theorem decF_cutWord {f mk : Nat} (hf : f < 2 ^ 30) (_hm : mk ≤ 1) : decF (cutWord f mk) = f := by
  have hP := P_val
  unfold decF cutWord
  rw [show (f % 2 ^ 16 + 2 ^ 21 * (f / 2 ^ 16) + 2 ^ 42 * mk) % 2 ^ 21 +
      65536 * ((f % 2 ^ 16 + 2 ^ 21 * (f / 2 ^ 16) + 2 ^ 42 * mk) / 2 ^ 21 % 2 ^ 21) = f by omega]
  exact Nat.mod_eq_of_lt (by omega)

theorem markOf_msgWords {y : List Nat} (hy : MsgWF y) : markOf (msgWords y) = 1 := by
  obtain ⟨hl, hf⟩ := hy
  match y, hl with
  | f :: fs, _ =>
    have := hf f List.mem_cons_self
    simp only [markOf, msgWords, List.cons_append, List.getD_cons_zero, cutWord]
    omega

theorem decFs_msgWords {y : List Nat} (hy : MsgWF y) : decFs (msgWords y) = y := by
  obtain ⟨hl, hf⟩ := hy
  match y, hl with
  | f :: fs, hl =>
    have h6 : fs.length = 6 := by simpa using hl
    simp only [decFs, msgWords, List.cons_append, List.take_succ_cons, List.map_cons]
    rw [List.take_left' (by simp [h6]), decF_cutWord (hf f List.mem_cons_self) (by decide), List.map_map]
    congr 1
    have e : ∀ g ∈ fs, (decF ∘ fun x => cutWord x 0) g = id g :=
      fun g hg => decF_cutWord (hf g (List.mem_cons_of_mem _ hg)) (by decide)
    rw [List.map_congr_left e, List.map_id]

theorem msgWords_w64 {y : List Nat} (hy : MsgWF y) : StateM5a.Sha512If.W64 (msgWords y) := by
  obtain ⟨hl, hf⟩ := hy
  match y, hl with
  | f :: fs, _ =>
    intro w hw
    simp only [msgWords, List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with rfl | ⟨g, hg, rfl⟩ | h
    · exact cutWord_lt (hf f List.mem_cons_self) (by decide)
    · exact cutWord_lt (hf g (List.mem_cons_of_mem _ hg)) (by decide)
    · simp at h; subst h; decide

/-! ## 2. CUTI's productions as rows -/

/-- Field `k` of CUTI row `r` (`lo_k + 2^16·hi_k`, as a natural). -/
def cutiF (tr : Trace) (r k : Nat) : Nat := (kc tr 30 r (5 + k) + ((65536 : Nat) : F) * kc tr 30 r (12 + k)).toNat

def cutiRow (tr : Trace) (r : Nat) : List Nat := (List.range 7).map (cutiF tr r)

theorem cuti_send_filter : Cut.In.table.inters.filter (fun i => i.bus = busStk ∧ i.send = true) =
    [chSend (Cut.F Cut.In.cols 0) (Cut.F Cut.In.cols 1) (Cut.F Cut.In.cols 2)
      [Cut.F Cut.In.cols 3, Cut.F Cut.In.cols 4, Cut.F Cut.In.cols 5, Cut.F Cut.In.cols 6] (pv pubTIn)
      (Cut.In.c "act")] := by
  decide +kernel

theorem cuti_ix_lo : ∀ k, k < 7 → ix Cut.In.cols s!"lo{k}" = 5 + k ∧ ix Cut.In.cols s!"hi{k}" = 12 + k := by decide

theorem cutiRow_eq (tr : Trace) (r : Nat) :
    cutiRow tr r = [cutiF tr r 0, cutiF tr r 1, cutiF tr r 2, cutiF tr r 3, cutiF tr r 4, cutiF tr r 5,
      cutiF tr r 6] := by
  simp [cutiRow, List.range_succ]

theorem cuti_evalF (tr : Trace) (pub : List F) (r : Nat) {k : Nat} (hk : k < 7) :
    (Cut.F Cut.In.cols k).eval (tr.row pub 30 r) = kc tr 30 r (5 + k) + ((65536 : Nat) : F) * kc tr 30 r (12 + k) := by
  simp only [Cut.F, Cut.c, (cuti_ix_lo k hk).1, (cuti_ix_lo k hk).2, v, Expr.eval_add', Expr.eval_mul',
    Expr.eval_col, Expr.eval_ofNat']
  rfl

/-- **CUTI's productions, row by row**: the active rows (`act = 1`) in row order, each producing its
7 fields at `t_in`. -/
theorem cuti_part (tr : Trace) (pub : List F) :
    (part Cut.In.table tr pub 30 busStk true).map decMsg =
      ((List.range (tr.height 30)).filter (fun r => rowNat tr 30 r 0 = 1)).map
        (fun r => ofFields (cutiRow tr r) (pub.getD pubTIn 0).toNat) := by
  unfold part
  have hact : ∀ r, ((Cut.In.c "act").eval (tr.row pub 30 r)).toNat = rowNat tr 30 r 0 := by
    intro r
    have : ix Cut.In.cols "act" = 0 := by decide
    simp only [Cut.In.c, Cut.c, this, v, Expr.eval, Trace.row, rowNat]
  rw [show (fun r => rowMsgs Cut.In.table tr pub 30 r busStk true) = fun r =>
      if rowNat tr 30 r 0 = 1 then [(chSend (Cut.F Cut.In.cols 0) (Cut.F Cut.In.cols 1) (Cut.F Cut.In.cols 2)
        [Cut.F Cut.In.cols 3, Cut.F Cut.In.cols 4, Cut.F Cut.In.cols 5, Cut.F Cut.In.cols 6] (pv pubTIn)
        (Cut.In.c "act")).msg.map (·.eval (tr.row pub 30 r))] else [] from
    funext fun r => by
      have e : (chSend (Cut.F Cut.In.cols 0) (Cut.F Cut.In.cols 1) (Cut.F Cut.In.cols 2)
        [Cut.F Cut.In.cols 3, Cut.F Cut.In.cols 4, Cut.F Cut.In.cols 5, Cut.F Cut.In.cols 6] (pv pubTIn)
        (Cut.In.c "act")).count = Cut.In.c "act" := rfl
      rw [rowMsgs_one cuti_send_filter, e, hact]]
  rw [flatMap_ite_single, List.map_map]
  apply List.map_congr_left
  intro r _
  simp only [Function.comp, chSend, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    cuti_evalF tr pub r (show 0 < 7 by omega), cuti_evalF tr pub r (show 1 < 7 by omega),
    cuti_evalF tr pub r (show 2 < 7 by omega), cuti_evalF tr pub r (show 3 < 7 by omega),
    cuti_evalF tr pub r (show 4 < 7 by omega), cuti_evalF tr pub r (show 5 < 7 by omega),
    cuti_evalF tr pub r (show 6 < 7 by omega), cutiRow_eq, decMsg, ofFields, List.getD_cons_zero,
    List.getD_cons_succ, pv, Expr.eval_pub]
  rfl

/-! ## 3. The CUTI stream -/

theorem streamW_getD (tr : Trace) (pub : List F) (t : Nat) (cs : List String) (r : Nat) {w : Nat} (hw : w < 8) :
    (streamW tr pub t cs r).getD w 0 = decW (bwF tr pub t cs r w) := by
  simp [streamW, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw]

theorem streamW_length (tr : Trace) (pub : List F) (t : Nat) (cs : List String) (r : Nat) :
    (streamW tr pub t cs r).length = 8 := by simp [streamW]

theorem f_one_ne_zero : (1 : F) ≠ 0 := by decide

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
  {chip : List StateM5a.Sha512If.IfMsg} (hC : ChipIf compressW (wasmBaseSegAir nloc ngl) pub tr chip)

omit H in
theorem cuti_hT : (30 = 30 ∧ Cut.In.cols = Cut.In.cols ∧ pubCtxIn = pubCtxIn) ∨
    (30 = 31 ∧ Cut.In.cols = Cut.Out.cols ∧ pubCtxIn = pubCtxOut) := Or.inl ⟨rfl, rfl, rfl⟩

include H in
theorem cuti_C : ∀ r, r < tr.height 30 → ∀ e ∈ Cut.streamConstraints Cut.In.cols pubCtxIn,
    e.eval (tr.row pub 30 r) = 0 := cutT_C H cuti_hT

include H in
/-- On a CUTI row with `kD = 0`, `act = 0`; with `kP = 1`, `kD = 0`. -/
theorem cuti_bits {r : Nat} (hr : r < tr.height 30) :
    (kc tr 30 r 0 = 0 ∨ kc tr 30 r 0 = 1) ∧ (kc tr 30 r 3 = 1 → kc tr 30 r 2 = 0) ∧
      (kc tr 30 r 4 = 1 → kc tr 30 r 2 = 0) ∧ (kc tr 30 r 2 = 1 → kc tr 30 r 3 = 0) ∧
      (kc tr 30 r 2 = 0 → kc tr 30 r 0 = 0) := by
  obtain ⟨ha, -, k, h0⟩ := cut_bits (Or.inl rfl) (cuti_C H) (r := r) hr
  refine ⟨ha, fun h => ?_, fun h => ?_, fun h => ?_, h0⟩ <;>
    rcases k with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> first | assumption |
      (exfalso; first | (rw [h] at a; first | exact f_one_ne_zero a | exact f_one_ne_zero a.symm) |
        (rw [h] at b; first | exact f_one_ne_zero b | exact f_one_ne_zero b.symm) |
        (rw [h] at c; first | exact f_one_ne_zero c | exact f_one_ne_zero c.symm))

include H hC in
/-- **The words of a CUTI data row are chip words**: each of its 8 limb triples is `wF` of the decoded
word, which is `< 2^64`. -/
theorem cuti_data_wF {N : Nat} (hN : 2 * N + 2 ≤ tr.height 30) (hd : ∀ r, r < 2 * N → kc tr 30 r 2 = 1)
    (hp : kc tr 30 (2 * N) 3 = 1) :
    ∀ r, r < 2 * N → ∀ w, w < 8 →
      bwF tr pub 30 Cut.In.cols r w = wF ((streamW tr pub 30 Cut.In.cols r).getD w 0) ∧
        (streamW tr pub 30 Cut.In.cols r).getD w 0 < 2 ^ 64 := by
  have hcs : Cut.In.cols = Cut.In.cols ∨ Cut.In.cols = Cut.Out.cols := Or.inl rfl
  have hC' := cuti_C H
  have ht := cutT_lt (nloc := nloc) (ngl := ngl) cuti_hT
  have hh : 4 ≤ tr.height 30 := H.heightPos 30 ht
  obtain ⟨N', hN', hd', hp0', -, rows, hcid, -⟩ := cut_rows hcs hC' hh
  have eN : N = N' := by
    rcases Nat.lt_trichotomy N N' with h | h | h
    · exfalso
      have := (cuti_bits H (r := 2 * N) (by omega)).2.2.2.1 (hd' (2 * N) (by omega))
      rw [hp] at this; exact f_one_ne_zero this
    · exact h
    · exfalso
      have := (cuti_bits H (r := 2 * N') (by omega)).2.2.2.1 (hd (2 * N') (by omega))
      rw [hp0'] at this; exact f_one_ne_zero this
  subst eN
  have cnt : ∀ r, r < 2 * N → kc tr 30 r 2 + kc tr 30 r 3 = 1 := by
    intro r hr
    rw [hd r hr, (cuti_bits H (r := r) (by omega)).2.2.2.1 (hd r hr)]; grind
  intro r hr w hw
  have hg : r / 2 < N := by omega
  have j0 : kc tr 30 (2 * (r / 2)) 1 = 0 := by
    rw [(rows (2 * (r / 2)) (by omega)).1, jF, show 2 * (r / 2) % 2 = 0 by omega]; rfl
  have j1 : kc tr 30 (2 * (r / 2) + 1) 1 = 1 := by
    rw [(rows (2 * (r / 2) + 1) (by omega)).1, jF, show (2 * (r / 2) + 1) % 2 = 1 by omega]; rfl
  obtain ⟨-, blk, -, h16, -, wb, -, e0, e1, -⟩ := cut_group H hC cuti_hT (g := r / 2) (by omega) j0 j1
    (hcid (r / 2) (by omega)) (cnt _ (by omega)) (cnt _ (by omega))
  have getw : ∀ k, blk.getD k 0 < 2 ^ 64 := by
    intro k
    rw [List.getD_eq_getElem?_getD]
    rcases e : blk[k]? with _ | x
    · simp
    · exact wb x (List.mem_of_getElem? e)
  have key : ∃ x, x < 2 ^ 64 ∧ bwF tr pub 30 Cut.In.cols r w = wF x := by
    rcases (by omega : r = 2 * (r / 2) ∨ r = 2 * (r / 2) + 1) with e | e
    · rw [e]; exact ⟨_, getw w, e0 w hw⟩
    · rw [e]; exact ⟨_, getw (8 + w), e1 w hw⟩
  obtain ⟨x, hx, ex⟩ := key
  rw [streamW_getD tr pub 30 Cut.In.cols r hw, ex, decW_wF hx]
  exact ⟨rfl, hx⟩

include H in
/-- CUTI rows from the padding group on are inactive. -/
theorem cuti_late {N : Nat} (hN : 2 * N + 2 ≤ tr.height 30) (hp0 : kc tr 30 (2 * N) 3 = 1)
    (hp1 : kc tr 30 (2 * N + 1) 3 = 1) (hj1 : kc tr 30 (2 * N + 1) 1 = 1) :
    ∀ r, r < tr.height 30 → 2 * N ≤ r → rowNat tr 30 r 0 = 0 := by
  have hcs : Cut.In.cols = Cut.In.cols ∨ Cut.In.cols = Cut.Out.cols := Or.inl rfl
  have hC' := cuti_C H
  have dead : ∀ r, r < tr.height 30 → 2 * N + 2 ≤ r → kc tr 30 r 4 = 1 := by
    intro r
    induction r with
    | zero => intro _ h; omega
    | succ r ih =>
      intro hr hle
      by_cases h2 : r = 2 * N + 1
      · subst h2; exact (cut_trans hcs hC' (r := 2 * N + 1) hr).2.2.1 hj1 hp1
      · exact (cut_trans hcs hC' (r := r) hr).2.2.2.1 (ih (by omega) (by omega))
  intro r hr hle
  have hkD : kc tr 30 r 2 = 0 := by
    rcases (by omega : r = 2 * N ∨ r = 2 * N + 1 ∨ 2 * N + 2 ≤ r) with rfl | rfl | h
    · exact (cuti_bits H hr).2.1 hp0
    · exact (cuti_bits H hr).2.1 hp1
    · exact (cuti_bits H hr).2.2.1 (dead r hr h)
  have := (cuti_bits H hr).2.2.2.2 hkD
  show (kc tr 30 r 0).toNat = 0
  rw [this]; rfl

include H in
theorem cuti_N_unique {N N' : Nat} (hN : 2 * N + 2 ≤ tr.height 30) (hd : ∀ r, r < 2 * N → kc tr 30 r 2 = 1)
    (hp : kc tr 30 (2 * N) 3 = 1) (hN' : 2 * N' + 2 ≤ tr.height 30) (hd' : ∀ r, r < 2 * N' → kc tr 30 r 2 = 1)
    (hp' : kc tr 30 (2 * N') 3 = 1) : N = N' := by
  rcases Nat.lt_trichotomy N N' with h | h | h
  · exfalso
    have := (cuti_bits H (r := 2 * N) (by omega)).2.2.2.1 (hd' (2 * N) (by omega))
    rw [hp] at this; exact f_one_ne_zero this
  · exact h
  · exfalso
    have := (cuti_bits H (r := 2 * N') (by omega)).2.2.2.1 (hd (2 * N') (by omega))
    rw [hp'] at this; exact f_one_ne_zero this

theorem decFs_streamW (tr : Trace) (pub : List F) (t : Nat) (cs : List String) (r : Nat) :
    decFs (streamW tr pub t cs r) = (List.range 7).map (fun w => decF ((streamW tr pub t cs r).getD w 0)) := by
  apply List.ext_getElem (by simp [decFs, streamW])
  intro i h1 h2
  have hi : i < 7 := by simpa using h2
  simp [decFs, streamW, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (show i < 8 by omega)]

include H hC in
/-- **A CUTI data row, decoded from its words**: it is active iff its block's mark is 1, and then its
7 produced fields are `decFs` of its words. -/
theorem cuti_row_dec {N : Nat} (hN : 2 * N + 2 ≤ tr.height 30) (hd : ∀ r, r < 2 * N → kc tr 30 r 2 = 1)
    (hp : kc tr 30 (2 * N) 3 = 1) {r : Nat} (hr : r < 2 * N) :
    (rowNat tr 30 r 0 = 1 ↔ markOf (streamW tr pub 30 Cut.In.cols r) = 1) ∧
      (rowNat tr 30 r 0 = 1 → cutiRow tr r = decFs (streamW tr pub 30 Cut.In.cols r)) := by
  have hP := P_val
  have W := cuti_data_wF H hC hN hd hp r hr
  have hkP : kc tr 30 r 3 = 0 := (cuti_bits H (r := r) (by omega)).2.2.2.1 (hd r hr)
  have hab := (cuti_bits H (r := r) (by omega)).1
  let x : Nat → Nat := fun w => (streamW tr pub 30 Cut.In.cols r).getD w 0
  have lim : ∀ w, w < 7 →
      kc tr 30 r 0 * kc tr 30 r (5 + w) = ((x w % 2 ^ 21 : Nat) : F) ∧
      kc tr 30 r 0 * kc tr 30 r (12 + w) = ((x w / 2 ^ 21 % 2 ^ 21 : Nat) : F) ∧
      (if w = 0 then kc tr 30 r 0 + kc tr 30 r 3 * (1 - kc tr 30 r 1) * ((2 ^ 21 : Nat) : F) else 0) =
        ((x w / 2 ^ 42 : Nat) : F) := by
    intro w hw
    have e := (W w (by omega)).1
    rw [bwF_eq (Or.inl rfl) r (show w < 8 by omega), if_pos hw] at e
    simp only [wF, StateM5a.wlimbs, List.map_cons, List.map_nil, List.cons.injEq, and_true] at e
    exact e
  have hx : ∀ w, w < 7 → x w < 2 ^ 64 := fun w hw => (W w (by omega)).2
  obtain ⟨-, -, l2⟩ := lim 0 (by decide)
  simp only [if_true, hkP] at l2
  have l2' : kc tr 30 r 0 = ((x 0 / 2 ^ 42 : Nat) : F) := by rw [← l2]; grind
  have hx0 := hx 0 (by decide)
  have mk : markOf (streamW tr pub 30 Cut.In.cols r) = x 0 / 2 ^ 42 := rfl
  have hrn : rowNat tr 30 r 0 = x 0 / 2 ^ 42 := by
    show (kc tr 30 r 0).toNat = _
    rw [l2', Fp.toNat_cast_of_lt (by omega)]
  refine ⟨by rw [mk, hrn], fun ha => ?_⟩
  have a1 : kc tr 30 r 0 = 1 := by
    rcases hab with h | h
    · exfalso; have : rowNat tr 30 r 0 = 0 := by show (kc tr 30 r 0).toNat = 0; rw [h]; rfl
      omega
    · exact h
  rw [cutiRow, decFs_streamW]
  apply List.map_congr_left
  intro w hw
  have hw' : w < 7 := List.mem_range.mp hw
  obtain ⟨l0, l1, -⟩ := lim w hw'
  rw [a1] at l0 l1
  have e : kc tr 30 r (5 + w) + ((65536 : Nat) : F) * kc tr 30 r (12 + w) =
      ((x w % 2 ^ 21 + 65536 * (x w / 2 ^ 21 % 2 ^ 21) : Nat) : F) := by
    have l0' : kc tr 30 r (5 + w) = ((x w % 2 ^ 21 : Nat) : F) := by rw [← l0]; grind
    have l1' : kc tr 30 r (12 + w) = ((x w / 2 ^ 21 % 2 ^ 21 : Nat) : F) := by rw [← l1]; grind
    rw [l0', l1', fcast]
  show (kc tr 30 r (5 + w) + ((65536 : Nat) : F) * kc tr 30 r (12 + w)).toNat = decF (x w)
  rw [e, Fp.toNat_cast]; rfl

theorem range_filter_stop {p : Nat → Bool} {M : Nat} : ∀ h, M ≤ h → (∀ r, M ≤ r → r < h → p r = false) →
    (List.range h).filter p = (List.range M).filter p
  | 0, hM, _ => by rw [show M = 0 by omega]
  | h + 1, hM, hp => by
    rcases Nat.lt_or_eq_of_le hM with hlt | rfl
    · rw [List.range_succ, List.filter_append, range_filter_stop h (by omega) (fun r h1 h2 => hp r h1 (by omega))]
      simp [hp h (by omega) (by omega)]
    · rfl

include H hC in
/-- **CUTI's digest and productions as a function of its hashed words** (item 1).  There are 8-word
blocks `B` (one per data row, all words `< 2^64`) such that the public `ctx_in` limbs are those of a
digest `d` with `wbytes d = sha384 (wbytes B.flatten)` (FIPS 180-4 SHA-384 of the concatenated words),
and CUTI's CH productions are, in row order, `ofFields (decFs b) t_in` for the blocks `b` with mark 1. -/
theorem cuti_stream :
    ∃ B : List (List Nat), (∀ b ∈ B, b.length = 8 ∧ StateM5a.Sha512If.W64 b) ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxIn = limbsF d ∧
        wbytes d = NearSpecV3.E2E.Bnd.sha384 (wbytes B.flatten)) ∧
      (part Cut.In.table tr pub 30 busStk true).map decMsg =
        (B.filter (fun b => markOf b = 1)).map (fun b => ofFields (decFs b) (pub.getD pubTIn 0).toNat) := by
  obtain ⟨N, hN, hd, hp, hw, d, h6, hW, hpub, hsha⟩ := cut_stream_digest H hC cuti_hT
  have hcs : Cut.In.cols = Cut.In.cols ∨ Cut.In.cols = Cut.Out.cols := Or.inl rfl
  obtain ⟨N', hN', hd', hp0', hp1', rows, -, -⟩ := cut_rows hcs (cuti_C H) (H.heightPos 30 (cutT_lt cuti_hT))
  have eN := cuti_N_unique H hN hd hp hN' hd' hp0'
  subst eN
  have hj1 : kc tr 30 (2 * N + 1) 1 = 1 := by
    rw [(rows (2 * N + 1) (by omega)).1, jF, show (2 * N + 1) % 2 = 1 by omega]; rfl
  let B := (List.range (2 * N)).map (streamW tr pub 30 Cut.In.cols)
  have hBf : B.flatten = (List.range (2 * N)).flatMap (streamW tr pub 30 Cut.In.cols) := by
    simp [B, List.flatMap_def]
  refine ⟨B, fun b hb => ?_, ⟨d, h6, hW, hpub, by rw [hBf]; exact hsha⟩, ?_⟩
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    refine ⟨streamW_length _ _ _ _ _, fun w hw' => hw w ?_⟩
    exact List.mem_flatMap.mpr ⟨r, hr, hw'⟩
  · rw [cuti_part, range_filter_stop (M := 2 * N) _ (by omega) (fun r h1 h2 => by
      have := cuti_late H hN hp hp1' hj1 r h2 h1; simp [this])]
    have hf : (List.range (2 * N)).filter (fun r => decide (rowNat tr 30 r 0 = 1)) =
        (List.range (2 * N)).filter ((fun b => decide (markOf b = 1)) ∘ streamW tr pub 30 Cut.In.cols) :=
      List.filter_congr (fun r hr => by
        rw [Function.comp_apply]
        exact decide_eq_decide.mpr (cuti_row_dec H hC hN hd hp (List.mem_range.mp hr)).1)
    simp only [B]
    rw [List.filter_map, List.map_map, ← hf]
    apply List.map_congr_left
    intro r hr
    obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
    have := (cuti_row_dec H hC hN hd hp (List.mem_range.mp hr1)).2 (by simpa using hr2)
    simp only [Function.comp, this]

end

/-! ## 4. CR decoding: CUTI's productions are the previous view (or SHA-384 collides) -/

theorem wF_len3 (w : Nat) : (wF w).length = 3 := rfl

theorem limbsF_inj : ∀ {d d' : List Nat}, d.length = d'.length → StateM5a.Sha512If.W64 d →
    StateM5a.Sha512If.W64 d' → limbsF d = limbsF d' → d = d'
  | [], [], _, _, _, _ => rfl
  | a :: d, a' :: d', hl, hw, hw', h => by
    simp only [limbsF, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [wF_len3, wF_len3])
    rw [wF_inj (hw a List.mem_cons_self) (hw' a' List.mem_cons_self) h1,
      limbsF_inj (by simpa using hl) (fun w hw0 => hw w (List.mem_cons_of_mem _ hw0))
        (fun w hw0 => hw' w (List.mem_cons_of_mem _ hw0)) h2]
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl

theorem wbytes_inj : ∀ {x y : List Nat}, StateM5a.Sha512If.W64 x → StateM5a.Sha512If.W64 y →
    wbytes x = wbytes y → x = y
  | [], [], _, _, _ => rfl
  | a :: x, b :: y, hx, hy, h => by
    simp only [wbytes, List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp [ArenaCore.Bytes.beN_length])
    have e : a = b := wordBytes_inj (hx a List.mem_cons_self) (hy b List.mem_cons_self)
      (by rw [wordBytes_eq_beN, wordBytes_eq_beN]; exact h1)
    rw [e, wbytes_inj (fun w hw => hx w (List.mem_cons_of_mem _ hw)) (fun w hw => hy w (List.mem_cons_of_mem _ hw)) h2]
  | [], _ :: _, _, _, h => by
    have := congrArg List.length h; simp [wbytes_length] at this
  | _ :: _, [], _, _, h => by
    have := congrArg List.length h; simp [wbytes_length] at this

theorem flatten_inj_blocks {α : Type} {n : Nat} (hn : 0 < n) : ∀ {A B : List (List α)},
    (∀ a ∈ A, a.length = n) → (∀ b ∈ B, b.length = n) → A.flatten = B.flatten → A = B
  | [], [], _, _, _ => rfl
  | a :: A, b :: B, hA, hB, h => by
    simp only [List.flatten_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by rw [hA a List.mem_cons_self, hB b List.mem_cons_self])
    rw [h1, flatten_inj_blocks hn (fun x hx => hA x (List.mem_cons_of_mem _ hx))
      (fun x hx => hB x (List.mem_cons_of_mem _ hx)) h2]
  | [], b :: B, _, hB, h => by
    have := congrArg List.length h
    simp only [List.flatten_nil, List.length_nil, List.flatten_cons, List.length_append, hB b List.mem_cons_self] at this
    omega
  | a :: A, [], hA, _, h => by
    have := congrArg List.length h
    simp only [List.flatten_nil, List.length_nil, List.flatten_cons, List.length_append, hA a List.mem_cons_self] at this
    omega

/-- The CUT filler block (the all-zero message completing an odd list). -/
def fillerB (L : List (List Nat)) : List (List Nat) := if L.length % 2 = 1 then [List.replicate 8 0] else []

theorem cutWords_blocks (L : List (List Nat)) : cutWords L = (L.map msgWords ++ fillerB L).flatten := by
  unfold cutWords fillerB
  rw [List.flatten_append, ← List.flatMap_def]
  split <;> simp

theorem cutWords_w64 {L : List (List Nat)} (hL : ∀ y ∈ L, MsgWF y) : StateM5a.Sha512If.W64 (cutWords L) := by
  intro w hw
  rw [cutWords_blocks, List.mem_flatten] at hw
  obtain ⟨b, hb, hw⟩ := hw
  rcases List.mem_append.mp hb with hb | hb
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    exact msgWords_w64 (hL y hy) w hw
  · unfold fillerB at hb; split at hb
    · simp at hb; subst hb; simp at hw; omega
    · simp at hb

/-- **CR decoding (item 2).**  If the public `ctx_in` is the digest `cutDigest L` of a list of
well-formed messages, then SHA-384 collides, or CUTI's CH productions are exactly the entries of `L`
in order, each as a message at `t_in`. -/
theorem cuti_view {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    {chip : List StateM5a.Sha512If.IfMsg} (hC : ChipIf compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    {L : List (List Nat)} (hL : ∀ y ∈ L, MsgWF y) (hpub : PubDigIs pub pubCtxIn (cutDigest L)) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      (part Cut.In.table tr pub 30 busStk true).map decMsg = L.map (fun y => ofFields y (pub.getD pubTIn 0).toNat) := by
  obtain ⟨B, hB, ⟨d, h6, hW, hpd, hsha⟩, hprod⟩ := cuti_stream H hC
  obtain ⟨d', h6', hW', hpd', hx'⟩ := hpub
  have edd : d = d' := limbsF_inj (by rw [h6, h6']) hW hW' (by rw [← hpd, hpd'])
  subst edd
  rw [hsha, cutDigest, cutBytes_eq] at hx'
  by_cases e : wbytes B.flatten = wbytes (cutWords L)
  · right
    have hBw : StateM5a.Sha512If.W64 B.flatten := by
      intro w hw
      obtain ⟨b, hb, hw⟩ := List.mem_flatten.mp hw
      exact (hB b hb).2 w hw
    have e2 := wbytes_inj hBw (cutWords_w64 hL) e
    rw [cutWords_blocks] at e2
    have e3 : B = L.map msgWords ++ fillerB L := flatten_inj_blocks (n := 8) (by decide)
      (fun b hb => (hB b hb).1) (fun b hb => by
        rcases List.mem_append.mp hb with hb | hb
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
          exact msgWords_length (hL y hy).1
        · unfold fillerB at hb; split at hb
          · simp at hb; subst hb; rfl
          · simp at hb) e2
    rw [hprod, e3, List.filter_append]
    have f1 : (L.map msgWords).filter (fun b => decide (markOf b = 1)) = L.map msgWords :=
      List.filter_eq_self.mpr (fun b hb => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
        simp [markOf_msgWords (hL y hy)])
    have f2 : (fillerB L).filter (fun b => decide (markOf b = 1)) = [] := by
      unfold fillerB; split <;> decide
    rw [f1, f2, List.append_nil, List.map_map]
    apply List.map_congr_left
    intro y hy
    simp only [Function.comp, decFs_msgWords (hL y hy)]
  · left
    exact StateM5a.StateView.sha384_coll e hx'

/-! ## 5. The in-boundary block is duplicate-free (item 3)

`initS = CUTI ∪ MEMB ∪ SEGB`.  CUTI's part is the previous view (item 2), duplicate-free under
`RegWF` (`cutView_nodup`), in spaces other than 3 and 7.  MEMB's part: data row `9b + k` sends the
bytes at `1024·blk_b + 128·k + i` (`i < 128`), with `blk_b < 2^16` (R16 on the block's padding row,
which exists: `memb_complete`) and distinct across blocks (`memb_blk_distinct_of_holds`), so all
addresses differ (`memb_addr_inj`); space 3.  SEGB's part is its one gas message (space 7). -/

theorem filterMap_uniform {row : Row} {c : Expr} : ∀ (l : List Inter), (∀ i ∈ l, i.count = c) →
    (l.filterMap fun i => if (i.count.eval row).toNat = 1 then some (i.msg.map (·.eval row)) else none) =
      if (c.eval row).toNat = 1 then l.map (fun i => i.msg.map (·.eval row)) else []
  | [], _ => by split <;> rfl
  | i :: l, hc => by
    rw [List.filterMap_cons, hc i List.mem_cons_self,
      filterMap_uniform l (fun j hj => hc j (List.mem_cons_of_mem _ hj))]
    by_cases h : (c.eval row).toNat = 1 <;> simp [h]

theorem memb_send_filter : Memb.table.inters.filter (fun i => i.bus = busStk ∧ i.send = true) =
    (List.range 128).map (fun i => chSend 3 (Memb.addr i) 0 [Memb.c s!"bi{i}", 0, 0, 0] (pv pubTIn) Memb.kD) := by
  decide +kernel

/-- MEMB's byte message `i` on row `r` (before decoding). -/
def membMsg (tr : Trace) (pub : List F) (r i : Nat) : List F :=
  (chSend 3 (Memb.addr i) 0 [Memb.c s!"bi{i}", 0, 0, 0] (pv pubTIn) Memb.kD).msg.map (·.eval (tr.row pub 19 r))

theorem memb_part (tr : Trace) (pub : List F) : part Memb.table tr pub 19 busStk true =
    (List.range (tr.height 19)).flatMap (fun r =>
      if (Memb.kD.eval (tr.row pub 19 r)).toNat = 1 then (List.range 128).map (membMsg tr pub r) else []) := by
  unfold part
  congr 1; funext r
  rw [rowMsgs_eq, memb_send_filter, filterMap_uniform _ (fun i hi => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hi; rfl), List.map_map]
  rfl

theorem membMsg_space (tr : Trace) (pub : List F) (r i : Nat) : (decMsg (membMsg tr pub r i)).space = 3 := by
  simp only [membMsg, decMsg, chSend, List.map_cons, List.cons_append, List.getD_cons_zero]
  rfl

theorem membMsg_slot (tr : Trace) (pub : List F) (r i : Nat) :
    (decMsg (membMsg tr pub r i)).slot = ((Memb.addr i).eval (tr.row pub 19 r)).toNat := by
  simp only [membMsg, decMsg, chSend, List.map_cons, List.cons_append, List.getD_cons_zero, List.getD_cons_succ]

theorem memb_kD_eval (tr : Trace) (pub : List F) (r : Nat) : Memb.kD.eval (tr.row pub 19 r) =
    ((mbN tr r 1 + mbN tr r 2 + mbN tr r 3 + mbN tr r 4 + mbN tr r 5 + mbN tr r 6 + mbN tr r 7 + mbN tr r 8 : Nat) : F) := by
  have e8 : Memb.kD = 0 + Memb.p 0 + Memb.p 1 + Memb.p 2 + Memb.p 3 + Memb.p 4 + Memb.p 5 + Memb.p 6 +
      Memb.p 7 := rfl
  rw [e8]
  simp only [Expr.eval_add', Expr.eval_ofNat', memb_p_eval tr pub r (show 0 < 9 by decide),
    memb_p_eval tr pub r (show 1 < 9 by decide), memb_p_eval tr pub r (show 2 < 9 by decide),
    memb_p_eval tr pub r (show 3 < 9 by decide), memb_p_eval tr pub r (show 4 < 9 by decide),
    memb_p_eval tr pub r (show 5 < 9 by decide), memb_p_eval tr pub r (show 6 < 9 by decide),
    memb_p_eval tr pub r (show 7 < 9 by decide), Lean.Grind.Semiring.natCast_add]
  grind

section memb
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

/-- A MEMB row whose byte sends fire (`kD = 1`) is an active data row. -/
theorem memb_kD_one {r : Nat} (hr : r < tr.height 19) (h : (Memb.kD.eval (tr.row pub 19 r)).toNat = 1) :
    mbN tr r 0 = 1 ∧ r % 9 < 8 := by
  have hP := P_val
  obtain ⟨ha, bp, hs⟩ := memb_row H hr
  have b1 : mbN tr r 1 ≤ 1 := bp 0 (by decide)
  have b2 : mbN tr r 2 ≤ 1 := bp 1 (by decide)
  have b3 : mbN tr r 3 ≤ 1 := bp 2 (by decide)
  have b4 : mbN tr r 4 ≤ 1 := bp 3 (by decide)
  have b5 : mbN tr r 5 ≤ 1 := bp 4 (by decide)
  have b6 : mbN tr r 6 ≤ 1 := bp 5 (by decide)
  have b7 : mbN tr r 7 ≤ 1 := bp 6 (by decide)
  have b8 : mbN tr r 8 ≤ 1 := bp 7 (by decide)
  have b9 : mbN tr r 9 ≤ 1 := bp 8 (by decide)
  rw [memb_kD_eval, Fp.toNat_cast_of_lt (by omega)] at h
  have ha1 : mbN tr r 0 = 1 := by omega
  refine ⟨ha1, ?_⟩
  have hp := (memb_pos H r hr ha1).2
  refine Classical.byContradiction fun hq => ?_
  have h8 : r % 9 = 8 := by have := Nat.mod_lt r (show 9 > 0 by decide); omega
  rw [h8] at hp
  have : mbN tr r 9 = 1 := hp
  omega

/-- The address of byte `i` on an active data row. -/
theorem memb_data_addr {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 < 8) (i : Nat) :
    (Memb.addr i).eval (tr.row pub 19 r) = ((1024 * mbN tr r 10 + 128 * (r % 9) + i : Nat) : F) := by
  have hp := (memb_pos H r hr ha).2
  obtain ⟨k, hkdef⟩ : ∃ k, k = r % 9 := ⟨_, rfl⟩
  rw [← hkdef] at hp hq ⊢
  have oh : ∀ j, j < 9 → mbN tr r (1 + j) = if j = k then 1 else 0 := by
    intro j hj
    by_cases hjk : j = k
    · subst hjk; simpa using hp
    · rw [if_neg hjk]; exact memb_onehot H hr (k := k) (by omega) hj (Ne.symm hjk) hp
  have pe : ∀ j, j < 9 → (Memb.p j).eval (tr.row pub 19 r) = (((if j = k then 1 else 0 : Nat) : Nat) : F) := by
    intro j hj; rw [memb_p_eval tr pub r hj, oh j hj]
  have kk : Memb.kk.eval (tr.row pub 19 r) = ((k : Nat) : F) := by
    have e9 : Memb.kk = 0 + Expr.c 0 * Memb.p 0 + Expr.c 1 * Memb.p 1 + Expr.c 2 * Memb.p 2 +
        Expr.c 3 * Memb.p 3 + Expr.c 4 * Memb.p 4 + Expr.c 5 * Memb.p 5 + Expr.c 6 * Memb.p 6 +
        Expr.c 7 * Memb.p 7 + Expr.c 8 * Memb.p 8 := rfl
    rw [e9]
    simp only [Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_c, pe 0 (by decide),
      pe 1 (by decide), pe 2 (by decide), pe 3 (by decide), pe 4 (by decide), pe 5 (by decide),
      pe 6 (by decide), pe 7 (by decide), pe 8 (by decide)]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      h | h | h | h | h | h | h | h <;> simp [h] <;> decide
  simp only [Memb.addr, Expr.eval_add', Expr.eval_mul', Expr.eval_ofNat', Expr.eval_c, memb_c_eval, mb_ix.2.1, kk]
  simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]

/-- An active data row is followed by an active row of the same block. -/
theorem memb_next {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 < 8) :
    r + 1 < tr.height 19 ∧ mbN tr (r + 1) 0 = 1 := by
  have hP := P_val
  have hp := (memb_pos H r hr ha).2
  have hm : r % 9 < 9 := Nat.mod_lt _ (by decide)
  have hp8 : mbN tr r (1 + 8) = 0 := memb_onehot H hr (k := r % 9) (j := 8) hm (by decide) (by omega) hp
  have hr1 : r + 1 < tr.height 19 := by
    refine Classical.byContradiction fun hn => ?_
    have hl : r + 1 = tr.height 19 := by omega
    have h := memb_C H hr (Expr.last * Memb.c "act" * (1 - Memb.p 8)) (by simp [Memb.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_c_eval, mb_ix.1,
      memb_p_eval tr pub r (show 8 < 9 by decide), ha, hp8, sel_last (t := 19) (tr := tr) (pub := pub) hl] at h
    exact absurd h (by decide)
  refine ⟨hr1, ?_⟩
  have hmem : Expr.trans * Memb.p (r % 9) * (1 - nv (ix Memb.cols s!"p{r % 9 + 1}")) ∈ Memb.constraints := by
    unfold Memb.constraints
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))))))
    exact List.mem_map.mpr ⟨r % 9, List.mem_range.mpr hq, rfl⟩
  have h := memb_C H (r := r) hr _ hmem
  rw [mb_ix_p (r % 9 + 1) (by omega)] at h
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_p_eval tr pub r hm, nv,
    Expr.eval_nxt, trans_eval_one tr pub 19 r hr1, hp, cast_one] at h
  simp only [Trace.row, Nat.mod_eq_of_lt hr1, cell_cast] at h
  have hq1 : mbN tr (r + 1) (1 + (r % 9 + 1)) = 1 :=
    natEq (R := 1) (by rw [cast_one]; grind) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
  obtain ⟨ha', bp', hs'⟩ := memb_row H hr1
  have b1 : mbN tr (r + 1) 1 ≤ 1 := bp' 0 (by decide)
  have b2 : mbN tr (r + 1) 2 ≤ 1 := bp' 1 (by decide)
  have b3 : mbN tr (r + 1) 3 ≤ 1 := bp' 2 (by decide)
  have b4 : mbN tr (r + 1) 4 ≤ 1 := bp' 3 (by decide)
  have b5 : mbN tr (r + 1) 5 ≤ 1 := bp' 4 (by decide)
  have b6 : mbN tr (r + 1) 6 ≤ 1 := bp' 5 (by decide)
  have b7 : mbN tr (r + 1) 7 ≤ 1 := bp' 6 (by decide)
  have b8 : mbN tr (r + 1) 8 ≤ 1 := bp' 7 (by decide)
  have b9 : mbN tr (r + 1) 9 ≤ 1 := bp' 8 (by decide)
  rcases (by omega : r % 9 = 0 ∨ r % 9 = 1 ∨ r % 9 = 2 ∨ r % 9 = 3 ∨ r % 9 = 4 ∨ r % 9 = 5 ∨ r % 9 = 6 ∨
    r % 9 = 7) with e | e | e | e | e | e | e | e <;> rw [e] at hq1 <;>
    (have : _ := hq1; simp only [Nat.reduceAdd] at this; omega)

/-- **An active data row's block is complete**: its padding row `9·(r/9) + 8` exists and is active. -/
theorem memb_complete : ∀ j r, 8 - r % 9 = j → r < tr.height 19 → mbN tr r 0 = 1 →
    9 * (r / 9) + 8 < tr.height 19 ∧ mbN tr (9 * (r / 9) + 8) 0 = 1
  | 0, r, hj, hr, ha => by
    have : r = 9 * (r / 9) + 8 := by have := Nat.mod_lt r (show 9 > 0 by decide); omega
    rw [← this]; exact ⟨hr, ha⟩
  | j + 1, r, hj, hr, ha => by
    have hq : r % 9 < 8 := by omega
    obtain ⟨hr1, ha1⟩ := memb_next H hr ha hq
    have e1 : (r + 1) / 9 = r / 9 := by omega
    have := memb_complete j (r + 1) (by omega) hr1 ha1
    rwa [e1] at this

/-- The padding row's `blk` is below `2^16` (R16 on `blk`, count `p8`). -/
theorem memb_blk_lt {b : Nat} (hr : 9 * b + 8 < tr.height 19) (ha : mbN tr (9 * b + 8) 0 = 1) :
    mbN tr (9 * b + 8) 10 < 65536 := by
  have ht : 19 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hp8 : mbN tr (9 * b + 8) (1 + 8) = 1 := by
    have := (memb_pos H _ hr ha).2; rwa [show (9 * b + 8) % 9 = 8 by omega] at this
  have mem : r16 (Memb.c "blk") (Memb.p 8) ∈ ((wasmBaseSegAir nloc ngl).tables[19]'ht).inters := by
    rw [seg_t19]
    show _ ∈ Memb.inters
    unfold Memb.inters
    refine List.mem_append_right _ ?_
    simp
  have h := seg_r16_lt H (seg_hsend_r16 H) ht hr mem (by rw [memb_p_eval tr pub _ (by decide), hp8]; decide)
  simpa only [memb_c_eval, mb_ix.2.1, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] using h

/-- The decoded address of byte `i` of an active data row, through its block's padding row. -/
theorem memb_slot {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 < 8) {i : Nat} (hi : i < 128) :
    (decMsg (membMsg tr pub r i)).slot = 1024 * mbN tr (9 * (r / 9) + 8) 10 + 128 * (r % 9) + i ∧
      mbN tr (9 * (r / 9) + 8) 10 < 65536 ∧ 9 * (r / 9) + 8 < tr.height 19 ∧ mbN tr (9 * (r / 9) + 8) 0 = 1 := by
  have hP := P_val
  obtain ⟨hc, hca⟩ := memb_complete H _ r rfl hr ha
  have hlt := memb_blk_lt H hc hca
  have hk := memb_blk_const H (b := r / 9) hc hca (r % 9) (by omega)
  rw [show 9 * (r / 9) + r % 9 = r by omega] at hk
  refine ⟨?_, hlt, hc, hca⟩
  rw [membMsg_slot, memb_data_addr H hr ha hq, hk, Fp.toNat_cast_of_lt (by omega)]

/-- **MEMB's in-side productions are duplicate-free.** -/
theorem memb_part_nodup : ((part Memb.table tr pub 19 busStk true).map decMsg).Nodup := by
  rw [memb_part, List.map_flatMap]
  refine nodup_flatMap_of _ _ (fun r hr => ?_) ?_
  · split
    · rename_i hk
      obtain ⟨ha, hq⟩ := memb_kD_one H (List.mem_range.mp hr) hk
      rw [List.map_map]
      refine nodup_map_range 128 _ (fun i j hi hj e => ?_)
      have := congrArg Msg.slot e
      simp only [Function.comp] at this
      rw [(memb_slot H (List.mem_range.mp hr) ha hq hi).1, (memb_slot H (List.mem_range.mp hr) ha hq hj).1] at this
      omega
    · exact List.nodup_nil
  · refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := tr.height 19))
    intro r r' hr hr' hne x hx hx'
    split at hx
    · rename_i hk
      split at hx'
      · rename_i hk'
        have hr0 := List.mem_range.mp hr
        have hr0' := List.mem_range.mp hr'
        obtain ⟨ha, hq⟩ := memb_kD_one H hr0 hk
        obtain ⟨ha', hq'⟩ := memb_kD_one H hr0' hk'
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (by simpa only [List.map_map] using hx)
        obtain ⟨i', hi', e⟩ := List.mem_map.mp (by simpa only [List.map_map] using hx')
        have hs := congrArg Msg.slot e
        simp only [Function.comp] at hs
        obtain ⟨s1, l1, c1, a1⟩ := memb_slot H hr0 ha hq (List.mem_range.mp hi)
        obtain ⟨s2, l2, c2, a2⟩ := memb_slot H hr0' ha' hq' (List.mem_range.mp hi')
        rw [s1, s2] at hs
        have hii := List.mem_range.mp hi
        have hii' := List.mem_range.mp hi'
        obtain ⟨eb, ek, -⟩ := memb_addr_inj hq' hq hii' hii hs
        by_cases hb : r' / 9 = r / 9
        · omega
        · exact memb_blk_distinct_of_holds H hb c2 c1 a2 a1 eb
      · simp at hx'
    · simp at hx

end memb

theorem segb_send_filter : Segb.table.inters.filter (fun i => i.bus = busStk ∧ i.send = true) =
    [chSend (Expr.c spaceGas) 0 (pv pubSsegIn) (Segb.pubs pubGbIn 4) (pv pubTIn) .first] := by
  decide +kernel

theorem segb_part (tr : Trace) (pub : List F) (h0 : 1 ≤ tr.height 0) :
    (part Segb.table tr pub 0 busStk true).map decMsg =
      [decMsg ((chSend (Expr.c spaceGas) 0 (pv pubSsegIn) (Segb.pubs pubGbIn 4) (pv pubTIn) .first).msg.map
        (·.eval (tr.row pub 0 0)))] := by
  rw [part_first segb_send_filter rfl h0]; rfl

theorem segb_gas_space (tr : Trace) (pub : List F) :
    (decMsg ((chSend (Expr.c spaceGas) 0 (pv pubSsegIn) (Segb.pubs pubGbIn 4) (pv pubTIn) .first).msg.map
      (·.eval (tr.row pub 0 0)))).space = 7 := by
  simp only [decMsg, chSend, List.map_cons, List.cons_append, List.getD_cons_zero, Expr.eval_c, spaceGas]
  rfl

theorem fieldsOf_ofFields {y : List Nat} (hy : y.length = 7) (tp : Nat) : fieldsOf (ofFields y tp) = y := by
  match y, hy with
  | [a, b, c, d, e, f, g], _ => rfl

/-- **The in-boundary block is duplicate-free** (item 3), given CUTI's productions as a list `L` of
well-formed, distinct messages outside spaces 3 and 7 (item 2 gives `L = cutView X s`). -/
theorem initS_nodup_of {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    {L : List (List Nat)}
    (hc : (part Cut.In.table tr pub 30 busStk true).map decMsg = L.map (fun y => ofFields y (pub.getD pubTIn 0).toNat))
    (hL : L.Nodup) (hwf : ∀ y ∈ L, MsgWF y) (hsp : ∀ y ∈ L, y.getD 0 0 ≠ 3 ∧ y.getD 0 0 ≠ 7) :
    (initS tr pub).Nodup := by
  have h0 : 1 ≤ tr.height 0 := seg_h0 H
  unfold initS
  rw [hc, segb_part tr pub h0, List.nodup_append, List.nodup_append]
  refine ⟨nodup_map_of_inj _ L hL (fun a ha b hb e => ?_), ⟨memb_part_nodup H, by simp, ?_⟩, ?_⟩
  · have := congrArg fieldsOf e
    rwa [fieldsOf_ofFields (hwf a ha).1, fieldsOf_ofFields (hwf b hb).1] at this
  · intro a ha b hb e
    rw [List.mem_singleton] at hb
    have s1 : a.space = 3 := by
      rw [memb_part, List.map_flatMap] at ha
      obtain ⟨r, -, hr⟩ := List.mem_flatMap.mp ha
      split at hr
      · obtain ⟨i, -, rfl⟩ := List.mem_map.mp (by simpa only [List.map_map] using hr)
        exact membMsg_space tr pub r i
      · simp at hr
    have s2 := segb_gas_space tr pub
    rw [← hb, ← e] at s2; omega
  · intro a ha b hb e
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
    have hs : (ofFields y (pub.getD pubTIn 0).toNat).space = y.getD 0 0 := rfl
    subst e
    rcases List.mem_append.mp hb with hb | hb
    · rw [memb_part, List.map_flatMap] at hb
      obtain ⟨r, -, hr⟩ := List.mem_flatMap.mp hb
      split at hr
      · obtain ⟨i, -, e⟩ := List.mem_map.mp (by simpa only [List.map_map] using hr)
        have := membMsg_space tr pub r i
        simp only [Function.comp] at e
        rw [e, hs] at this
        exact (hsp y hy).1 this
      · simp at hr
    · rw [List.mem_singleton] at hb
      have := segb_gas_space tr pub
      rw [← hb, hs] at this
      exact (hsp y hy).2 this

/-- The view's entries are in spaces other than 3 and 7. -/
theorem cutView_sp {X : Ctx} {s : St} {y : List Nat} (hy : y ∈ cutView X s) : y.getD 0 0 ≠ 3 ∧ y.getD 0 0 ≠ 7 := by
  obtain ⟨x, hx, rfl⟩ := mem_cutView.mp hy
  have : (fieldsOf x).getD 0 0 = x.space := rfl
  rw [this]
  rcases cutMsgs_space hx with a | a | a | a | ⟨a, -⟩ | a <;> omega

/-- **`(initS tr pub).Nodup` at a view boundary** (item 3): CUTI produces `cutView X s` (item 2),
`RegWF s`, the view `MsgWF`. -/
theorem initS_nodup {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    {X : Ctx} {s : St} (hw : RegWF s) (hwf : ∀ y ∈ cutView X s, MsgWF y)
    (hc : (part Cut.In.table tr pub 30 busStk true).map decMsg =
      (cutView X s).map (fun y => ofFields y (pub.getD pubTIn 0).toNat)) :
    (initS tr pub).Nodup :=
  initS_nodup_of H hc (cutView_nodup X hw) hwf (fun y hy => cutView_sp hy)

end Cuti

#print axioms Cuti.cuti_part
#print axioms Cuti.cuti_stream
#print axioms Cuti.cuti_view
#print axioms Cuti.memb_part_nodup
#print axioms Cuti.initS_nodup

end WasmBase
