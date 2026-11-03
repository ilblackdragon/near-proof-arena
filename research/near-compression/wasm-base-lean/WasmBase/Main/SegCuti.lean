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

end Cuti

#print axioms Cuti.cuti_part
#print axioms Cuti.cuti_stream
#print axioms Cuti.cuti_view

end WasmBase
