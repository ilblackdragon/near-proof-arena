import WasmBase.Main.SegCuti
import WasmBase.Main.SegS.SegSoundC
/-!
# WasmBase.Main.SegS.SegCuti — `SegCuti`'s `seg_sound` chain from `HoldsXS` (E2E M4c, MP)

Copies of the declarations of `Main/SegCuti.lean` that `seg_sound` uses, with `HoldsX (wasmBaseSegAir …)` replaced by `HoldsXS` (no table 20, no buses 15/16/17/103; `Main/SegHoldsS.lean`) and every chain name `foo` renamed `fooS`.  Proofs are the originals', with the side conditions `t ≠ 20` / `OkBus b` added.
-/
namespace WasmBase

open ZkFormal.Algebra Chips Seg SegSha
open NearSpecV3.Wasm hiding P

namespace Cuti

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
  {chip : List StateM5a.Sha512If.IfMsg} (hC : SegSha.ChipIfS compressW nloc ngl pub tr chip)

include H in
theorem cuti_CS : ∀ r, r < tr.height 30 → ∀ e ∈ Cut.streamConstraints Cut.In.cols pubCtxIn,
    e.eval (tr.row pub 30 r) = 0 := cutT_CS H cuti_hT

include H in
/-- On a CUTI row with `kD = 0`, `act = 0`; with `kP = 1`, `kD = 0`. -/
theorem cuti_bitsS {r : Nat} (hr : r < tr.height 30) :
    (kc tr 30 r 0 = 0 ∨ kc tr 30 r 0 = 1) ∧ (kc tr 30 r 3 = 1 → kc tr 30 r 2 = 0) ∧
      (kc tr 30 r 4 = 1 → kc tr 30 r 2 = 0) ∧ (kc tr 30 r 2 = 1 → kc tr 30 r 3 = 0) ∧
      (kc tr 30 r 2 = 0 → kc tr 30 r 0 = 0) := by
  obtain ⟨ha, -, k, h0⟩ := cut_bits (Or.inl rfl) (cuti_CS H) (r := r) hr
  refine ⟨ha, fun h => ?_, fun h => ?_, fun h => ?_, h0⟩ <;>
    rcases k with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> first | assumption |
      (exfalso; first | (rw [h] at a; first | exact f_one_ne_zero a | exact f_one_ne_zero a.symm) |
        (rw [h] at b; first | exact f_one_ne_zero b | exact f_one_ne_zero b.symm) |
        (rw [h] at c; first | exact f_one_ne_zero c | exact f_one_ne_zero c.symm))

include H hC in
/-- **The words of a CUTI data row are chip words**: each of its 8 limb triples is `wF` of the decoded
word, which is `< 2^64`. -/
theorem cuti_data_wFS {N : Nat} (hN : 2 * N + 2 ≤ tr.height 30) (hd : ∀ r, r < 2 * N → kc tr 30 r 2 = 1)
    (hp : kc tr 30 (2 * N) 3 = 1) :
    ∀ r, r < 2 * N → ∀ w, w < 8 →
      bwF tr pub 30 Cut.In.cols r w = wF ((streamW tr pub 30 Cut.In.cols r).getD w 0) ∧
        (streamW tr pub 30 Cut.In.cols r).getD w 0 < 2 ^ 64 := by
  have hcs : Cut.In.cols = Cut.In.cols ∨ Cut.In.cols = Cut.Out.cols := Or.inl rfl
  have hC' := cuti_CS H
  have ht := cutT_lt (nloc := nloc) (ngl := ngl) cuti_hT
  have hh : 4 ≤ tr.height 30 := H.heightPos 30 ht
  obtain ⟨N', hN', hd', hp0', -, rows, hcid, -⟩ := cut_rows hcs hC' hh
  have eN : N = N' := by
    rcases Nat.lt_trichotomy N N' with h | h | h
    · exfalso
      have := (cuti_bitsS H (r := 2 * N) (by omega)).2.2.2.1 (hd' (2 * N) (by omega))
      rw [hp] at this; exact f_one_ne_zero this
    · exact h
    · exfalso
      have := (cuti_bitsS H (r := 2 * N') (by omega)).2.2.2.1 (hd (2 * N') (by omega))
      rw [hp0'] at this; exact f_one_ne_zero this
  subst eN
  have cnt : ∀ r, r < 2 * N → kc tr 30 r 2 + kc tr 30 r 3 = 1 := by
    intro r hr
    rw [hd r hr, (cuti_bitsS H (r := r) (by omega)).2.2.2.1 (hd r hr)]; grind
  intro r hr w hw
  have hg : r / 2 < N := by omega
  have j0 : kc tr 30 (2 * (r / 2)) 1 = 0 := by
    rw [(rows (2 * (r / 2)) (by omega)).1, jF, show 2 * (r / 2) % 2 = 0 by omega]; rfl
  have j1 : kc tr 30 (2 * (r / 2) + 1) 1 = 1 := by
    rw [(rows (2 * (r / 2) + 1) (by omega)).1, jF, show (2 * (r / 2) + 1) % 2 = 1 by omega]; rfl
  obtain ⟨-, blk, -, h16, -, wb, -, e0, e1, -⟩ := cut_groupS H hC cuti_hT (g := r / 2) (by omega) j0 j1
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
theorem cuti_lateS {N : Nat} (hN : 2 * N + 2 ≤ tr.height 30) (hp0 : kc tr 30 (2 * N) 3 = 1)
    (hp1 : kc tr 30 (2 * N + 1) 3 = 1) (hj1 : kc tr 30 (2 * N + 1) 1 = 1) :
    ∀ r, r < tr.height 30 → 2 * N ≤ r → rowNat tr 30 r 0 = 0 := by
  have hcs : Cut.In.cols = Cut.In.cols ∨ Cut.In.cols = Cut.Out.cols := Or.inl rfl
  have hC' := cuti_CS H
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
    · exact (cuti_bitsS H hr).2.1 hp0
    · exact (cuti_bitsS H hr).2.1 hp1
    · exact (cuti_bitsS H hr).2.2.1 (dead r hr h)
  have := (cuti_bitsS H hr).2.2.2.2 hkD
  show (kc tr 30 r 0).toNat = 0
  rw [this]; rfl

include H in
theorem cuti_N_uniqueS {N N' : Nat} (hN : 2 * N + 2 ≤ tr.height 30) (hd : ∀ r, r < 2 * N → kc tr 30 r 2 = 1)
    (hp : kc tr 30 (2 * N) 3 = 1) (hN' : 2 * N' + 2 ≤ tr.height 30) (hd' : ∀ r, r < 2 * N' → kc tr 30 r 2 = 1)
    (hp' : kc tr 30 (2 * N') 3 = 1) : N = N' := by
  rcases Nat.lt_trichotomy N N' with h | h | h
  · exfalso
    have := (cuti_bitsS H (r := 2 * N) (by omega)).2.2.2.1 (hd' (2 * N) (by omega))
    rw [hp] at this; exact f_one_ne_zero this
  · exact h
  · exfalso
    have := (cuti_bitsS H (r := 2 * N') (by omega)).2.2.2.1 (hd (2 * N') (by omega))
    rw [hp'] at this; exact f_one_ne_zero this

include H hC in
/-- **A CUTI data row, decoded from its words**: it is active iff its block's mark is 1, and then its
7 produced fields are `decFs` of its words. -/
theorem cuti_row_decS {N : Nat} (hN : 2 * N + 2 ≤ tr.height 30) (hd : ∀ r, r < 2 * N → kc tr 30 r 2 = 1)
    (hp : kc tr 30 (2 * N) 3 = 1) {r : Nat} (hr : r < 2 * N) :
    (rowNat tr 30 r 0 = 1 ↔ markOf (streamW tr pub 30 Cut.In.cols r) = 1) ∧
      (rowNat tr 30 r 0 = 1 → cutiRow tr r = decFs (streamW tr pub 30 Cut.In.cols r)) := by
  have hP := P_val
  have W := cuti_data_wFS H hC hN hd hp r hr
  have hkP : kc tr 30 r 3 = 0 := (cuti_bitsS H (r := r) (by omega)).2.2.2.1 (hd r hr)
  have hab := (cuti_bitsS H (r := r) (by omega)).1
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

include H hC in
/-- **CUTI's digest and productions as a function of its hashed words** (item 1).  There are 8-word
blocks `B` (one per data row, all words `< 2^64`) such that the public `ctx_in` limbs are those of a
digest `d` with `wbytes d = sha384 (wbytes B.flatten)` (FIPS 180-4 SHA-384 of the concatenated words),
and CUTI's CH productions are, in row order, `ofFields (decFs b) t_in` for the blocks `b` with mark 1. -/
theorem cuti_streamS :
    ∃ B : List (List Nat), (∀ b ∈ B, b.length = 8 ∧ StateM5a.Sha512If.W64 b) ∧
      (∃ d : List Nat, d.length = 6 ∧ StateM5a.Sha512If.W64 d ∧ pubDig pub pubCtxIn = limbsF d ∧
        wbytes d = NearSpecV3.E2E.Bnd.sha384 (wbytes B.flatten)) ∧
      (part Cut.In.table tr pub 30 busStk true).map decMsg =
        (B.filter (fun b => markOf b = 1)).map (fun b => ofFields (decFs b) (pub.getD pubTIn 0).toNat) := by
  obtain ⟨N, hN, hd, hp, hw, d, h6, hW, hpub, hsha⟩ := cut_stream_digestS H hC cuti_hT
  have hcs : Cut.In.cols = Cut.In.cols ∨ Cut.In.cols = Cut.Out.cols := Or.inl rfl
  obtain ⟨N', hN', hd', hp0', hp1', rows, -, -⟩ := cut_rows hcs (cuti_CS H) (H.heightPos 30 (cutT_lt cuti_hT))
  have eN := cuti_N_uniqueS H hN hd hp hN' hd' hp0'
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
      have := cuti_lateS H hN hp hp1' hj1 r h2 h1; simp [this])]
    have hf : (List.range (2 * N)).filter (fun r => decide (rowNat tr 30 r 0 = 1)) =
        (List.range (2 * N)).filter ((fun b => decide (markOf b = 1)) ∘ streamW tr pub 30 Cut.In.cols) :=
      List.filter_congr (fun r hr => by
        rw [Function.comp_apply]
        exact decide_eq_decide.mpr (cuti_row_decS H hC hN hd hp (List.mem_range.mp hr)).1)
    simp only [B]
    rw [List.filter_map, List.map_map, ← hf]
    apply List.map_congr_left
    intro r hr
    obtain ⟨hr1, hr2⟩ := List.mem_filter.mp hr
    have := (cuti_row_decS H hC hN hd hp (List.mem_range.mp hr1)).2 (by simpa using hr2)
    simp only [Function.comp, this]

end

/-- **CR decoding (item 2).**  If the public `ctx_in` is the digest `cutDigest L` of a list of
well-formed messages, then SHA-384 collides, or CUTI's CH productions are exactly the entries of `L`
in order, each as a message at `t_in`. -/
theorem cuti_viewS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    {chip : List StateM5a.Sha512If.IfMsg} (hC : SegSha.ChipIfS compressW nloc ngl pub tr chip)
    {L : List (List Nat)} (hL : ∀ y ∈ L, MsgWF y) (hpub : PubDigIs pub pubCtxIn (cutDigest L)) :
    NearSpecV3.E2E.Bnd.Sha384Coll ∨
      (part Cut.In.table tr pub 30 busStk true).map decMsg = L.map (fun y => ofFields y (pub.getD pubTIn 0).toNat) := by
  obtain ⟨B, hB, ⟨d, h6, hW, hpd, hsha⟩, hprod⟩ := cuti_streamS H hC
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

section
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
include H

/-- A MEMB row whose byte sends fire (`kD = 1`) is an active data row. -/
theorem memb_kD_oneS {r : Nat} (hr : r < tr.height 19) (h : (Memb.kD.eval (tr.row pub 19 r)).toNat = 1) :
    mbN tr r 0 = 1 ∧ r % 9 < 8 := by
  have hP := P_val
  obtain ⟨ha, bp, hs⟩ := memb_rowS H hr
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
  have hp := (memb_posS H r hr ha1).2
  refine Classical.byContradiction fun hq => ?_
  have h8 : r % 9 = 8 := by have := Nat.mod_lt r (show 9 > 0 by decide); omega
  rw [h8] at hp
  have : mbN tr r 9 = 1 := hp
  omega

/-- The address of byte `i` on an active data row. -/
theorem memb_data_addrS {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 < 8) (i : Nat) :
    (Memb.addr i).eval (tr.row pub 19 r) = ((1024 * mbN tr r 10 + 128 * (r % 9) + i : Nat) : F) := by
  have hp := (memb_posS H r hr ha).2
  obtain ⟨k, hkdef⟩ : ∃ k, k = r % 9 := ⟨_, rfl⟩
  rw [← hkdef] at hp hq ⊢
  have oh : ∀ j, j < 9 → mbN tr r (1 + j) = if j = k then 1 else 0 := by
    intro j hj
    by_cases hjk : j = k
    · subst hjk; simpa using hp
    · rw [if_neg hjk]; exact memb_onehotS H hr (k := k) (by omega) hj (Ne.symm hjk) hp
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
theorem memb_nextS {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 < 8) :
    r + 1 < tr.height 19 ∧ mbN tr (r + 1) 0 = 1 := by
  have hP := P_val
  have hp := (memb_posS H r hr ha).2
  have hm : r % 9 < 9 := Nat.mod_lt _ (by decide)
  have hp8 : mbN tr r (1 + 8) = 0 := memb_onehotS H hr (k := r % 9) (j := 8) hm (by decide) (by omega) hp
  have hr1 : r + 1 < tr.height 19 := by
    refine Classical.byContradiction fun hn => ?_
    have hl : r + 1 = tr.height 19 := by omega
    have h := memb_CS H hr (Expr.last * Memb.c "act" * (1 - Memb.p 8)) (by simp [Memb.constraints])
    simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_c_eval, mb_ix.1,
      memb_p_eval tr pub r (show 8 < 9 by decide), ha, hp8, sel_last (t := 19) (tr := tr) (pub := pub) hl] at h
    exact absurd h (by decide)
  refine ⟨hr1, ?_⟩
  have hmem : Expr.trans * Memb.p (r % 9) * (1 - nv (ix Memb.cols s!"p{r % 9 + 1}")) ∈ Memb.constraints := by
    unfold Memb.constraints
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))))))
    exact List.mem_map.mpr ⟨r % 9, List.mem_range.mpr hq, rfl⟩
  have h := memb_CS H (r := r) hr _ hmem
  rw [mb_ix_p (r % 9 + 1) (by omega)] at h
  simp only [Expr.eval_mul', Expr.eval_sub', Expr.eval_ofNat', memb_p_eval tr pub r hm, nv,
    Expr.eval_nxt, trans_eval_one tr pub 19 r hr1, hp, cast_one] at h
  simp only [Trace.row, Nat.mod_eq_of_lt hr1, cell_cast] at h
  have hq1 : mbN tr (r + 1) (1 + (r % 9 + 1)) = 1 :=
    natEq (R := 1) (by rw [cast_one]; grind) (rowNat_lt _ _ _ _) (by rw [P_val]; decide)
  obtain ⟨ha', bp', hs'⟩ := memb_rowS H hr1
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
theorem memb_completeS : ∀ j r, 8 - r % 9 = j → r < tr.height 19 → mbN tr r 0 = 1 →
    9 * (r / 9) + 8 < tr.height 19 ∧ mbN tr (9 * (r / 9) + 8) 0 = 1
  | 0, r, hj, hr, ha => by
    have : r = 9 * (r / 9) + 8 := by have := Nat.mod_lt r (show 9 > 0 by decide); omega
    rw [← this]; exact ⟨hr, ha⟩
  | j + 1, r, hj, hr, ha => by
    have hq : r % 9 < 8 := by omega
    obtain ⟨hr1, ha1⟩ := memb_nextS H hr ha hq
    have e1 : (r + 1) / 9 = r / 9 := by omega
    have := memb_completeS j (r + 1) (by omega) hr1 ha1
    rwa [e1] at this

/-- The padding row's `blk` is below `2^16` (R16 on `blk`, count `p8`). -/
theorem memb_blk_ltS {b : Nat} (hr : 9 * b + 8 < tr.height 19) (ha : mbN tr (9 * b + 8) 0 = 1) :
    mbN tr (9 * b + 8) 10 < 65536 := by
  have ht : 19 < (wasmBaseSegAir nloc ngl).tables.length := by simp [seg_air_len]
  have hp8 : mbN tr (9 * b + 8) (1 + 8) = 1 := by
    have := (memb_posS H _ hr ha).2; rwa [show (9 * b + 8) % 9 = 8 by omega] at this
  have mem : r16 (Memb.c "blk") (Memb.p 8) ∈ ((wasmBaseSegAir nloc ngl).tables[19]'ht).inters := by
    rw [seg_t19]
    show _ ∈ Memb.inters
    unfold Memb.inters
    refine List.mem_append_right _ ?_
    simp
  have h := seg_r16_ltS H (seg_hsend_r16S H) ht hr mem (by rw [memb_p_eval tr pub _ (by decide), hp8]; decide)
  simpa only [memb_c_eval, mb_ix.2.1, Fp.toNat_cast_of_lt (rowNat_lt _ _ _ _)] using h

/-- The decoded address of byte `i` of an active data row, through its block's padding row. -/
theorem memb_slotS {r : Nat} (hr : r < tr.height 19) (ha : mbN tr r 0 = 1) (hq : r % 9 < 8) {i : Nat} (hi : i < 128) :
    (decMsg (membMsg tr pub r i)).slot = 1024 * mbN tr (9 * (r / 9) + 8) 10 + 128 * (r % 9) + i ∧
      mbN tr (9 * (r / 9) + 8) 10 < 65536 ∧ 9 * (r / 9) + 8 < tr.height 19 ∧ mbN tr (9 * (r / 9) + 8) 0 = 1 := by
  have hP := P_val
  obtain ⟨hc, hca⟩ := memb_completeS H _ r rfl hr ha
  have hlt := memb_blk_ltS H hc hca
  have hk := memb_blk_constS H (b := r / 9) hc hca (r % 9) (by omega)
  rw [show 9 * (r / 9) + r % 9 = r by omega] at hk
  refine ⟨?_, hlt, hc, hca⟩
  rw [membMsg_slot, memb_data_addrS H hr ha hq, hk, Fp.toNat_cast_of_lt (by omega)]

/-- **MEMB's in-side productions are duplicate-free.** -/
theorem memb_part_nodupS : ((part Memb.table tr pub 19 busStk true).map decMsg).Nodup := by
  rw [memb_part, List.map_flatMap]
  refine nodup_flatMap_of _ _ (fun r hr => ?_) ?_
  · split
    · rename_i hk
      obtain ⟨ha, hq⟩ := memb_kD_oneS H (List.mem_range.mp hr) hk
      rw [List.map_map]
      refine nodup_map_range 128 _ (fun i j hi hj e => ?_)
      have := congrArg Msg.slot e
      simp only [Function.comp] at this
      rw [(memb_slotS H (List.mem_range.mp hr) ha hq hi).1, (memb_slotS H (List.mem_range.mp hr) ha hq hj).1] at this
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
        obtain ⟨ha, hq⟩ := memb_kD_oneS H hr0 hk
        obtain ⟨ha', hq'⟩ := memb_kD_oneS H hr0' hk'
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (by simpa only [List.map_map] using hx)
        obtain ⟨i', hi', e⟩ := List.mem_map.mp (by simpa only [List.map_map] using hx')
        have hs := congrArg Msg.slot e
        simp only [Function.comp] at hs
        obtain ⟨s1, l1, c1, a1⟩ := memb_slotS H hr0 ha hq (List.mem_range.mp hi)
        obtain ⟨s2, l2, c2, a2⟩ := memb_slotS H hr0' ha' hq' (List.mem_range.mp hi')
        rw [s1, s2] at hs
        have hii := List.mem_range.mp hi
        have hii' := List.mem_range.mp hi'
        obtain ⟨eb, ek, -⟩ := memb_addr_inj hq' hq hii' hii hs
        by_cases hb : r' / 9 = r / 9
        · omega
        · exact memb_blk_distinct_of_holdsS H hb c2 c1 a2 a1 eb
      · simp at hx'
    · simp at hx

end

/-- **The in-boundary block is duplicate-free** (item 3), given CUTI's productions as a list `L` of
well-formed, distinct messages outside spaces 3 and 7 (item 2 gives `L = cutView X s`). -/
theorem initS_nodup_ofS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    {L : List (List Nat)}
    (hc : (part Cut.In.table tr pub 30 busStk true).map decMsg = L.map (fun y => ofFields y (pub.getD pubTIn 0).toNat))
    (hL : L.Nodup) (hwf : ∀ y ∈ L, MsgWF y) (hsp : ∀ y ∈ L, y.getD 0 0 ≠ 3 ∧ y.getD 0 0 ≠ 7) :
    (initS tr pub).Nodup := by
  have h0 : 1 ≤ tr.height 0 := seg_h0S H
  unfold initS
  rw [hc, segb_part tr pub h0, List.nodup_append, List.nodup_append]
  refine ⟨nodup_map_of_inj _ L hL (fun a ha b hb e => ?_), ⟨memb_part_nodupS H, by simp, ?_⟩, ?_⟩
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

/-- **`(initS tr pub).Nodup` at a view boundary** (item 3): CUTI produces `cutView X s` (item 2),
`RegWF s`, the view `MsgWF`. -/
theorem initS_nodupS {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsXS nloc ngl pub tr)
    {X : Ctx} {s : St} (hw : RegWF s) (hwf : ∀ y ∈ cutView X s, MsgWF y)
    (hc : (part Cut.In.table tr pub 30 busStk true).map decMsg =
      (cutView X s).map (fun y => ofFields y (pub.getD pubTIn 0).toNat)) :
    (initS tr pub).Nodup :=
  initS_nodup_ofS H hc (cutView_nodup X hw) hwf (fun y hy => cutView_sp hy)

end Cuti

end WasmBase
