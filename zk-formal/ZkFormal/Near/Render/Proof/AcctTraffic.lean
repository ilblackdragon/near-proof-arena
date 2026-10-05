import ZkFormal.Near.Render.Proof.AcctFacts
import ZkFormal.Near.Render.Proof.SortLocal

/-!
# ZkFormal.Near.Render.Proof.AcctTraffic — `AcctTrafficStmt`

Lane `i` of the segment of slot `k` sends the `VPRE(k)`/`VPOST(k)` bytes at
positions `posOf i = {i, 16+i, 32+2i, 33+2i} (∪ {64+i} if i < 8)` (these
partition `[0, 72)`), one `MEM` write and read, and (lane 0) `VSLOT (k)`.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace AcctTraffic
open SortLocal (ofNat0 ofNat1)

def posOf (i : Nat) : List Nat := [i, 16 + i, 32 + 2 * i, 33 + 2 * i] ++ (if i < 8 then [64 + i] else [])

theorem posOf_perm : ((List.range 16).flatMap posOf).Perm (List.range 72) := by decide

/-- The byte messages of `VPRE`/`VPOST` at position `p`. -/
def bmsg (kind k p x : Nat) : List Fp := [Fp.ofNat (kind + 16 * k), Fp.ofNat p, Fp.ofNat x]

variable (I : Info)

/-- Traffic of lane `i` of slot `k`. -/
def rowK (k i b : Nat) (s : Bool) : List (List Fp) :=
  let v := I.vpre.getD k []
  let w := I.vpost.getD k []
  if b = B_BYTES ∧ s = true then
    (posOf i).map (fun p => bmsg K_VPRE k p (v.getD p 0)) ++
      (posOf i).map (fun p => bmsg K_VPOST k p (if p < 16 then w.getD p 0 else v.getD p 0))
  else if b = B_MEM ∧ s = true then
    [[Fp.ofNat k, Fp.ofNat 0, Fp.ofNat i, Fp.ofNat (v.getD i 0), Fp.ofNat (v.getD (16 + i) 0),
      Fp.ofNat (if i < 8 then v.getD (64 + i) 0 else 0)]]
  else if b = B_MEM ∧ s = false then
    [[Fp.ofNat k, Fp.ofNat (tlastOf I.e k), Fp.ofNat i, Fp.ofNat (w.getD i 0), Fp.ofNat (v.getD (16 + i) 0),
      Fp.ofNat (if i < 8 then v.getD (64 + i) 0 else 0)]]
  else if b = B_VSLOT ∧ s = true then (if i = 0 then [[Fp.ofNat k]] else [])
  else []

/-- Traffic of an active row `q` (lane `q % 16` of slot `kOf q`). -/
def rowA (q b : Nat) (s : Bool) : List (List Fp) := rowK I (AcctGen.kOf I q) (q % 16) b s

section
variable {I} {tr : Trace Fp} {pub : List Fp} {H : Nat}
  (hcell : ∀ q col, q < H → col < 16 → tr.cell T_ACCT q col = Fp.ofNat (AcctGen.cell I q col))
include hcell

theorem row {q : Nat} (hq : q < H) (b : Nat) (s : Bool) :
    rowTraffic Acct.interactions tr T_ACCT q pub b s =
      if q < 16 * I.touched.length then rowA I q b s else [] := by
  have hc : ∀ col, col < 16 → tr.cell T_ACCT q col = Fp.ofNat (AcctGen.cell I q col) :=
    fun col h => hcell q col hq h
  simp only [rowTraffic, Acct.interactions, Acct.vbytes, send, recv, List.cons_append, List.nil_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, multNat_one, Interaction.msgVal, List.map_cons,
    List.map_nil, eval_c, eval_mid, eval_add, eval_k, eval_smul, Acct.act, Acct.af, Acct.gS, Acct.kk, Acct.i,
    Acct.amt, Acct.post, Acct.lk, Acct.st, Acct.ch0, Acct.ch1, Acct.tlast, hc, Nat.reduceLT, natCast_eq,
    ofNat_mul', ofNat_add']
  by_cases ha : q < 16 * I.touched.length
  · simp only [AcctGen.cell, ha, if_true, AcctGen.actCell, rowA, rowK, posOf, bmsg, ofNat1, msgId]
    have hi : q % 16 < 16 := Nat.mod_lt _ (by omega)
    have f1 : ¬ 16 + q % 16 < 16 := by omega
    have f2 : ¬ 32 + 2 * (q % 16) < 16 := by omega
    have f3 : ¬ 33 + 2 * (q % 16) < 16 := by omega
    have f4 : ¬ 64 + q % 16 < 16 := by omega
    rcases (show b = 0 ∨ b = 3 ∨ b = 7 ∨ (b ≠ 0 ∧ b ≠ 3 ∧ b ≠ 7) by omega) with rfl | rfl | rfl | ⟨h0, h3, h7⟩ <;>
    cases s <;> by_cases hz : q % 16 = 0 <;> by_cases h8 : q % 16 < 8 <;>
    simp [B_BYTES, B_MEM, B_VSLOT, ofNat1, ofNat0, hz, h8, hi, f1, f2, f3, f4, fp_zero_ne_one, *] <;> omega
  · simp only [AcctGen.cell, ha, if_false, ofNat0]
    simp [fp_zero_ne_one]

end

/-! ## segments -/

theorem take_drop_getD {w v : List Nat} (hw : 16 ≤ w.length) (p : Nat) :
    (w.take 16 ++ v.drop 16).getD p 0 = if p < 16 then w.getD p 0 else v.getD p 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_take]; simp [*]
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop]
    simp only [List.length_take, Nat.min_eq_left hw]
    congr 2; omega

theorem acctSends_flat (as : List AcctV) (b : Nat) :
    acctSends as b = as.flatMap fun a => acctSends [a] b := by
  simp only [acctSends]
  split
  · simp
  · split
    · simp
    · split
      · exact (flatMap_single (fun _ _ => rfl)).symm
      · simp

theorem acctRecvs_flat (as : List AcctV) (b : Nat) :
    acctRecvs as b = as.flatMap fun a => acctRecvs [a] b := by
  simp only [acctRecvs]
  split
  · simp
  · simp

/-- The view of slot `k`. -/
def viewK (k : Nat) : AcctV := ⟨k, tlastOf I.e k, I.vpre.getD k [], (I.vpost.getD k []).take 16⟩

section seg
variable {I} {k : Nat} (hv : (I.vpre.getD k []).length = 72) (hw : (I.vpost.getD k []).length = 72)
include hv hw

theorem seg_bytes :
    ((List.range 16).flatMap fun i => rowK I k i B_BYTES true).Perm
      ((acctSends [viewK I k] B_BYTES).map Msg.toFp) := by
  simp only [rowK, and_self, if_true]
  refine (perm_flatMap_append _ _ _).trans ?_
  simp only [acctSends, if_true, viewK, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append]
  rw [← List.map_flatMap, ← List.map_flatMap]
  refine List.Perm.append ?_ ?_
  · refine (posOf_perm.map _).trans (List.Perm.of_eq ?_)
    simp only [emitAt, hv, List.map_map]
    apply List.map_congr_left; intro p _
    simp [bmsg, Msg.toFp, msgId]
  · refine (posOf_perm.map _).trans (List.Perm.of_eq ?_)
    simp only [emitAt, List.length_append, List.length_take, List.length_drop, hv, hw, List.map_map]
    apply List.map_congr_left; intro p _
    simp only [Function.comp_apply]
    rw [take_drop_getD (show 16 ≤ (I.vpost.getD k []).length by omega)]
    simp [bmsg, Msg.toFp, msgId]

theorem seg_memS :
    ((List.range 16).flatMap fun i => rowK I k i B_MEM true).Perm
      ((acctSends [viewK I k] B_MEM).map Msg.toFp) := by
  apply List.Perm.of_eq
  simp only [rowK, B_MEM, B_BYTES, B_VSLOT, Nat.reduceEqDiff, false_and, and_self, if_false, if_true]
  rw [flatMap_single (fun _ _ => rfl)]
  simp only [acctSends, B_MEM, B_BYTES, Nat.reduceEqDiff, if_false, if_true, viewK, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.map_map]
  apply List.map_congr_left; intro i _
  simp [Msg.toFp, acctLane]

theorem seg_memR :
    ((List.range 16).flatMap fun i => rowK I k i B_MEM false).Perm
      ((acctRecvs [viewK I k] B_MEM).map Msg.toFp) := by
  apply List.Perm.of_eq
  simp only [rowK, B_MEM, B_BYTES, B_VSLOT, Nat.reduceEqDiff, false_and, and_false, Bool.false_eq_true,
    and_self, if_false, if_true]
  rw [flatMap_single (fun _ _ => rfl)]
  simp only [acctRecvs, B_MEM, if_true, viewK, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
  apply List.map_congr_left; intro i hi
  have := List.mem_range.1 hi
  simp [Msg.toFp, acctLane, List.getD_eq_getElem?_getD, List.getElem?_take, this]

theorem seg_vslot :
    ((List.range 16).flatMap fun i => rowK I k i B_VSLOT true).Perm
      ((acctSends [viewK I k] B_VSLOT).map Msg.toFp) := by
  apply List.Perm.of_eq
  simp [rowK, acctSends, viewK, B_VSLOT, B_BYTES, B_MEM, List.range, List.range.loop, Msg.toFp]

theorem segS (b : Nat) :
    ((List.range 16).flatMap fun i => rowK I k i b true).Perm ((acctSends [viewK I k] b).map Msg.toFp) := by
  rcases (show b = B_BYTES ∨ b = B_MEM ∨ b = B_VSLOT ∨ (b ≠ B_BYTES ∧ b ≠ B_MEM ∧ b ≠ B_VSLOT) by
    simp only [B_BYTES, B_MEM, B_VSLOT]; omega) with rfl | rfl | rfl | ⟨h0, h7, h3⟩
  · exact seg_bytes hv hw
  · exact seg_memS hv hw
  · exact seg_vslot hv hw
  · apply List.Perm.of_eq
    simp [rowK, acctSends, h0, h7, h3]

theorem segR (b : Nat) :
    ((List.range 16).flatMap fun i => rowK I k i b false).Perm ((acctRecvs [viewK I k] b).map Msg.toFp) := by
  by_cases h7 : b = B_MEM
  · subst h7; exact seg_memR hv hw
  · apply List.Perm.of_eq
    simp [rowK, acctRecvs, h7]

end seg

end AcctTraffic

open AcctTraffic in
/-- **`AcctTrafficStmt`.** -/
theorem acctTraffic_ok : AcctTrafficStmt := by
  intro c e hg
  have hp : partOf (bundle c.1 e) T_ACCT =
      mkTab (2 ^ logOf (16 * (mkInfo c.1 e).touched.length)) Acct.width (AcctGen.cell (mkInfo c.1 e)) := rfl
  obtain ⟨_, hH, hcell⟩ := render_mkTab (by decide) (by decide) hp
  have hpre := acct_pre hg
  have hpost := acct_post hg
  have htf : htf c.1 e T_ACCT = acctTraffic ((mkInfo c.1 e).touched.map (viewK (mkInfo c.1 e))) := rfl
  rw [htf]
  generalize mkInfo c.1 e = I at hp hH hcell hpre hpost
  have hle : 16 * I.touched.length ≤ 2 ^ logOf (16 * I.touched.length) := le_pow_logOf _
  have hcell' : ∀ q col, q < 2 ^ logOf (16 * I.touched.length) → col < 16 →
      (render c.1 e).cell T_ACCT q col = Fp.ofNat (AcctGen.cell I q col) := fun q col hq hc => hcell q col hq hc
  -- rows → segments
  have hrows : ∀ b s, ((List.range ((render c.1 e).height T_ACCT)).flatMap fun r =>
      rowTraffic Acct.interactions (render c.1 e) T_ACCT r (publicOf c) b s) =
      (List.range I.touched.length).flatMap fun t => (List.range 16).flatMap fun i =>
        rowK I (I.touched.getD t 0) i b s := by
    intro b s
    rw [hH, range_split hle, List.flatMap_append,
      flatMap_nil' (l := List.map _ _) (fun q hq => by
        obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        have := List.mem_range.1 hq'
        rw [row hcell' (by omega), if_neg (by omega)]),
      List.append_nil, range_flatMap_chunks 16 _ I.touched.length]
    apply flatMap_congr'; intro t ht
    apply flatMap_congr'; intro i hi
    have ht' := List.mem_range.1 ht; have hi' := List.mem_range.1 hi
    rw [row hcell' (by omega), if_pos (by omega)]
    simp only [rowA, AcctGen.kOf]
    rw [show (16 * t + i) / 16 = t by omega, show (16 * t + i) % 16 = i by omega]
  have hmem : ∀ t ∈ List.range I.touched.length, I.touched.getD t 0 ∈ I.touched := by
    intro t ht
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.mem_range.1 ht), Option.getD_some]
    exact List.getElem_mem _
  apply traffic_of
  · intro b
    rw [hrows]; dsimp only [acctTraffic]; rw [acctSends_flat, List.flatMap_map, flatMap_getD 0 I.touched, List.map_flatMap]
    exact perm_flatMap_congr fun t ht =>
      segS (hpre _ (hmem t ht)).1 (hpost _ (hmem t ht)) b
  · intro b
    rw [hrows]; dsimp only [acctTraffic]; rw [acctRecvs_flat, List.flatMap_map, flatMap_getD 0 I.touched, List.map_flatMap]
    exact perm_flatMap_congr fun t ht =>
      segR (hpre _ (hmem t ht)).1 (hpost _ (hmem t ht)) b

end ZkFormal.Near.Render
