import M5T1.ShSem

/-!
# M5T1.SeOpen — what `SE`'s opening rows establish, as bytes (F-7)

On every satisfying trace of the STATE engine half (`Se.fullSe xtape`, stand-in tape premises,
lane B's chip contract `ShDef.ChipOK`), with `SE` row 0's byte strings `cb tr s w` (`dS`, `dQ`,
`dM`, … the opened / closed remainder parts, `rsi` = `STMA`'s `rest_in`, `rso` = `STMQ`'s
`rest_out`) and `serIn tr` (`tag_in ‖ ws ‖ wsLen ‖ trie ‖ idx ‖ rest_in`, lane B's
`StCommit.ser` of the opening), **`se_open`** gives (`SeOpenOK`):

* `bdigest (serIn tr) = B_in.stRoot` — the opening is of the input record's `stRoot`;
* `bdigest (dS ‖ dQ ‖ dM) = rest_in`, `bdigest (dS' ‖ dQ' ‖ dM') = rest_out` (`encRestI` in / out);
* `dM` and `dM'` are chained SHA-384 digests of byte messages **in the trace** (the `d_move`
  preimages, `SH` runs `hid` 6 / 7; their content is the residual step contract's);
* `fin = 1` (the finalize step): `tag_in = 8`, `tag_out = 3`, `dQ' = dQ`, `bdigest (dK ‖ dSh) = dS`,
  `bdigest (dK ‖ dShN) = dS'`, `bdigest [0] = dShN` (`Ser.enc none`); `fin = 0`: `dS' = dS`;
  `tag_in < 255`.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace M5T1.SeOpen

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View M5T1 M5T1.Bus M5T1.MsgRow
open M5T1.ShDef M5T1.ShSem M5T1.SegRt NearSpecV3.E2E.Bnd
open M5T1.AccDef (chainDig chainDig_pad)
open M5T1.AccSem (evAdd evMul evSub evK evOne evZero evFirst0 evFirstS evTrans evPub gate_eq bool_le NoRecvOn)

abbrev Bytes := ArenaCore.Bytes

/-- `SE` row 0's cell `s.j`. -/
def col (tr : Trace Fp) (s : String) (j : Nat := 0) : Nat := nv tr 0 0 (Se.L.off s + j)

/-- `SE` row 0's `w` bytes of group `s`. -/
def cb (tr : Trace Fp) (s : String) (w : Nat := 42) : Bytes := (List.range w).map fun j => UInt8.ofNat (col tr s j)

/-- The opening's 139 bytes (lane B's `StCommit.ser`). -/
def serIn (tr : Trace Fp) : Bytes :=
  [UInt8.ofNat (col tr "tgi")] ++ cb tr "wsi" 48 ++ cb tr "wli" 8 ++ cb tr "tri" 32 ++ cb tr "ixi" 8 ++ cb tr "rsi"

/-- **What `SE`'s opening rows establish** (module doc). -/
def SeOpenOK (pub : List Fp) (tr : Trace Fp) : Prop :=
  bdigest (serIn tr) = bytesOf pub (BndLay.engF.off "stRoot") 42 ∧ col tr "tgi" < 255 ∧
  bdigest (cb tr "dS" ++ cb tr "dQ" ++ cb tr "dM") = cb tr "rsi" ∧
  bdigest (cb tr "dSo" ++ cb tr "dQo" ++ cb tr "dMo") = cb tr "rso" ∧
  (∃ m : List Nat, m.length % 128 = 0 ∧ 0 < m.length ∧ (∀ x ∈ m, x < 256) ∧ chainDig m = cb tr "dM") ∧
  (∃ m : List Nat, m.length % 128 = 0 ∧ 0 < m.length ∧ (∀ x ∈ m, x < 256) ∧ chainDig m = cb tr "dMo") ∧
  (col tr "fin" = 1 → col tr "tgi" = 8 ∧ col tr "tgo" = 3 ∧ cb tr "dQo" = cb tr "dQ" ∧
    bdigest (cb tr "dK" ++ cb tr "dSh") = cb tr "dS" ∧ bdigest (cb tr "dK" ++ cb tr "dShN") = cb tr "dSo" ∧
    bdigest [0] = cb tr "dShN") ∧
  (col tr "fin" ≠ 1 → cb tr "dSo" = cb tr "dS")

/-! ## Padding -/

theorem beN_map : ∀ (w x : Nat), (ArenaCore.Bytes.beN w x).map UInt8.toNat =
    (List.range w).map fun i => x / 256 ^ (w - 1 - i) % 256
  | 0, _ => rfl
  | w + 1, x => by
    rw [ArenaCore.Bytes.beN, List.map_append, beN_map w (x / 256), List.range_succ (n := w), List.map_append]
    congr 1
    · apply List.map_congr_left
      intro i hi
      have hi := List.mem_range.1 hi
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ', show w + 1 - 1 - i = (w - 1 - i) + 1 by omega]
    · simp

section
variable {tr : Trace Fp} {pub : List Fp}

/-- **`padE` evaluates to the spec's SHA-512 padding** of the message's bytes. -/
theorem padE_eval (m : List Expr) (hm : ∀ e ∈ m, ev tr 0 0 pub e < 256) :
    (Se.padE m).map (ev tr 0 0 pub) =
      NearSpecV3.SHA512.pad ((m.map fun e => UInt8.ofNat (ev tr 0 0 pub e)).map UInt8.toNat) := by
  have hmm : (m.map fun e => UInt8.ofNat (ev tr 0 0 pub e)).map UInt8.toNat = m.map (ev tr 0 0 pub) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro e he
    simp only [Function.comp, UInt8.toNat_ofNat]
    exact Nat.mod_eq_of_lt (hm e he)
  rw [hmm]
  simp only [Se.padE, NearSpecV3.SHA512.pad, List.map_append, List.length_map, List.map_cons, List.map_nil,
    List.map_replicate, beN_map, List.map_map]
  congr 2
  funext i
  simp only [Function.comp, evK]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
end

/-! ## The opening -/

section
variable {xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (Se.fullSe xtape) pub tr)
  (hr2 : NoRng xtape) (hi2 : NoSendOn B_IF384 xtape) (hC : ChipOK tr)
  (hd : NoRecvOn B_SHD xtape) (hb : NoSendOn B_SHB xtape)
include H hr2 hi2 hC hd hb

/-- A fixed hash of `SE`, as `bdigest` of its evaluated message. -/
theorem fixed_dig {s : Se.HSpec} (hs : s ∈ Se.hashes) (hfx : s.fx = true) (hm : ev tr 0 0 pub s.mul = 1) :
    bdigest (s.msg.map fun e => UInt8.ofNat (ev tr 0 0 pub e)) = digOf pub tr s := by
  obtain ⟨m, -, -, -, hfm, hdg⟩ := sh_sound H hr2 hi2 hC hd hb s hs hm
  rw [← hdg, hfm hfx, padE_eval _ (se_msg_lt H hr2 s hs), chainDig_pad]

/-- A witnessed hash of `SE`: some byte message in the trace has the digest. -/
theorem wit_dig {s : Se.HSpec} (hs : s ∈ Se.hashes) (hm : ev tr 0 0 pub s.mul = 1) :
    ∃ m : List Nat, m.length % 128 = 0 ∧ 0 < m.length ∧ (∀ x ∈ m, x < 256) ∧ chainDig m = digOf pub tr s := by
  obtain ⟨m, h1, h2, h3, -, h5⟩ := sh_sound H hr2 hi2 hC hd hb s hs hm
  exact ⟨m, h1, h2, h3, h5⟩

end

section
variable {pub : List Fp} {tr : Trace Fp}

theorem gate0 (e : Expr) : ev tr 0 0 pub (BndLay.gate e) = ev tr 0 0 pub e := by
  simp only [BndLay.gate, evMul, evFirst0, Nat.one_mul]; exact Nat.mod_eq_of_lt (ev_lt _)

@[simp] theorem colv (s : String) (j : Nat) : ev tr 0 0 pub (Se.c s j) = col tr s j := rfl

theorem col_lt (s : String) (j : Nat) : col tr s j < 2013265921 := Fp.toNat_lt _

theorem h0p : 0 < tr.height 0 := by unfold Trace.height; exact Nat.two_pow_pos _
end

section
variable {xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (Se.fullSe xtape) pub tr)
include H

theorem c7 {e : Expr} (he : e ∈ Se.cons7) : ev tr 0 0 pub e = 0 :=
  ev_of_eval (H.constr 0 se_lt 0 h0p e (List.mem_append_right _ he))

theorem fin_le : col tr "fin" ≤ 1 := by
  have h := c7 H (e := BndLay.gate (bool (Se.c "fin"))) (by simp [Se.cons7])
  rw [gate0] at h
  exact bool_le (tr := tr) (t := 0) (r := 0) (pub := pub) (x := Se.c "fin") h

/-- `fin = 1 ⇒ a = v` from a gated `fin · (a − v)` constraint (`v < p`). -/
theorem fin_const {a : String} {v : Nat} (hv : v < 2013265921) (hf : col tr "fin" = 1)
    (hm : BndLay.gate (Se.c "fin" * (Se.c a - .const v)) ∈ Se.cons7) : col tr a = v := by
  have h := c7 H hm
  rw [gate0] at h
  simp only [evMul, evSub, ev_const, colv, hf, Nat.one_mul] at h
  have := col_lt (tr := tr) a 0
  have e : col tr a = col tr a 0 := rfl
  omega

theorem fin_copy (hf : col tr "fin" = 1) (j : Nat) (hj : j < 42) : col tr "dQo" j = col tr "dQ" j := by
  have h := c7 H (e := BndLay.gate (Se.c "fin" * (Se.c "dQo" j - Se.c "dQ" j))) (by
    simp only [Se.cons7, List.mem_append]; exact .inr (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩))
  rw [gate0] at h
  simp only [evMul, evSub, colv, hf, Nat.one_mul] at h
  have h1 := col_lt (tr := tr) "dQo" j; have h2 := col_lt (tr := tr) "dQ" j
  rw [Nat.mod_eq_of_lt (by omega)] at h
  omega

theorem seg_copy (hf : col tr "fin" ≠ 1) (j : Nat) (hj : j < 42) : col tr "dSo" j = col tr "dS" j := by
  have hf0 : col tr "fin" = 0 := by have := fin_le H; omega
  have h := c7 H (e := BndLay.gate ((1 - Se.c "fin") * (Se.c "dSo" j - Se.c "dS" j))) (by
    simp only [Se.cons7, List.mem_append]; exact .inl (.inr (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)))
  rw [gate0] at h
  simp only [evMul, evSub, evOne, colv, hf0] at h
  have h1 := col_lt (tr := tr) "dSo" j; have h2 := col_lt (tr := tr) "dS" j
  simp only [Nat.sub_zero, Nat.mod_self, Nat.add_zero] at h
  omega
end

theorem cb_congr {tr : Trace Fp} {s s' : String} (h : ∀ j < 42, col tr s j = col tr s' j) : cb tr s = cb tr s' := by
  unfold cb; apply List.map_congr_left; intro j hj; rw [h j (List.mem_range.1 hj)]

section
variable {xtape : Tp} {pub : List Fp} {tr : Trace Fp} (H : Holds (Se.fullSe xtape) pub tr)
  (hr2 : NoRng xtape) (hi2 : NoSendOn B_IF384 xtape) (hC : ChipOK tr)
  (hd : NoRecvOn B_SHD xtape) (hb : NoSendOn B_SHB xtape)
include H hr2 hi2 hC hd hb

/-- **`SE`'s opening rows** (module doc). -/
theorem se_open : SeOpenOK pub tr := by
  have hfirst : ev tr 0 0 pub .isFirst = 1 := evFirst0
  have hfin : col tr "fin" = 1 → ev tr 0 0 pub (.isFirst * Se.c "fin") = 1 := fun hf => by
    simp only [evMul, evFirst0, colv, hf]
  have m : ∀ {s}, s ∈ [Se.hS0, Se.hS1, Se.hS2, Se.hS3, Se.hS4, Se.hS5, Se.hS6, Se.hS7, Se.hS8] → s ∈ Se.hashes :=
    fun h => h
  refine ⟨?_, se_tgi_lt H hr2, ?_, ?_, ?_, ?_, fun hf => ?_, fun hf => ?_⟩
  · exact fixed_dig H hr2 hi2 hC hd hb (s := Se.hS0) (m (by simp)) rfl hfirst
  · exact fixed_dig H hr2 hi2 hC hd hb (s := Se.hS1) (m (by simp)) rfl hfirst
  · exact fixed_dig H hr2 hi2 hC hd hb (s := Se.hS2) (m (by simp)) rfl hfirst
  · exact wit_dig H hr2 hi2 hC hd hb (s := Se.hS6) (m (by simp)) hfirst
  · exact wit_dig H hr2 hi2 hC hd hb (s := Se.hS7) (m (by simp)) hfirst
  · refine ⟨fin_const H (a := "tgi") (v := 8) (by decide) hf
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..))))),
      fin_const H (a := "tgo") (v := 3) (by decide) hf
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))),
      cb_congr (fin_copy H hf), ?_, ?_, ?_⟩
    · exact fixed_dig H hr2 hi2 hC hd hb (s := Se.hS3) (m (by simp)) rfl (hfin hf)
    · exact fixed_dig H hr2 hi2 hC hd hb (s := Se.hS4) (m (by simp)) rfl (hfin hf)
    · exact fixed_dig H hr2 hi2 hC hd hb (s := Se.hS5) (m (by simp)) rfl (hfin hf)
  · exact cb_congr (seg_copy H hf)

end

#print axioms se_open

end M5T1.SeOpen
