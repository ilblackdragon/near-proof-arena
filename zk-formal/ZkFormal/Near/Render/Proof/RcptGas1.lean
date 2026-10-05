import ZkFormal.Near.Render.Proof.RcptRegs4

/-!
# ZkFormal.Near.Render.Proof.RcptGas1 — cells of the `GP` rows; bit pools; public bytes

* `PA_field`: the claim bytes of the generator's public array are the
  little-endian bytes of the claim fields (`Link.pub_*`);
* `bitsX_seg`/`bitsXn_seg`: a bit pool of a receipt row evaluates to the number
  whose bits it holds;
* the cells of row `i` of the `GP` field (`gp_*`).
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

set_option linter.unusedSimpArgs false

namespace RcptP

open RcptGen

/-! ## Public bytes -/

theorem PA_pubNat (c : WfClaim) (e : Ext) (j : Nat) : (PA c.1 e).getD j 0 = pubNat (publicOf c) j := by
  rw [Link.pubNat_publicOf]
  simp only [PA, pubArr, mkInfo_c, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD,
    toNats, List.getElem?_map]
  cases c.1.encode[j]? <;> rfl

theorem PA_field {c : WfClaim} {e : Ext} {off w X : Nat}
    (h : pubBytes (publicOf c) off w = (leN w X).map (·.toNat)) {k : Nat} (hk : k < w) :
    (PA c.1 e).getD (off + k) 0 = (leBytes w X).getD k 0 := by
  have := congrArg (fun l => l.getD k 0) h
  simp only [pubBytes, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some] at this
  rw [PA_pubNat, this]
  simp [leBytes, toNats, List.getD_eq_getElem?_getD]

theorem PA_bgp {c : WfClaim} {e : Ext} (hh : Link.Hdr c) {k : Nat} (hk : k < 16) :
    (PA c.1 e).getD (PV_BGP + k) 0 = BG c.1 k := PA_field (Link.pub_bgp hh) hk

/-! ## Bit pools -/

section
variable {c : Claim} {e : Ext} {r s i : Nat} {nx : Nat → Fp} {fst lst : Bool} {pub : List Fp}

theorem bitsX_seg {off len X : Nat} (hlen : off + len ≤ 66)
    (hv : ∀ j, j < len → segXb (Df c e r) (BG c) s i (off + j) = bitOf X j) (hX : X < 2 ^ len) :
    evR (cF c e (.seg r s i)) nx fst lst pub (Rcpt.bitsX off len) = Fp.ofNat X := by
  rw [evR_bitsX (v := fun j => segXb (Df c e r) (BG c) s i j) off len (fun j h1 h2 => by
    simp only [cF]; rw [S_xb c e r s i (by omega)])]
  rw [bitsVal_pool hv hX]

theorem bitsXn_seg {cur : Nat → Fp} {off len X : Nat} (hlen : off + len ≤ 66)
    (hv : ∀ j, j < len → segXb (Df c e r) (BG c) s i (off + j) = bitOf X j) (hX : X < 2 ^ len) :
    evR cur (cF c e (.seg r s i)) fst lst pub (Rcpt.bitsXn off len) = Fp.ofNat X := by
  rw [evR_bitsXn (v := fun j => segXb (Df c e r) (BG c) s i j) off len (fun j h1 h2 => by
    simp only [cF]; rw [S_xb c e r s i (by omega)])]
  rw [bitsVal_pool hv hX]

theorem cF_xb {j : Nat} (hj : j < 66) : cF c e (.seg r s i) (Rcpt.xb j) = Fp.ofNat (segXb (Df c e r) (BG c) s i j) := by
  simp only [cF, S_xb c e r s i hj]

theorem bitOf_small {x : Nat} (h : x ≤ 1) : bitOf x 0 = x := by unfold bitOf; simp; omega

theorem bitOf_lt (x : Nat) {len : Nat} (hx : x < 2 ^ len) : ∀ j, j ≥ len → bitOf x j = 0 := by
  intro j hj
  unfold bitOf
  have : 2 ^ len ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj
  rw [Nat.div_eq_of_lt (by omega)]

end

/-! ## `GP` pools -/

section
variable {d : RD} {bg : Nat → Nat} {i : Nat}

theorem gx_D {j : Nat} (hj : j < 8) : segXb d bg 15 i (0 + j) = bitOf (Seg.gdv d bg i) j := by
  simp only [segXb, ↓reduceIte, Nat.zero_add, hj]
theorem gx_8 : segXb d bg 15 i 8 = bitOf (Seg.gbr d bg (i + 1)) 0 := by simp [segXb]
theorem gx_B {j : Nat} (hj : j < 11) : segXb d bg 15 i (9 + j) = bitOf (Seg.sb d bg i / 256) j := by
  simp only [segXb, ↓reduceIte]; simp (disch := omega) only [if_pos, if_neg]; congr 1; omega
theorem gx_R {j : Nat} (hj : j < 11) : segXb d bg 15 i (20 + j) = bitOf (Seg.sr d bg i / 256) j := by
  simp only [segXb, ↓reduceIte]; simp (disch := omega) only [if_pos, if_neg]; congr 1; omega
theorem gx_T {j : Nat} (hj : j < 8) : segXb d bg 15 i (31 + j) = bitOf (Seg.tt d bg i % 256) j := by
  simp only [segXb, ↓reduceIte]; simp (disch := omega) only [if_pos, if_neg]; congr 1; omega
theorem gx_39 : segXb d bg 15 i 39 = bitOf (Seg.tt d bg i / 256) 0 := by simp [segXb]

end

/-! ## `GP` cells -/

section
variable {c : Claim} {e : Ext} {r i : Nat}

theorem gp_b : cF c e (.seg r 15 i) Rcpt.b = Fp.ofNat (Seg.gpB (Df c e r) i) := by
  simp only [cF, S_b]; rfl
theorem gp_reg0 (hi : i < 16) : cF c e (.seg r 15 i) (Rcpt.reg 0) = Fp.ofNat ((PA c e).getD (PV_BGP + i) 0) := by
  rw [cF_reg (by decide)]
  simp only [fLd, Nat.reduceEqDiff, ↓reduceIte, Nat.add_zero, pubs_getD _ hi]
theorem gp_c1 : cF c e (.seg r 15 i) Rcpt.c1 = Fp.ofNat (Seg.gbr (Df c e r) (BG c) i) := by
  simp only [cF, S_c1]; rfl
theorem gp_c2 : cF c e (.seg r 15 i) Rcpt.c2 = Fp.ofNat (chain (Seg.x2 (Df c e r) (BG c)) i) := by
  simp only [cF, S_c2]; rfl
theorem gp_c3 : cF c e (.seg r 15 i) Rcpt.c3 = Fp.ofNat (chain (Seg.x3 (Df c e r) (BG c)) i) := by
  simp only [cF, S_c3]; rfl
theorem gp_c4 : cF c e (.seg r 15 i) Rcpt.c4 = Fp.ofNat (chain (Seg.x4 (Df c e r) (BG c)) i) := by
  simp only [cF, S_c4]; rfl
theorem gp_burnt : cF c e (.seg r 15 i) Rcpt.burnt = Fp.ofNat (Seg.sb (Df c e r) (BG c) i % 256) := by
  simp only [cF, S_burnt]; rfl
theorem gp_ramt : cF c e (.seg r 15 i) Rcpt.ramt = Fp.ofNat (Seg.sr (Df c e r) (BG c) i % 256) := by
  simp only [cF, S_ramt]; rfl
theorem gp_sumD : cF c e (.seg r 15 i) Rcpt.sumD = Fp.ofNat (runSum (Seg.gdv (Df c e r) (BG c)) i) := by
  simp only [cF, S_sumD]; rfl
theorem gp_invA : cF c e (.seg r 15 i) Rcpt.invA =
    Fp.ofNat (if i + 1 = 16 ∧ (Df c e r).hr = true then invP (runSum (Seg.gdv (Df c e r) (BG c)) i) else 0) := by
  simp only [cF, S_invA]; rfl
theorem gp_ge : cF c e (.seg r 15 i) Rcpt.ge = Fp.ofNat (b2n (Df c e r).ge) := by simp only [cF, S_ge]
theorem gp_hr : cF c e (.seg r 15 i) Rcpt.hr = Fp.ofNat (b2n (Df c e r).hr) := by simp only [cF, S_hr]
theorem gp_tok0 : cF c e (.seg r 15 i) (Rcpt.tok 0) = Fp.ofNat (if i < 16 then Seg.tokOld (Df c e r) i
    else Seg.tokNew (Df c e r) (i - 16)) := by
  rw [cF_tok (by decide)]; simp [segTok, beforeGP]
theorem gp_dlP {j : Nat} (hj : j < 4) :
    cF c e (.seg r 15 i) (Rcpt.dl j) = Fp.ofNat (if j < i then Seg.pB (Df c e r) (BG c) (i - 1 - j) else 0) := by
  simp only [cF, S_dl c e r 15 i (show j < 8 by omega), ↓reduceIte, show 208 + j < 212 by omega]
theorem gp_dlS {j : Nat} (hj : j < 4) :
    cF c e (.seg r 15 i) (Rcpt.dl (4 + j)) = Fp.ofNat (if j < i then Seg.surB (Df c e r) (BG c) (i - 1 - j) else 0) := by
  simp only [cF, S_dl c e r 15 i (show 4 + j < 8 by omega), ↓reduceIte, show ¬ (208 + (4 + j) < 212) by omega,
    show 208 + (4 + j) - 212 = j by omega]

end

end RcptP

end ZkFormal.Near.Render
