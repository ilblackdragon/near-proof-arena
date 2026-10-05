import ZkFormal.Near.Render.Proof.RcptLocal
import ZkFormal.Near.Render.Proof.RcptNat

/-!
# ZkFormal.Near.Render.Proof.RcptRegs1 — `cRegs`: the split, claim-row register cells, the loads

`cRegs = rA ++ … ++ rJ` (loads, register head, shifts, claim loads, claim token
loads, rotations, tokens zeroed, tokens rewritten in `GP`, the new top byte,
tokens kept).  `load_ok`: the register contents loaded at a field's first
row are the values of the `loads` expressions.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

def rA : List Expr := Rcpt.loads.flatMap (fun (s, l) =>
    (l.zip (List.range l.length)).map fun (e, j) => mul3 (c s) (c Rcpt.fs) (sub (c (Rcpt.reg j)) e))
def rB : List Expr := [ .mul (sum (Rcpt.regStates.map c)) (sub (c Rcpt.b) (c (Rcpt.reg 0))) ]
def rC : List Expr := (List.range 31).map (fun j => mul3 Rcpt.rowE (Dsl.not (c Rcpt.fe))
    (sub (n (Rcpt.reg j)) (c (Rcpt.reg (j + 1)))))
def clLd : List Expr :=
  Rcpt.pubs PV_SHARD 8 ++ Rcpt.pubs PV_N 4 ++ Rcpt.pubs PV_NREF 4 ++ Rcpt.ks Rcpt.G_LE ++ Rcpt.pubs PV_GASLIM 8
def tkLd : List Expr := Rcpt.pubs PV_GAS 8 ++ Rcpt.ks (List.replicate 8 0)
def rD : List Expr := (clLd.zip (List.range 32)).map (fun (e, j) => .mul .isFirst (sub (c (Rcpt.reg j)) e))
def rE : List Expr := (tkLd.zip (List.range 16)).map (fun (e, j) => .mul .isFirst (sub (c (Rcpt.tok j)) e))
def rF : List Expr := Rcpt.rot (fun j => Rcpt.reg j) 12 ++ Rcpt.rot (fun j => Rcpt.reg (12 + j)) 4 ++
  Rcpt.rot (fun j => Rcpt.reg (16 + j)) 8 ++ Rcpt.rot (fun j => Rcpt.reg (24 + j)) 8 ++ Rcpt.rot (fun j => Rcpt.tok j) 8
def rG : List Expr := (List.range 16).map (fun j => mul3 (c Rcpt.sCL) (c Rcpt.fe) (n (Rcpt.tok j)))
def rH : List Expr := (List.range 15).map (fun j => .mul (c Rcpt.sGP) (sub (n (Rcpt.tok j)) (c (Rcpt.tok (j + 1)))))
def rI : List Expr := [ .mul (c Rcpt.sGP) (sub (n (Rcpt.tok 15)) (Rcpt.bitsX 31 8)) ]
def rJ : List Expr := (List.range 16).map (fun j =>
  .mul (sub (sub Rcpt.rowE (c Rcpt.sGP)) (c Rcpt.lastR)) (sub (n (Rcpt.tok j)) (c (Rcpt.tok j))))

set_option maxRecDepth 20000 in
theorem cRegs_eq : Rcpt.cRegs = rA ++ rB ++ rC ++ rD ++ rE ++ rF ++ rG ++ rH ++ rI ++ rJ := rfl

/-! ## Claim-row register cells -/

section
variable (c : Claim) (e : Ext) (i : Nat)

theorem L_reg {j : Nat} (hj : j < 32) : Cc c e (.cl i) (Rcpt.reg j) =
    if j < 12 then (Cl.A (PA c e)).getD ((i + j) % 12) 0
    else if j < 16 then (Cl.B (PA c e)).getD ((i + (j - 12)) % 4) 0
    else if j < 24 then Rcpt.G_LE.getD ((i + (j - 16)) % 8) 0
    else (Cl.D (PA c e)).getD ((i + (j - 24)) % 8) 0 := by
  simp only [Rcpt.reg]
  rw [Cc_cl _ _ _ _ (by omega)]
  simp only [clCell]
  by_cases h1 : j < 12
  · simp (disch := omega) only [if_pos, if_neg]; congr 2; omega
  by_cases h2 : j < 16
  · simp (disch := omega) only [if_pos, if_neg]; congr 2; omega
  by_cases h3 : j < 24
  · simp (disch := omega) only [if_pos, if_neg]; congr 2; omega
  · simp (disch := omega) only [if_pos, if_neg]; congr 2; omega

theorem L_tok {j : Nat} (hj : j < 16) : Cc c e (.cl i) (Rcpt.tok j) =
    if j < 8 then (Cl.T (PA c e)).getD ((i + j) % 8) 0 else 0 := by
  simp only [Rcpt.tok]
  rw [Cc_cl _ _ _ _ (by omega)]
  simp only [clCell]
  by_cases h1 : j < 8
  · simp (disch := omega) only [if_pos, if_neg]; congr 2; omega
  · simp (disch := omega) only [if_pos, if_neg]
    split <;> rfl

theorem L_xb {j : Nat} (hj : j < 66) : Cc c e (.cl i) (Rcpt.xb j) = clCell (PA c e) i (138 + j) := by
  simp only [Rcpt.xb]; rw [Cc_cl _ _ _ _ (by omega)]

theorem L_xbA {j : Nat} (hj : j < 8) : Cc c e (.cl i) (Rcpt.xb j) = if i < 8 then bitOf (Cl.sy (PA c e) i % 256) j else 0 := by
  rw [L_xb _ _ _ (by omega)]; simp only [clCell]
  simp (disch := omega) only [if_neg, if_pos, Nat.add_sub_cancel_left]

theorem L_xbB {j : Nat} (hj : j < 8) : Cc c e (.cl i) (Rcpt.xb (8 + j)) = if i < 8 then bitOf (Cl.sy (PA c e) i / 256) j else 0 := by
  rw [L_xb _ _ _ (by omega)]; simp only [clCell]
  simp (disch := omega) only [if_neg, if_pos]
  rw [show 138 + (8 + j) - 146 = j by omega]

theorem L_xbC {j : Nat} (hj : j < 8) : Cc c e (.cl i) (Rcpt.xb (16 + j)) = if i < 8 then bitOf (Cl.dv (PA c e) i) j else 0 := by
  rw [L_xb _ _ _ (by omega)]; simp only [clCell]
  simp (disch := omega) only [if_neg, if_pos]
  rw [show 138 + (16 + j) - 154 = j by omega]

theorem L_xb24 : Cc c e (.cl i) (Rcpt.xb 24) = if i < 8 then bitOf (Cl.br (PA c e) (i + 1)) 0 else 0 := by
  rw [L_xb _ _ _ (by omega)]; simp [clCell]

theorem L_xb25 : Cc c e (.cl i) (Rcpt.xb 25) = if i < 8 then bitOf (Cl.sg (PA c e) i / 256) 0 else 0 := by
  rw [L_xb _ _ _ (by omega)]; simp [clCell]

end

/-! ## Loads -/

theorem mem_zip_range {α : Type} {l : List α} {x : α} {j : Nat} (h : (x, j) ∈ l.zip (List.range l.length)) :
    ∃ h : j < l.length, l[j] = x := by
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.1 h
  simp only [List.length_zip, List.length_range, Nat.min_self] at hk
  simp only [List.getElem_zip, List.getElem_range, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨hk, rfl⟩

theorem mem_zip_range' {α : Type} {l : List α} {x : α} {j m : Nat} (hm : m = l.length)
    (h : (x, j) ∈ l.zip (List.range m)) : ∃ h : j < l.length, l[j] = x := by
  subst hm; exact mem_zip_range h

theorem getElem_ks {L : List Nat} {j : Nat} (h : j < (Rcpt.ks L).length) :
    (Rcpt.ks L)[j] = Dsl.k (L[j]'(by simpa [Rcpt.ks] using h)) := by
  simp [Rcpt.ks]

theorem getElem_pubs {off len j : Nat} (h : j < (Rcpt.pubs off len).length) :
    (Rcpt.pubs off len)[j] = .pub (off + j) := by
  simp [Rcpt.pubs]

theorem pubs_getD (pub : Array Nat) {off len j : Nat} (h : j < len) :
    (RcptGen.pubs pub off len).getD j 0 = pub.getD (off + j) 0 := by
  simp [RcptGen.pubs, List.getD_eq_getElem?_getD, List.getElem?_range h]

theorem pub_get (c : WfClaim) (e : Ext) (i : Nat) : (publicOf c)[i]?.getD 0 = Fp.ofNat ((PA c.1 e).getD i 0) := by
  rw [← pub_eq c e i, List.getD_eq_getElem?_getD]

theorem getD_eq_getElem {L : List Nat} {j : Nat} (h : j < L.length) : L.getD j 0 = L[j] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

section
variable {c : WfClaim} {e : Ext} {r : Nat} {nx : Nat → Fp} {fst lst : Bool}

theorem ld_pubs {st off len j : Nat} (hj : j < len) (hf : fLd (Df c.1 e r) (PA c.1 e) st = RcptGen.pubs (PA c.1 e) off len) :
    evR (cF c.1 e (.seg r st 0)) nx fst lst (publicOf c) (.pub (off + j)) =
      Fp.ofNat ((fLd (Df c.1 e r) (PA c.1 e) st).getD j 0) := by
  rw [evR_pub, pub_eq, hf, pubs_getD _ hj]

theorem ld_ks {st j : Nat} {L : List Nat} (hj : j < L.length) (hf : fLd (Df c.1 e r) (PA c.1 e) st = L) :
    evR (cF c.1 e (.seg r st 0)) nx fst lst (publicOf c) (Dsl.k (L[j])) =
      Fp.ofNat ((fLd (Df c.1 e r) (PA c.1 e) st).getD j 0) := by
  rw [evR_k, hf, getD_eq_getElem hj]; rfl

/-- **The loads.** -/
theorem load_ok {st : Nat} {l : List Expr} (hl : (st, l) ∈ Rcpt.loads) {x : Expr} {j : Nat}
    (hx : (x, j) ∈ l.zip (List.range l.length)) :
    j < 32 ∧ evR (cF c.1 e (.seg r st 0)) nx fst lst (publicOf c) x =
      Fp.ofNat ((fLd (Df c.1 e r) (PA c.1 e) st).getD j 0) := by
  obtain ⟨hj, rfl⟩ := mem_zip_range hx
  simp only [Rcpt.loads, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hl
  rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp only [List.length_cons, List.length_nil, Rcpt.ks, Rcpt.pubs, List.length_map, List.length_range,
    List.length_append, List.length_replicate, Rcpt.G_LE] at hj
  all_goals refine ⟨by omega, ?_⟩
  all_goals rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  all_goals first
    | omega
    | simp [Rcpt.ks, Rcpt.pubs, Rcpt.G_LE, fLd, cF, rseg, pub_eq, pubs_getD, natCast_eq, pub_get c e, RcptGen.pubs, Rcpt.sPL, Rcpt.sVL,
        Rcpt.sSL, Rcpt.sT0, Rcpt.sKT, Rcpt.sTL, Rcpt.sXP0, Rcpt.sXG, Rcpt.sXST, Rcpt.sXL0, Rcpt.sXRH, Rcpt.sXRF,
        Rcpt.sXRZ, Rcpt.sP, Rcpt.sGP, PV_HEIGHT, PV_BGP]

end

end RcptP

end ZkFormal.Near.Render
