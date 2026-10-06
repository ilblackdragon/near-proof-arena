import ZkFormal.NearV3.Rcpt.Extract.V.RowT

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.Of — the view of one `rcptV3` receipt, emission chunks

`rcptOf tr y`: the `RcptV` read from the rows of the receipt of shape `y`.
`fld_chunk`: the messages of one emission slot over a field, when the slot is
always on, are an `emitAt` chunk; `emitAt_chunks`: an `emitAt` of a
concatenation splits into chunks.
-/

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- `len` values of column `x` from row `r0`. -/
def colAt (tr : Trace Fp) (tt r0 len x : Nat) : List Nat := (List.range len).map fun k => cv tr tt (r0 + k) x

theorem colAt_len (tr : Trace Fp) (tt r0 len x : Nat) : (colAt tr tt r0 len x).length = len := by simp [colAt]

theorem colAt_get (tr : Trace Fp) (tt r0 len x k : Nat) (hk : k < len) :
    (colAt tr tt r0 len x).getD k 0 = cv tr tt (r0 + k) x := by
  simp [colAt, List.getD_eq_getElem?_getD, List.getElem?_range hk]

/-- Row of routing lookup position `k` of the receipt at `s` (receiver row `k`, or the first
`RID` row for `k = Lv`). -/
def lkRow (y : RS) (k : Nat) : Nat := y.s + (8 + y.Lp) + k

/-- The receipt read from the rows of the receipt of shape `y`. -/
def rcptOf (tr : Trace Fp) (tt : Nat) (y : RS) : RcptE :=
  let s := y.s
  let V := Vt y.Lp y.Lv y.Ls y.kt
  let T0 := s + (40 + y.Lp + y.Lv)
  { p := colAt tr tt (s + 4) y.Lp b
    v := colAt tr tt (s + (8 + y.Lp)) y.Lv b
    s := colAt tr tt (s + (45 + y.Lp + y.Lv)) y.Ls b
    rid := colAt tr tt (s + (8 + y.Lp + y.Lv)) 32 b
    kt := y.kt
    pk := colAt tr tt (s + (46 + y.Lp + y.Lv + y.Ls)) (32 + 32 * y.kt) b
    gp := colAt tr tt (s + (78 + V)) 16 b
    dep := colAt tr tt (s + (107 + V)) 16 b
    hr := y.h
    ge := decide (tr.cell tt s ge = 1)
    kslot := cv tr tt s kslot
    tprev := cv tr tt s tprev
    bef := colAt tr tt (s + (107 + V)) 16 bef
    lk := colAt tr tt (s + (107 + V)) 16 lk
    st := colAt tr tt (s + (107 + V)) 16 st
    aft := (List.range 16).map fun k => bitsVal (fun j => cv tr tt (s + (107 + V) + k) (xb j)) 0 8
    burnt := colAt tr tt (s + (78 + V)) 16 burnt
    ramt := colAt tr tt (s + (78 + V)) 16 ramt
    rfid := if y.h then colAt tr tt (s + (127 + V)) 32 b else List.replicate 32 0
    peoh := colAt tr tt (s + (144 + 32 * hN y.h + V)) 32 b
    sys := decide (tr.cell tt s RcptV3.sys = 1)
    ee := decide (tr.cell tt s ee = 1)
    gv := (List.range y.Lv).map fun k => decide (tr.cell tt (s + (8 + y.Lp) + k) gV = 1)
    gs := (List.range y.Ls).map fun k => decide (tr.cell tt (s + (45 + y.Lp + y.Lv) + k) gS = 1)
    sx := colAt tr tt (s + (45 + y.Lp + y.Lv)) y.Ls sx
    akf := cv tr tt T0 fkF
    akk := cv tr tt T0 kF
    aku := cv tr tt T0 uak
    q := cv tr tt s RcptV3.q
    rlk := (List.range (y.Lv + 1)).filterMap fun k =>
      if tr.cell tt (lkRow y k) gBd = 1 then
        some (k, cv tr tt (lkRow y k) loB, cv tr tt (lkRow y k) hiB, cv tr tt (lkRow y k) hnB, cv tr tt (lkRow y k) uB)
      else none }

/-! ## Chunks -/

/-- Chunks `(offset, bytes)` laid out consecutively from `off`. -/
def Consec2 : Nat → List (Nat × List Nat) → Prop
  | _, [] => True
  | off, (o, l) :: rest => o = off ∧ Consec2 (off + l.length) rest

theorem emitAt_append (id off : Nat) (l1 l2 : List Nat) :
    emitAt id off (l1 ++ l2) = emitAt id off l1 ++ emitAt id (off + l1.length) l2 := by
  unfold emitAt
  rw [List.length_append, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left; intro i hi; rw [List.mem_range] at hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  · apply List.map_congr_left; intro i hi
    simp [List.getD_eq_getElem?_getD, Nat.add_assoc, List.getElem?_append_right]

theorem emitAt_chunks (id : Nat) : ∀ (cs : List (Nat × List Nat)) (off : Nat), Consec2 off cs →
    emitAt id off (cs.flatMap (·.2)) = cs.flatMap (fun c => emitAt id c.1 c.2) := by
  intro cs
  induction cs with
  | nil => intro _ _; rfl
  | cons c rest ih =>
    intro off hc
    obtain ⟨o, l⟩ := c
    obtain ⟨rfl, hc⟩ := hc
    simp only [List.flatMap_cons]
    rw [emitAt_append, ih _ hc]

variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- **An always-on emission slot over a field is an `emitAt` chunk.** -/
theorem fld_chunk {s r0 L X : Nat} {ems : List Em} {e : Nat} {id p v g : Expr}
    (hH : r0 + L ≤ tr.height tt) (F : RFld tr tt s r0 L X) (hX : (X, ems) ∈ emits) (he : e < 3)
    (hs : ems[e]? = some (id, p, v, g)) (idN off : Nat) (bytes : List Nat) (hlen : bytes.length = L)
    (hg : ∀ k, k < L → g.eval tr tt (r0 + k) pub = 1)
    (hid : ∀ k, k < L → id.eval tr tt (r0 + k) pub = ((idN : Nat) : Fp))
    (hp : ∀ k, k < L → p.eval tr tt (r0 + k) pub = ((off + k : Nat) : Fp))
    (hv : ∀ k, k < L → v.eval tr tt (r0 + k) pub = ((bytes.getD k 0 : Nat) : Fp)) :
    (List.range' r0 L).flatMap (fun q => slotT tr tt q e) = (emitAt idN off bytes).map Msg.toFp := by
  rw [List.range'_eq_map_range, List.flatMap_map, emitAt, hlen, List.map_map]
  rw [flatMap_congr' (G := fun k => [[((idN : Nat) : Fp), ((off + k : Nat) : Fp), ((bytes.getD k 0 : Nat) : Fp)]])
    (fun k hk => by
      rw [List.mem_range] at hk
      rw [emit_some hL (by omega) hX (F.fld.st k hk) he hs, if_pos (hg k hk), hid k hk, hp k hk, hv k hk])]
  rw [← map_eq_flatMap]
  apply List.map_congr_left; intro k _
  simp [Msg.toFp, natCast_eq]

/-- A slot that is off over a field. -/
theorem fld_chunk_off {s r0 L X : Nat} {ems : List Em} {e : Nat} {id p v g : Expr}
    (hH : r0 + L ≤ tr.height tt) (F : RFld tr tt s r0 L X) (hX : (X, ems) ∈ emits) (he : e < 3)
    (hs : ems[e]? = some (id, p, v, g)) (hg : ∀ k, k < L → g.eval tr tt (r0 + k) pub = 0) :
    (List.range' r0 L).flatMap (fun q => slotT tr tt q e) = [] := by
  rw [List.range'_eq_map_range, List.flatMap_map]
  rw [flatMap_congr' (G := fun _ => []) (fun k hk => by
      rw [List.mem_range] at hk
      rw [emit_some hL (by omega) hX (F.fld.st k hk) he hs, if_neg (by rw [hg k hk]; exact fp_zero_ne_one)]),
    flatMap_nil_fun]

/-- A missing slot. -/
theorem fld_chunk_none {s r0 L X : Nat} {ems : List Em} {e : Nat}
    (hH : r0 + L ≤ tr.height tt) (F : RFld tr tt s r0 L X) (hX : (X, ems) ∈ emits) (he : e < 3)
    (hs : ems[e]? = none) : (List.range' r0 L).flatMap (fun q => slotT tr tt q e) = [] := by
  rw [List.range'_eq_map_range, List.flatMap_map]
  rw [flatMap_congr' (G := fun _ => []) (fun k hk => by
      rw [List.mem_range] at hk
      exact emit_none hL (by omega) hX (F.fld.st k hk) he hs), flatMap_nil_fun]

end ZkFormal.NearV3.RcptV3Proof

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3

/-- The three slots of a field's rows, up to permutation. -/
theorem slots_perm (tr : Trace Fp) (tt r0 L : Nat) :
    ((List.range' r0 L).flatMap fun q => (List.range 3).flatMap (slotT tr tt q)).Perm
      ((List.range' r0 L).flatMap (fun q => slotT tr tt q 0) ++ (List.range' r0 L).flatMap (fun q => slotT tr tt q 1) ++
        (List.range' r0 L).flatMap (fun q => slotT tr tt q 2)) := by
  have h3 : ∀ q, (List.range 3).flatMap (slotT tr tt q) = slotT tr tt q 0 ++ (slotT tr tt q 1 ++ slotT tr tt q 2) := by
    intro q; simp [List.range_succ]
  simp only [h3]
  refine (flatMap_append_perm _ _ _).trans ?_
  rw [List.append_assoc]
  exact List.Perm.append_left _ (flatMap_append_perm _ _ _)

end ZkFormal.NearV3.RcptV3Proof
