import ZkFormal.Near.Extract.RcptRowT

/-!
# ZkFormal.Near.Extract.RcptOf — the view of one receipt, emission chunks

`rcptOf tr y`: the `RcptV` read from the rows of the receipt of shape `y`.
`fld_chunk`: the messages of one emission slot over a field, when the slot is
always on, are an `emitAt` chunk; `emitAt_chunks`: an `emitAt` of a
concatenation splits into chunks.
-/

namespace ZkFormal.Near.RcptProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

variable {tr : Trace Fp} {pub : List Fp}

/-- `len` values of column `x` from row `r0`. -/
def colAt (tr : Trace Fp) (r0 len x : Nat) : List Nat := (List.range len).map fun k => cv tr T_RCPT (r0 + k) x

theorem colAt_len (tr : Trace Fp) (r0 len x : Nat) : (colAt tr r0 len x).length = len := by simp [colAt]

theorem colAt_get (tr : Trace Fp) (r0 len x k : Nat) (hk : k < len) :
    (colAt tr r0 len x).getD k 0 = cv tr T_RCPT (r0 + k) x := by
  simp [colAt, List.getD_eq_getElem?_getD, List.getElem?_range hk]

/-- The receipt read from the rows of the receipt of shape `y`. -/
def rcptOf (tr : Trace Fp) (y : RS) : RcptV :=
  let s := y.s
  let V := Vt y.Lp y.Lv y.Ls y.kt
  { p := colAt tr (s + 4) y.Lp b
    v := colAt tr (s + (8 + y.Lp)) y.Lv b
    s := colAt tr (s + (45 + y.Lp + y.Lv)) y.Ls b
    rid := colAt tr (s + (8 + y.Lp + y.Lv)) 32 b
    kt := y.kt
    pk := colAt tr (s + (46 + y.Lp + y.Lv + y.Ls)) (32 + 32 * y.kt) b
    gp := colAt tr (s + (78 + V)) 16 b
    dep := colAt tr (s + (107 + V)) 16 b
    hr := y.h
    ge := decide (tr.cell T_RCPT s ge = 1)
    kslot := cv tr T_RCPT s kslot
    tprev := cv tr T_RCPT s tprev
    bef := colAt tr (s + (107 + V)) 16 bef
    lk := colAt tr (s + (107 + V)) 16 lk
    st := colAt tr (s + (107 + V)) 16 st
    aft := (List.range 16).map fun k => bitsVal (fun j => cv tr T_RCPT (s + (107 + V) + k) (xb j)) 0 8
    burnt := colAt tr (s + (78 + V)) 16 burnt
    ramt := colAt tr (s + (78 + V)) 16 ramt
    rfid := if y.h then colAt tr (s + (127 + V)) 32 b else List.replicate 32 0
    peoh := colAt tr (s + (144 + 32 * hN y.h + V)) 32 b }

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

variable (hL : TableLocal Rcpt.table tr T_RCPT pub)
include hL

/-- **An always-on emission slot over a field is an `emitAt` chunk.** -/
theorem fld_chunk {s r0 L X : Nat} {ems : List Em} {e : Nat} {id p v g : Expr}
    (hH : r0 + L ≤ tr.height T_RCPT) (F : RFld tr s r0 L X) (hX : (X, ems) ∈ emits) (he : e < 3)
    (hs : ems[e]? = some (id, p, v, g)) (idN off : Nat) (bytes : List Nat) (hlen : bytes.length = L)
    (hg : ∀ k, k < L → g.eval tr T_RCPT (r0 + k) pub = 1)
    (hid : ∀ k, k < L → id.eval tr T_RCPT (r0 + k) pub = ((idN : Nat) : Fp))
    (hp : ∀ k, k < L → p.eval tr T_RCPT (r0 + k) pub = ((off + k : Nat) : Fp))
    (hv : ∀ k, k < L → v.eval tr T_RCPT (r0 + k) pub = ((bytes.getD k 0 : Nat) : Fp)) :
    (List.range' r0 L).flatMap (fun q => slotT tr q e) = (emitAt idN off bytes).map Msg.toFp := by
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
    (hH : r0 + L ≤ tr.height T_RCPT) (F : RFld tr s r0 L X) (hX : (X, ems) ∈ emits) (he : e < 3)
    (hs : ems[e]? = some (id, p, v, g)) (hg : ∀ k, k < L → g.eval tr T_RCPT (r0 + k) pub = 0) :
    (List.range' r0 L).flatMap (fun q => slotT tr q e) = [] := by
  rw [List.range'_eq_map_range, List.flatMap_map]
  rw [flatMap_congr' (G := fun _ => []) (fun k hk => by
      rw [List.mem_range] at hk
      rw [emit_some hL (by omega) hX (F.fld.st k hk) he hs, if_neg (by rw [hg k hk]; exact fp_zero_ne_one)]),
    flatMap_nil_fun]

/-- A missing slot. -/
theorem fld_chunk_none {s r0 L X : Nat} {ems : List Em} {e : Nat}
    (hH : r0 + L ≤ tr.height T_RCPT) (F : RFld tr s r0 L X) (hX : (X, ems) ∈ emits) (he : e < 3)
    (hs : ems[e]? = none) : (List.range' r0 L).flatMap (fun q => slotT tr q e) = [] := by
  rw [List.range'_eq_map_range, List.flatMap_map]
  rw [flatMap_congr' (G := fun _ => []) (fun k hk => by
      rw [List.mem_range] at hk
      exact emit_none hL (by omega) hX (F.fld.st k hk) he hs), flatMap_nil_fun]

end ZkFormal.Near.RcptProof

namespace ZkFormal.Near.RcptProof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl ZkFormal.Near.Rcpt

/-- The three slots of a field's rows, up to permutation. -/
theorem slots_perm (tr : Trace Fp) (r0 L : Nat) :
    ((List.range' r0 L).flatMap fun q => (List.range 3).flatMap (slotT tr q)).Perm
      ((List.range' r0 L).flatMap (fun q => slotT tr q 0) ++ (List.range' r0 L).flatMap (fun q => slotT tr q 1) ++
        (List.range' r0 L).flatMap (fun q => slotT tr q 2)) := by
  have h3 : ∀ q, (List.range 3).flatMap (slotT tr q) = slotT tr q 0 ++ (slotT tr q 1 ++ slotT tr q 2) := by
    intro q; simp [List.range_succ]
  simp only [h3]
  refine (flatMap_append_perm _ _ _).trans ?_
  rw [List.append_assoc]
  exact List.Perm.append_left _ (flatMap_append_perm _ _ _)

end ZkFormal.Near.RcptProof
