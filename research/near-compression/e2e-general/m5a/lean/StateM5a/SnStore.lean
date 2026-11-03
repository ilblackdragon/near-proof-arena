import StateM5a.SnVer

/-!
# StateM5a.SnStore — `OldOK` / `NewOK` of the `SN` rows from `VER` balance (`cont = 0`)

The `SN` part of the version store: `snVers` (rows publishing their new node under a version id,
`(snVid r, snNew r)`), with ids distinct from each other and from the `BR` ones
(`vers_nodup`: `ID_BR + 2·rid + 1` vs `ID_SN + 2·rid + 1`, times 256 mod `P`).

* **`sn_newOK`**: a row with a new node (`gnew`, `cont = 0`) publishes `NewOK σ snOut snNew` —
  hashed (`SnRec.sn_new_node`) or under its version id;
* **`sn_oldOK`**: a row reading its old node (`gold`, `cont = 0`) has `OldOK σ snIn snOld` —
  hashed here (`SnRec.sn_old_node`), or read on `VER` (`SnVer.sn_rd_part`, 3 parts): under a
  version id all parts come from the one row with that id, so the record is that row's new
  record; under a digest each part comes from a record hashed to it, all equal by `Sha256CR`
  (`hashed_agree`), and the reader's fields are those records' fields (part 0: kind, key length,
  payload, memory; parts 1 / 2: the key nibbles, equal through the common key).

The `SN` record parts carry raw nibbles, which a record does not determine past the key's end,
so the generic `VerDec.PartDec` route of the `BR` side does not apply; the agreement is argued on
the key directly.
-/

namespace StateM5a.SnStore

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KeyDecode StateM5a.KeyDigest StateM5a.SnSer StateM5a.SnHashed StateM5a.SnRec
open StateM5a.SnVer StateM5a.RowSn StateM5a.RowSnMsg StateM5a.RowSnN

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Publisher columns -/

def pX (nw : Bool) (t : Nat) : Expr := if nw then Sn.c "nx" t else Sn.c "x" t
def pXF (nw : Bool) : Expr := if nw then Sn.c "nxf" else Sn.c "xf"
def pMB (nw : Bool) (b : Nat) : Expr := if nw then Sn.c "nmem" b else Sn.c "mem" b
def pFL (nw : Bool) : Expr := if nw then Sn.c "nref" else 0
def pRef (nw : Bool) : List Expr := if nw then pack2 fun b => Sn.c "hn" b else pack2 fun b => Sn.c "ho" b
def pE (nw : Bool) (p : Nat) : List Expr := if nw then sNewE p else sOldE p

theorem pE_parts (nw : Bool) :
    pE nw 0 = [K VT_SN, K 0, pFL nw] ++ pRef nw ++ [Sn.c "isL", Sn.c "klen", pXF nw] ++
      (List.range 36).map (pX nw) ++ (List.range 4).map (fun k => limb16 (pMB nw) k) ∧
    pE nw 1 = [K VT_SN, K 1, pFL nw] ++ pRef nw ++ (List.range 32).map (fun j => Sn.c "k" j) ∧
    pE nw 2 = [K VT_SN, K 2, pFL nw] ++ pRef nw ++ (List.range 32).map (fun j => Sn.c "k" (32 + j)) := by
  cases nw <;> exact ⟨rfl, rfl, rfl⟩

theorem rd_parts :
    sRdE 0 = [K VT_SN, K 0, Sn.c "oref"] ++ (pack2 fun b => Sn.c "ho" b) ++ [Sn.c "isL", Sn.c "klen", Sn.c "xf"] ++
      (List.range 36).map (fun t => Sn.c "x" t) ++ (List.range 4).map (fun k => limb16 (fun b => Sn.c "mem" b) k) ∧
    sRdE 1 = [K VT_SN, K 1, Sn.c "oref"] ++ (pack2 fun b => Sn.c "ho" b) ++ (List.range 32).map (fun j => Sn.c "k" j) ∧
    sRdE 2 = [K VT_SN, K 2, Sn.c "oref"] ++ (pack2 fun b => Sn.c "ho" b) ++
      (List.range 32).map (fun j => Sn.c "k" (32 + j)) :=
  ⟨rfl, rfl, rfl⟩

theorem app_inj_r {f g : Expr → Fp} {a b c d : List Expr} (h : (a ++ c).map f = (b ++ d).map g)
    (hl : c.length = d.length) : a.map f = b.map g ∧ c.map f = d.map g := by
  simp only [List.map_append] at h
  exact List.append_inj' h (by simp [hl])

theorem map_range_eq {f g : Expr → Fp} {n : Nat} {u v : Nat → Expr}
    (h : ((List.range n).map u).map f = ((List.range n).map v).map g) : ∀ j, j < n → f (u j) = g (v j) := by
  intro j hj
  have := congrArg (fun l => l[j]?) h
  simp only [List.map_map, List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq,
    Function.comp] at this
  exact this

section
variable {tr : Trace Fp} {pub : List Fp}

/-- What a part-0 message carries. -/
structure Fields0 (r r' : Nat) (nw : Bool) : Prop where
  fl : E tr 3 r pub (Sn.c "oref") = E tr 3 r' pub (pFL nw)
  ref : (pack2 fun b => Sn.c "ho" b).map (E tr 3 r pub) = (pRef nw).map (E tr 3 r' pub)
  isL : E tr 3 r pub (Sn.c "isL") = E tr 3 r' pub (Sn.c "isL")
  klen : E tr 3 r pub (Sn.c "klen") = E tr 3 r' pub (Sn.c "klen")
  xf : E tr 3 r pub (Sn.c "xf") = E tr 3 r' pub (pXF nw)
  x : ∀ t, t < 36 → E tr 3 r pub (Sn.c "x" t) = E tr 3 r' pub (pX nw t)
  mem : ((List.range 4).map (fun k => limb16 (fun b => Sn.c "mem" b) k)).map (E tr 3 r pub) =
    ((List.range 4).map (fun k => limb16 (pMB nw) k)).map (E tr 3 r' pub)

theorem fields0 {r r' : Nat} {nw : Bool}
    (h : (sRdE 0).map (E tr 3 r pub) = (pE nw 0).map (E tr 3 r' pub)) : Fields0 (tr := tr) (pub := pub) r r' nw := by
  rw [rd_parts.1, (pE_parts nw).1] at h
  obtain ⟨h, hm⟩ := app_inj_r h (by simp)
  obtain ⟨h, hx⟩ := app_inj_r h (by simp)
  obtain ⟨h, h3⟩ := app_inj_r h (by simp)
  obtain ⟨h, hr⟩ := app_inj_r h (by cases nw <;> simp [pRef, pack2])
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at h h3
  exact ⟨h.2.2.1, hr, h3.1, h3.2.1, h3.2.2.1, fun t ht => map_range_eq hx t ht, hm⟩

theorem fields1 {r r' : Nat} {nw : Bool}
    (h : (sRdE 1).map (E tr 3 r pub) = (pE nw 1).map (E tr 3 r' pub)) :
    ∀ j, j < 32 → E tr 3 r pub (Sn.c "k" j) = E tr 3 r' pub (Sn.c "k" j) := by
  rw [rd_parts.2.1, (pE_parts nw).2.1] at h
  obtain ⟨-, hk⟩ := app_inj_r h (by simp)
  exact map_range_eq hk

theorem fields2 {r r' : Nat} {nw : Bool}
    (h : (sRdE 2).map (E tr 3 r pub) = (pE nw 2).map (E tr 3 r' pub)) :
    ∀ j, j < 32 → E tr 3 r pub (Sn.c "k" (32 + j)) = E tr 3 r' pub (Sn.c "k" (32 + j)) := by
  rw [rd_parts.2.2, (pE_parts nw).2.2] at h
  obtain ⟨-, hk⟩ := app_inj_r h (by simp)
  exact map_range_eq hk

theorem fl_ref {r r' : Nat} {nw : Bool} {p : Nat} (hp : p < 3)
    (h : (sRdE p).map (E tr 3 r pub) = (pE nw p).map (E tr 3 r' pub)) :
    E tr 3 r pub (Sn.c "oref") = E tr 3 r' pub (pFL nw) ∧
      (pack2 fun b => Sn.c "ho" b).map (E tr 3 r pub) = (pRef nw).map (E tr 3 r' pub) := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl
  · exact ⟨(fields0 h).fl, (fields0 h).ref⟩
  · rw [rd_parts.2.1, (pE_parts nw).2.1] at h
    obtain ⟨h, -⟩ := app_inj_r h (by simp)
    obtain ⟨h, hr⟩ := app_inj_r h (by cases nw <;> simp [pRef, pack2])
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
    exact ⟨h.2.2.1, hr⟩
  · rw [rd_parts.2.2, (pE_parts nw).2.2] at h
    obtain ⟨h, -⟩ := app_inj_r h (by simp)
    obtain ⟨h, hr⟩ := app_inj_r h (by cases nw <;> simp [pRef, pack2])
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at h
    exact ⟨h.2.2.1, hr⟩

/-! ## Expression congruence across rows -/

theorem eval_add_congr {a b a' b' : Expr} {r r' : Nat} (ha : E tr 3 r pub a = E tr 3 r' pub a')
    (hb : E tr 3 r pub b = E tr 3 r' pub b') : E tr 3 r pub (a + b) = E tr 3 r' pub (a' + b') := by
  show (rowEnv tr 3 r pub).add _ _ = (rowEnv tr 3 r' pub).add _ _
  change (rowEnv tr 3 r pub).add (E tr 3 r pub a) (E tr 3 r pub b) =
    (rowEnv tr 3 r' pub).add (E tr 3 r' pub a') (E tr 3 r' pub b')
  rw [ha, hb]; rfl

theorem eval_mul_congr {a b a' b' : Expr} {r r' : Nat} (ha : E tr 3 r pub a = E tr 3 r' pub a')
    (hb : E tr 3 r pub b = E tr 3 r' pub b') : E tr 3 r pub (a * b) = E tr 3 r' pub (a' * b') := by
  change (rowEnv tr 3 r pub).mul (E tr 3 r pub a) (E tr 3 r pub b) =
    (rowEnv tr 3 r' pub).mul (E tr 3 r' pub a') (E tr 3 r' pub b')
  rw [ha, hb]; rfl

theorem eval_const_congr (c : Nat) {r r' : Nat} : E tr 3 r pub (Expr.const c) = E tr 3 r' pub (Expr.const c) := rfl

theorem pack2_congr {v w : Nat → Expr} {r r' : Nat} (h : ∀ j, j < 32 → E tr 3 r pub (v j) = E tr 3 r' pub (w j)) :
    (pack2 v).map (E tr 3 r pub) = (pack2 w).map (E tr 3 r' pub) := by
  unfold pack2
  simp only [List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.1 hi
  exact eval_add_congr (eval_mul_congr (eval_const_congr 256) (h _ (by omega))) (h _ (by omega))

theorem vlen_congr {v w : Nat → Expr} {r r' : Nat} (h : ∀ j, j < 3 → E tr 3 r pub (v j) = E tr 3 r' pub (w j)) :
    ev tr 3 r pub (Sn.vlenOf v) = ev tr 3 r' pub (Sn.vlenOf w) := by
  unfold Sn.vlenOf
  exact congrArg Fp.toNat (eval_add_congr (eval_add_congr (h 0 (by omega))
    (eval_mul_congr (eval_const_congr 256) (h 1 (by omega))))
    (eval_mul_congr (eval_const_congr 65536) (h 2 (by omega))))

theorem memS_congr {u v : Nat → Expr} {r r' : Nat}
    (h : ((List.range 4).map (fun k => limb16 u k)).map (E tr 3 r pub) =
      ((List.range 4).map (fun k => limb16 v k)).map (E tr 3 r' pub)) :
    memS tr pub r u = memS tr pub r' v := by
  unfold memS; rw [h]

/-- **A reader's record from the publisher's part-0 fields and a common key.** -/
theorem grec_of_fields {r r' : Nat} {nw : Bool} (hF : Fields0 (tr := tr) (pub := pub) r r' nw)
    (hk : snKey tr pub r = snKey tr pub r') :
    gRecS tr pub r (fun t => Sn.c "x" t) (Sn.c "xf") (fun b => Sn.c "mem" b) =
      gRecS tr pub r' (pX nw) (pXF nw) (pMB nw) := by
  have hL : ev tr 3 r pub (Sn.c "isL") = ev tr 3 r' pub (Sn.c "isL") := congrArg Fp.toNat hF.isL
  have e1 : (pack2 fun b => Sn.c "x" (4 + b)).map (nE tr pub r) = (pack2 fun b => pX nw (4 + b)).map (nE tr pub r') :=
    pack2_congr (fun j hj => hF.x _ (by omega))
  have e2 : (pack2 fun t => Sn.c "x" t).map (nE tr pub r) = (pack2 (pX nw)).map (nE tr pub r') :=
    pack2_congr (fun j hj => hF.x _ (by omega))
  have e3 : nE tr pub r (Sn.c "xf") = nE tr pub r' (pXF nw) := hF.xf
  unfold gRecS
  rw [hL, hk, memS_congr hF.mem, vlen_congr (fun j hj => hF.x j (by omega)), e1, e2, e3]

theorem pRec_false (r : Nat) : gRecS tr pub r (pX false) (pXF false) (pMB false) = snOld tr pub r := rfl
theorem pRec_true (r : Nat) : gRecS tr pub r (pX true) (pXF true) (pMB true) = snNew tr pub r := rfl

/-- The key of a record. -/
def Rec.key : Rec → List Nat
  | .leaf k _ _ => k
  | .ext k _ _ => k
  | .branch .. => []

theorem gRecS_key {r : Nat} {x : Nat → Expr} {xf : Expr} {mb : Nat → Expr} :
    Rec.key (gRecS tr pub r x xf mb) = snKey tr pub r := by
  unfold gRecS; split <;> rfl

/-- **The reader's key** from the key length (part 0) and the nibbles of two publishers (parts 1,
2) whose keys equal the part-0 publisher's. -/
theorem key_of_parts {r a b c : Nat} (hka : E tr 3 r pub (Sn.c "klen") = E tr 3 a pub (Sn.c "klen"))
    (hla : ev tr 3 a pub (Sn.c "klen") ≤ 64)
    (h1 : ∀ j, j < 32 → E tr 3 r pub (Sn.c "k" j) = E tr 3 b pub (Sn.c "k" j))
    (h2 : ∀ j, j < 32 → E tr 3 r pub (Sn.c "k" (32 + j)) = E tr 3 c pub (Sn.c "k" (32 + j)))
    (hb : snKey tr pub b = snKey tr pub a) (hc : snKey tr pub c = snKey tr pub a) :
    snKey tr pub r = snKey tr pub a := by
  have hkl : ev tr 3 r pub (Sn.c "klen") = ev tr 3 a pub (Sn.c "klen") := congrArg Fp.toNat hka
  have lb : ev tr 3 b pub (Sn.c "klen") = ev tr 3 a pub (Sn.c "klen") := by
    have := congrArg List.length hb; simpa [snKey, FieldRows2.keyOf] using this
  have lc : ev tr 3 c pub (Sn.c "klen") = ev tr 3 a pub (Sn.c "klen") := by
    have := congrArg List.length hc; simpa [snKey, FieldRows2.keyOf] using this
  apply List.ext_getElem?
  intro j
  simp only [snKey, FieldRows2.keyOf, List.getElem?_map, List.getElem?_range'] at *
  rcases Nat.lt_or_ge j (ev tr 3 a pub (Sn.c "klen")) with hj | hj
  · rw [List.getElem?_range (by omega), List.getElem?_range hj]
    simp only [Option.map_some, Option.some.injEq]
    rcases Nat.lt_or_ge j 32 with hj32 | hj32
    · have e := congrArg (fun l => l[j]?) hb
      simp only [List.getElem?_map, List.getElem?_range (show j < ev tr 3 b pub (Sn.c "klen") by omega),
        List.getElem?_range hj, Option.map_some, Option.some.injEq] at e
      rw [← e]; exact congrArg Fp.toNat (h1 j hj32)
    · have e := congrArg (fun l => l[j]?) hc
      simp only [List.getElem?_map, List.getElem?_range (show j < ev tr 3 c pub (Sn.c "klen") by omega),
        List.getElem?_range hj, Option.map_some, Option.some.injEq] at e
      rw [← e]
      have := h2 (j - 32) (by omega)
      rw [show 32 + (j - 32) = j by omega] at this
      exact congrArg Fp.toNat this
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    rfl

end

end StateM5a.SnStore
