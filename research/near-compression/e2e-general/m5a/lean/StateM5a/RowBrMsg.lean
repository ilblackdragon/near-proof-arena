import StateM5a.RowBr

/-!
# StateM5a.RowBrMsg — a `BR` walk row's decoded record and messages

The row's old node `brOld` (value from `hasv`/`vl`/`vh`, slots from `f`/`isn`/`ch`, memory from
the `mem` limbs) under its input ref `brIn`, decoded with the same ref / byte decoders as
`RowDec.cDc`, and the decoded `DOWN` / `UP` messages of the row (`br_din`, `br_dout`, `br_uin`,
`br_uout`): each field is the field value of the row's expression.
-/

namespace StateM5a.RowBrMsg

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr

set_option maxRecDepth 100000

section
variable (tr : Trace Fp) (pub : List Fp) (r : Nat)

/-- Field values on `BR` row `r`. -/
abbrev bE (e : Expr) : Fp := e.eval tr 2 r pub

/-- The input ref. -/
def brIn : Ref := refOf (bE tr pub r (Br.c "oref")) ((pack2 fun b => Br.c "ho" b).map (bE tr pub r))

/-- The ref of old slot `i`. -/
def brSlot (i : Nat) : Ref :=
  refOf (bE tr pub r (Br.c "isn" i)) ((pack2 fun b => Br.ch i b).map (bE tr pub r))

def brKids : RKids := kidsFrom (fun i => ev tr 2 r pub (Br.c "f" i)) (brSlot tr pub r) 0 16

/-- The old value length, as a natural from its two 16-bit limbs (no field wrap). -/
def brVlen : Nat :=
  (bE tr pub r (limb16 (fun t => Br.c "vl" t) 0)).toNat + 65536 * (bE tr pub r (limb16 (fun t => Br.c "vl" t) 1)).toNat

/-- The old value slot. -/
def brVal : Option Slot :=
  if ev tr 2 r pub (Br.c "hasv") = 1 then
    some (.ref (brVlen tr pub r)
      (bytesOf ((pack2 fun b => Br.c "vh" b).map (bE tr pub r))))
  else none

def brMem : Nat := le4 (Br.M.map (bE tr pub r))

/-- **The old node** of a `BR` row. -/
def brOld : Rec := .branch (brVal tr pub r) (brKids tr pub r) (brMem tr pub r)

end

/-! ## The messages -/

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem len_pack2 (f : Nat → Expr) : (pack2 f).length = 16 := by simp [pack2]

theorem br_din : cDc.down (vals tr 2 r pub brW.di) =
    ⟨ev tr 2 r pub (Br.c "w"), ev tr 2 r pub (Br.c "d"), brIn tr pub r,
      payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))⟩ := by
  rw [br_di, down_eq _ _ _ _ _ (len_pack2 _)]; rfl

theorem br_dout : cDc.down (vals tr 2 r pub brW.dd) =
    ⟨ev tr 2 r pub (Br.c "w"), ev tr 2 r pub (Br.c "d" + 1),
      refOf (E tr 2 r pub Br.isnSel) ((pack2 Br.chSel).map (E tr 2 r pub)),
      payOf ((payE (fun s j => Br.c s j) Br.mode).map (E tr 2 r pub))⟩ := by
  rw [br_dd, down_eq _ _ _ _ _ (len_pack2 _)]

theorem br_uin : cDc.dr ((vals tr 2 r pub brW.ui).drop 2) =
    ⟨ev tr 2 r pub (Br.c "rk"),
      refOf (E tr 2 r pub ((Br.c "oUD" + Br.c "oDH") * Br.c "nhf" + Br.c "oDS" * Br.isnSel))
        ((((pack2 (fun b => Br.c "nh" b)).zip (pack2 Br.chSel)).map
          (fun (p, q) => (Br.c "oUD" + Br.c "oDH") * p + Br.c "oDS" * q)).map (E tr 2 r pub)),
      le4 (((List.range 4).map fun k => (Br.c "oUD" + Br.c "oDH") * Br.c "nm" k).map (E tr 2 r pub)),
      le4 (((List.range 4).map fun k => Br.c "om" k).map (E tr 2 r pub)),
      ev tr 2 r pub (Br.c "oDL" * Br.c "kid2"), ev tr 2 r pub (Br.c "oDL" * Br.c "st2"),
      ev tr 2 r pub ((Br.c "oFD" + Br.c "oDL") * Br.c "lvlen"),
      bytesOf (((List.range 16).map fun i => (Br.c "oFD" + Br.c "oDL") * Br.c "lvh" i).map (E tr 2 r pub)),
      ev tr 2 r pub (Br.c "oFD" * Br.c "fpres")⟩ := by
  rw [br_ui, up_eq _ _ _ _ _ _ _ _ _ _ _ _ (by simp [pack2]) (by simp) (by simp) (by simp)]

theorem br_uout : cDc.dr ((vals tr 2 r pub brW.uo).drop 2) =
    ⟨ev tr 2 r pub (Br.c "oUD" + Br.c "oUN" + Br.c "oUV" + sm 2 (Br.gKeep + Br.c "oDV") + sm 4 (Br.c "oD1") +
        sm RK_SAME Br.gSame),
      refOf (E tr 2 r pub (Br.c "gnew" * Br.c "nref" + Br.gSame * Br.c "oref"))
        ((((pack2 (fun b => Br.c "hn" b)).zip (pack2 fun b => Br.c "ho" b)).map
          (fun (p, q) => Br.c "gnew" * p + Br.gSame * q)).map (E tr 2 r pub)),
      le4 ((Br.NM.map (Br.c "gnew" * ·)).map (E tr 2 r pub)),
      le4 ((Br.M.map ((Br.c "mU" + Br.c "mD") * ·)).map (E tr 2 r pub)),
      ev tr 2 r pub (Br.c "oD1" * Br.c "kid2"), ev tr 2 r pub (Br.c "oD1" * Br.c "d"),
      ev tr 2 r pub ((Br.c "oFD" + Br.c "oD1") * Br.c "lvlen" + Br.c "oFV" * Br.vlen),
      bytesOf ((((List.range 16).zip (pack2 fun b => Br.c "vh" b)).map
        (fun (i, p) => (Br.c "oFD" + Br.c "oD1") * Br.c "lvh" i + Br.c "oFV" * p)).map (E tr 2 r pub)),
      ev tr 2 r pub (Br.c "oFD" * Br.c "fpres" + Br.c "oFV" * Br.c "hasv")⟩ := by
  rw [br_uo, up_eq _ _ _ _ _ _ _ _ _ _ _ _ (by simp [pack2]) (by simp [Br.NM, memLimbs])
    (by simp [Br.M, memLimbs]) (by simp [pack2])]

/-- `pack2` of pointwise-equal byte expressions evaluates equally. -/
theorem pack2_eval {f g : Nat → Expr} (h : ∀ b, (f b).eval tr 2 r pub = (g b).eval tr 2 r pub) :
    (pack2 f).map (E tr 2 r pub) = (pack2 g).map (E tr 2 r pub) := by
  simp only [pack2, List.map_map]
  congr 1; funext i
  simp only [Function.comp, E, eval_add, eval_mul, h]

end

end StateM5a.RowBrMsg
