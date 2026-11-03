import StateM5a.RowSn

/-!
# StateM5a.RowSnMsg — an `SN` walk row's decoded record and messages

The row's old record `snOld` under its input ref `snIn` (a leaf `snKey ↦ (vlen, vh)` when
`isL = 1`, otherwise an extension `snKey → snChild`), the decoded walk row `snRow` (as
`DecodeWalk.rowsOf cDc snW` produces it), and its four decoded messages (`sn_din`, `sn_dout`,
`sn_uin`, `sn_uout`).
-/

namespace StateM5a.RowSnMsg

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.RowBr StateM5a.RowBrMsg StateM5a.RowSn

set_option maxRecDepth 100000

section
variable (tr : Trace Fp) (pub : List Fp) (r : Nat)

/-- Field values on `SN` row `r`. -/
abbrev sE (e : Expr) : Fp := e.eval tr 3 r pub

def snIn : Ref := refOf (sE tr pub r (Sn.c "oref")) ((pack2 fun b => Sn.c "ho" b).map (sE tr pub r))
/-- The head key (`klen` nibbles). -/
def snKey : List Nat := FieldRows2.keyOf tr 3 r pub
def snChild : Ref := refOf (sE tr pub r (Sn.c "xf")) ((pack2 fun b => Sn.c "x" b).map (sE tr pub r))
def snMem : Nat := le4 (Sn.M.map (sE tr pub r))
def snVal : Slot :=
  .ref (ev tr 3 r pub (Sn.vlenOf fun t => Sn.c "x" t)) (bytesOf ((pack2 fun b => Sn.c "x" (4 + b)).map (sE tr pub r)))

/-- **The old record** of an `SN` row. -/
def snOld : Rec :=
  if ev tr 3 r pub (Sn.c "isL") = 1 then .leaf (snKey tr pub r) (snVal tr pub r) (snMem tr pub r)
  else .ext (snKey tr pub r) (snChild tr pub r) (snMem tr pub r)

/-- The decoded walk row of `SN` row `r` (as `rowsOf`). -/
def snRow : WRow Ref Pay Res :=
  { din := cDc.down (vals tr 3 r pub snW.di),
    dout := if snW.gdn.eval tr 3 r pub = 1 then some (cDc.down (vals tr 3 r pub snW.dd)) else none,
    uin := cDc.dr ((vals tr 3 r pub snW.ui).drop 2),
    uout := cDc.dr ((vals tr 3 r pub snW.uo).drop 2) }

end

theorem mem_snRows {tr : Trace Fp} {pub : List Fp} {x : WRow Ref Pay Res}
    (hx : x ∈ rowsOf cDc snW tr 3 pub) :
    ∃ r, r < tr.height 3 ∧ snW.g.eval tr 3 r pub = 1 ∧ x = snRow tr pub r :=
  DecodeShape.mem_rowsOf hx

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem sn_din : cDc.down (vals tr 3 r pub snW.di) =
    ⟨ev tr 3 r pub (Sn.c "w"), ev tr 3 r pub (Sn.c "d"), snIn tr pub r,
      payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))⟩ := by
  rw [sn_di, down_eq _ _ _ _ _ (len_pack2 _)]; rfl

theorem sn_dout : cDc.down (vals tr 3 r pub snW.dd) =
    ⟨ev tr 3 r pub (Sn.c "w"), ev tr 3 r pub (Sn.c "d" + Sn.c "klen"), snChild tr pub r,
      payOf ((payE (fun s j => Sn.c s j) Sn.mode).map (E tr 3 r pub))⟩ := by
  rw [sn_dd, down_eq _ _ _ _ _ (len_pack2 _)]; rfl

theorem sn_uin : cDc.dr ((vals tr 3 r pub snW.ui).drop 2) =
    ⟨ev tr 3 r pub (Sn.c "rkc"),
      refOf (E tr 3 r pub ((Sn.c "oEU" + Sn.c "oEB") * Sn.c "nxf" + Sn.c "oES" * Sn.c "xf"))
        ((((pack2 (fun b => Sn.c "nx" b)).zip (pack2 fun b => Sn.c "x" b)).map
          (fun (p, q) => (Sn.c "oEU" + Sn.c "oEB") * p + Sn.c "oES" * q)).map (E tr 3 r pub)),
      le4 (((List.range 4).map fun t => (Sn.c "oEU" + Sn.c "oEB") * Sn.c "unm" t).map (E tr 3 r pub)),
      le4 (((List.range 4).map fun t => Sn.c "uom" t).map (E tr 3 r pub)),
      ev tr 3 r pub (Sn.c "oED" * Sn.c "kid2"), ev tr 3 r pub (Sn.c "oED" * (Sn.c "d" + Sn.c "klen")),
      ev tr 3 r pub ((Sn.c "oEF" + Sn.c "oED") * Sn.c "alen"),
      bytesOf (((List.range 16).map fun i => (Sn.c "oEF" + Sn.c "oED") * Sn.c "avh" i).map (E tr 3 r pub)),
      ev tr 3 r pub (Sn.c "oEF" * Sn.c "fpres")⟩ := by
  rw [sn_ui, up_eq _ _ _ _ _ _ _ _ _ _ _ _ (by simp [pack2]) (by simp) (by simp) (by simp)]

theorem sn_uout : cDc.dr ((vals tr 3 r pub snW.uo).drop 2) =
    ⟨ev tr 3 r pub rkE,
      refOf (E tr 3 r pub (gnu * Sn.c "nref" + Sn.gS * Sn.c "oref" + Sn.gX * Sn.c "shf"))
        ((((pack2 (fun b => Sn.c "hn" b)).zip (pack2 fun b => Sn.c "ho" b)).zip
          ((List.range 16).map fun i => Sn.c "sh" i)).map
          (fun ((p, q), s) => gnu * p + Sn.gS * q + Sn.gX * s) |>.map (E tr 3 r pub)),
      le4 (((Sn.NM.zip ((List.range 4).map fun t => Sn.c "sm" t)).map fun (p, s) => gnu * p + Sn.gX * s).map
        (E tr 3 r pub)),
      le4 ((Sn.M.map ((Sn.c "mU" + Sn.c "mD") * ·)).map (E tr 3 r pub)),
      ev tr 3 r pub (Sn.c "oED" * Sn.c "kid2"), ev tr 3 r pub (Sn.c "oED" * Sn.c "d"),
      ev tr 3 r pub (Sn.c "oLF" * Sn.vlenOf (fun t => Sn.c "x" t) + (Sn.c "oEF" + Sn.c "oED") * Sn.c "alen"),
      bytesOf (((pack2 fun b => Sn.c "x" (4 + b)).zip ((List.range 16).map fun i => Sn.c "avh" i)).map
        (fun (p, q) => Sn.c "oLF" * p + (Sn.c "oEF" + Sn.c "oED") * q) |>.map (E tr 3 r pub)),
      ev tr 3 r pub (Sn.c "oLF" + Sn.c "oEF" * Sn.c "fpres")⟩ := by
  rw [sn_uo, up_eq _ _ _ _ _ _ _ _ _ _ _ _ (by simp [pack2]) (by simp [Sn.NM, memLimbs])
    (by simp [Sn.M, memLimbs]) (by simp [pack2])]

end

end StateM5a.RowSnMsg
