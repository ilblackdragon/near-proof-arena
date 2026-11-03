namespace SegSha

/-- **The chip hypothesis without table 20** (`ChipIf` minus the bus-103 balance of table 20): the
chip contract, its id bound, and every bus-103 receive with count 1 of a table `≠ 20` is a chip
message.  `ChipIf … (wasmBaseSegAir …)` and `ChipIf … (wasmBaseSegAirMP …)` both imply it, with the
respective `HoldsX` (`ChipIf.toS`, `ChipIf.toSMP`). -/
structure ChipIfS (compress : List Nat → List Nat → List Nat) (nloc ngl : Nat) (pub : List F) (tr : Trace)
    (chip : List IfMsg) : Prop where
  contract : Sha512IfContract compress chip
  cidLt : ∀ x ∈ chip, x.cid < P
  recv : ∀ t (ht : t < (wasmBaseSegAir nloc ngl).tables.length), t ≠ 20 → ∀ r, r < tr.height t →
    ∀ i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters, i.bus = extBus →
      (i.count.eval (tr.row pub t r)).toNat = 1 → i.msg.map (·.eval (tr.row pub t r)) ∈ chip.map ifF

/-- `if_recv_mem` for `ChipIfS`: a bus-103 receive with count 1 of a table `≠ 20` is a chip message. -/
theorem if_recv_memS {compress : List Nat → List Nat → List Nat} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {chip : List IfMsg} (hC : ChipIfS compress nloc ngl pub tr chip)
    {t : Nat} (ht : t < (wasmBaseSegAir nloc ngl).tables.length) (h20 : t ≠ 20) {r : Nat} (hr : r < tr.height t)
    {i : Inter} (hi : i ∈ ((wasmBaseSegAir nloc ngl).tables[t]'ht).inters) (hb : i.bus = extBus)
    (hc : (i.count.eval (tr.row pub t r)).toNat = 1) :
    i.msg.map (·.eval (tr.row pub t r)) ∈ chip.map ifF :=
  hC.recv t ht h20 r hr i hi hb hc

/-- `ChipIf` of the M4 AIR implies `ChipIfS` (`if_recv_mem`). -/
theorem ChipIf.toS {compress : List Nat → List Nat → List Nat} {nloc ngl : Nat} {pub : List F} {tr : Trace}
    {chip : List IfMsg} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
    (hC : ChipIf compress (wasmBaseSegAir nloc ngl) pub tr chip) : ChipIfS compress nloc ngl pub tr chip where
  contract := hC.contract
  cidLt := hC.cidLt
  recv t ht _ r hr i hi hb hc := if_recv_mem H hC (occ_of_inter ht hr hi hc) hb rfl

end SegSha
