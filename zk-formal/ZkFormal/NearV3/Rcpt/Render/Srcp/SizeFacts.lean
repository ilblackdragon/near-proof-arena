import ZkFormal.NearV3.Rcpt.Render.Srcp.Duplicate

namespace ZkFormal.NearV3.Render.SrcpGen

def rowCharge (bs : List SrcpB) (r : Nat) : Nat :=
  cell bs r SrcpV3.rt * cell bs r SrcpV3.L +
    33 * (cell bs r SrcpV3.sf * cell bs r SrcpV3.sg * (1 - cell bs r SrcpV3.lf))

theorem active_charge (bs : List SrcpB) (r : Nat) (hr : r < R bs) :
    rowCharge bs r = chargeKind (bs.getD ((recs bs).getD r default).1 default)
      ((recs bs).getD r default).2 := by
  simp only [rowCharge, cell, hr, ite_true, rowFrame]
  exact (charge_gate _ _ _).symm

theorem padding_charge (bs : List SrcpB) (r : Nat) (hr : R bs ≤ r) : rowCharge bs r = 0 := by
  simp [rowCharge, padding_cell hr, SrcpV3.rt, SrcpV3.L, SrcpV3.sf, SrcpV3.sg, SrcpV3.lf, SrcpV3.sz]

theorem last_size_cell {bs : List SrcpB} (h : SrcpWf bs) :
    cell bs (R bs - 1) SrcpV3.sz = srcpSize bs := by
  have hr : R bs - 1 < R bs := by have := R_pos h; omega
  have hp : 0 < bs.length := by have hh := h.nonempty; cases bs <;> simp_all
  have hi : bs.length - 1 < bs.length := by omega
  have hn : bs.length - 1 + 1 = bs.length := by omega
  simp only [cell, hr, ite_true, lastAt h, rowFrame]
  change (frame _ _ (lastKind _)).sz = _
  rw [last_size]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp only [Option.getD_some]
  rw [← before_next _ hi, hn, before_end]

theorem cross_size {bs : List SrcpB} (i : Nat) (hi : i + 1 < bs.length) :
    (rootFrame (bs.getD (i + 1) default) (before bs (i + 1))).sz =
      (frame (bs.getD i default) (before bs i) (lastKind (bs.getD i default))).sz +
        (bs.getD (i + 1) default).L := by
  have hp : i < bs.length := by omega
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hp]
    using next_root_size i hi

end ZkFormal.NearV3.Render.SrcpGen
