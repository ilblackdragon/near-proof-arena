import ZkFormal.NearV3.Render.Ups.CompactExtract.HeaderBits
import ZkFormal.NearV3.Render.Ups.CompactExtract.PartFresh
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
attribute [local irreducible] UpsSeg.row UpsSeg.next
section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s∈v)
include hw hs
theorem tagField {r : Nat} (hU : UField s r 1) (hst : stOf (s.row r) = 0) (hlt : r + 1 ≤ s.rows.length)
    (hq : s.row r qb = 1) (hpf : s.row r pf = 1) :
    rowsB s r 1 = [s.row r qtb1 + 2 * s.row r qtb2 + 3 * s.row r qte] := by
  have R := fieldRowSt hw hs hU hst hlt (fun d hd => by rw [show d = 0 by omega, Nat.add_zero]; exact hq) 0 (by omega)
  simp only [Nat.add_zero] at R
  have h1 := (stOf_inv R.1).1 R.2
  rw [rowsB_one, (gramRow (okRow hw hs (i := r) (by omega)) (rowLt hw hs _) (nextLt hw hs _) R.1.sum).1 h1 hpf]

/-- The full four-byte header, with local digit bounds and no short-prefix premise. -/
theorem hplField {r : Nat} (hU : UField s r 4) (hst : stOf (s.row r) = 1) (hlt : r + 4 ≤ s.rows.length)
    (hq : ∀ d, d < 4 → s.row (r + d) qb = 1) :
    rowsB s r 4 = u32Bytes (s.row (r+3) qhk) := by
  have R := fieldRowSt hw hs hU hst hlt hq
  have H := fun d (hd : d<4) => (stOf_inv (R d hd).1).2.1 (R d hd).2
  have fe0 : ∀ d, d<3 → s.row (r+d) fe=0 := by
    intro d hd
    rcases rowBool (okRow hw hs (i:=r+d) (by omega)) (rowLt hw hs _) (x:=fe) (by decide) with h|h
    · exact h
    · have := (hU.fe d (by omega)).1 h; omega
  have fe3 := (hU.fe 3 (by omega)).2 rfl
  have fs0 := (hU.fs 0 (by omega)).2 rfl
  have O := fun d (hd : d<4) => okRow hw hs (i:=r+d) (by omega)
  have a0 := bHPL0 (O 0 (by omega)) (rowLt hw hs _) (R 0 (by omega)).1.sum (H 0 (by omega)) fs0
  have sc0 := bHPLr (O 0 (by omega)) (rowLt hw hs _) (R 0 (by omega)).1.sum (H 0 (by omega)) fs0
  have step := fun d (hd : d<3) => hplStep (O d (by omega)) (rowLt hw hs _)
    (R d (by omega)).1.sum (H d (by omega)) (fe0 d hd)
  have scale := fun d (hd : d<3) => hplScale (O d (by omega)) (rowLt hw hs _)
    (R d (by omega)).1.sum (H d (by omega)) (fe0 d hd)
  have e3 := hplEnd (O 3 (by omega)) (rowLt hw hs _) (R 3 (by omega)).1.sum (H 3 (by omega)) fe3
  have top := hplTop (O 3 (by omega)) (rowLt hw hs _) (R 3 (by omega)).1.sum (H 3 (by omega)) fe3
  have hb3 : s.row (r+3) b=0 := natv (rowLt hw hs _ _) (by unfold P; omega) (by simpa only [cast0] using top)
  have hb := fun d (hd : d<4) => headerByte_lt (O d hd) (rowLt hw hs _) (R d hd).1.sum (H d hd)
  have st1 := step 0 (by omega); have st2 := step 1 (by omega); have st3 := step 2 (by omega)
  have sc1 := scale 0 (by omega); have sc2 := scale 1 (by omega); have sc3 := scale 2 (by omega)
  rw [compactNext (s:=s) (i:=r+0) (by omega)] at st1 sc1
  rw [compactNext (s:=s) (i:=r+1) (by omega)] at st2 sc2
  rw [compactNext (s:=s) (i:=r+2) (by omega)] at st3 sc3
  simp only [Nat.add_zero,Nat.add_assoc] at st1 st2 st3 sc1 sc2 sc3 a0 sc0
  have hv : le256 (rowsB s r 4)=s.row (r+3) qhk := by
    rw [rowsB_four,hb3]
    simp only [le256]
    have h0 := hb 0 (by omega); have h1 := hb 1 (by omega); have h2 := hb 2 (by omega)
    simp only [Nat.add_zero] at h0
    apply natv (by unfold P; omega) (rowLt hw hs _ _)
    rw [← e3,st3,sc3,st2,sc2,st1,sc1,sc0,a0]
    simp only [natCast_add,natCast_mul,hb3,cast0]
    grind
  have hby : ∀ x∈rowsB s r 4,x<256 := by
    intro x hx
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hx
    exact hb d (List.mem_range.mp hd)
  rw [← hv]
  exact (u32Bytes_of_digits _ (by simp [rowsB]) hby).symm

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
