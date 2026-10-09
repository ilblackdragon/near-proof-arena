import ZkFormal.NearV3.Render.Ups.CompactExtract.RbrBytes
import ZkFormal.NearV3.Extract.Ups.KidsBytes
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- **Window flags**: windows `e < w` at `r + 32e` (preceded by a non-window row, followed by
the `MEM` field): `fw = [e = 0]`, `lastw = [e = w − 1]`. -/
theorem winFlags {r w : Nat} (hw0 : 0 < w) (hlt : r + 32 * w < s.rows.length) (hr : 0 < r)
    (hprev : s.row (r - 1) sCH = 0)
    (W : ∀ e, e < w → UField s (r + 32 * e) 32 ∧ (∀ d, d < 32 → s.row (r + 32 * e + d) sCH = 1))
    (hmem : s.row (r + 32 * w) sMEM = 1) (hchM : s.row (r + 32 * w) sCH = 0) :
    ∀ e, e < w → ∀ d, d < 32 → s.row (r + 32 * e + d) fw = (if e = 0 then 1 else 0) ∧
      s.row (r + 32 * e + d) lastw = (if e + 1 = w then 1 else 0) := by
  have st := fun i (hi : i < s.rows.length) => winStep (okRow hw hs hi) (rowLt hw hs _) (nextLt hw hs _)
  have nx := fun i (hi : i + 1 < s.rows.length) => compactNext (s:=s) (i := i) hi
  have fe0 : ∀ e, e < w → ∀ d, d < 31 → s.row (r + 32 * e + d) fe = 0 := fun e he d hd => by
    rcases rowBool (okRow hw hs (i := r + 32 * e + d) (by omega)) (rowLt hw hs _) (x := fe) (by decide) with h | h
    · exact h
    · have := ((W e he).1.fe d (by omega)).1 h; omega
  have fe1 : ∀ e, e < w → s.row (r + 32 * e + 31) fe = 1 := fun e he => ((W e he).1.fe 31 (by omega)).2 rfl
  -- the flags are constant inside a window
  have inW : ∀ e, e < w → ∀ d, d < 32 → s.row (r + 32 * e + d) fw = s.row (r + 32 * e) fw ∧
      s.row (r + 32 * e + d) lastw = s.row (r + 32 * e) lastw := by
    intro e he d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hd
      have h := (st (r + 32 * e + d) (by omega)).2.1 ((W e he).2 d (by omega)) (fe0 e he d (by omega))
      rw [nx _ (by omega), show r + 32 * e + d + 1 = r + 32 * e + (d + 1) by omega] at h
      rw [h.1, h.2.1]; exact ih (by omega)
  -- first rows
  have first : ∀ e, e < w → s.row (r + 32 * e) fw = (if e = 0 then 1 else 0) := by
    intro e he
    rcases e with _ | e
    · have := (st (r - 1) (by omega)).1 hprev (by
        rw [nx _ (by omega), show r - 1 + 1 = r by omega]; simpa using (W 0 hw0).2 0 (by omega))
      rw [nx _ (by omega), show r - 1 + 1 = r by omega] at this
      simpa using this
    · have := (st (r + 32 * e + 31) (by omega)).2.2.1 ((W e (by omega)).2 31 (by omega)) (fe1 e (by omega))
        (by
          rw [nx _ (by omega)]
          have := (W (e + 1) he).2 0 (by omega); rwa [show r + 32 * (e + 1) + 0 = r + 32 * e + 31 + 1 by omega] at this)
      rw [nx _ (by omega), show r + 32 * e + 31 + 1 = r + 32 * (e + 1) by omega] at this
      simpa using this
  have last : ∀ e, e < w → s.row (r + 32 * e) lastw = (if e + 1 = w then 1 else 0) := by
    intro e he
    have := (st (r + 32 * e + 31) (by omega)).2.2.2 ((W e he).2 31 (by omega)) (fe1 e he)
    rw [nx _ (by omega)] at this
    rw [← (inW e he 31 (by omega)).2, this]
    split
    · next h => rw [show r + 32 * e + 31 + 1 = r + 32 * w by omega, hmem]
    · next h =>
      have := (W (e + 1) (by omega)).2 0 (by omega)
      rw [show r + 32 * (e + 1) + 0 = r + 32 * e + 31 + 1 by omega] at this
      have hoh := le1 (rowBool (okRow hw hs (i := r + 32 * e + 31 + 1) (by omega)) (rowLt hw hs _) (x := sMEM)
        (by simp [rowBools, states]))
      have := stSum (okRow hw hs (i := r + 32 * e + 31 + 1) (by omega)) (rowLt hw hs _)
      have := le1 (rowBool (okRow hw hs (i := r + 32 * e + 31 + 1) (by omega)) (rowLt hw hs _) (x := qb)
        (by simp [rowBools]))
      omega
  intro e he d hd
  rw [(inW e he d hd).1, (inW e he d hd).2, first e he, last e he]
  exact ⟨rfl, rfl⟩

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
