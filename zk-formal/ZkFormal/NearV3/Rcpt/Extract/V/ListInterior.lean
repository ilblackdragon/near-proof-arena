import ZkFormal.NearV3.Rcpt.Extract.V.ListTerminal
import ZkFormal.NearV3.Rcpt.Extract.V.Gates

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Every row of a receipt is active and is not a list header. -/
theorem Layout.row_flags {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (k : Nat) (hk : k<y.tot) :
    tr.cell tt (y.s+k) act=1 ∧ tr.cell tt (y.s+k) sCL=0 := by
  obtain ⟨f,hf,hlo,hhi⟩ := plan_cover y.h y.Lp y.Lv y.Ls y.kt k hk
  have hs := (h.flds f hf).fld.st (k-f.2.1) (by omega)
  rw [show y.s+f.2.1+(k-f.2.1)=y.s+k by omega] at hs
  have hfin := h.fin
  have hp := plan_states y.h y.Lp y.Lv y.Ls y.kt f hf
  have hh := oneHot hL (r := y.s+k) (by unfold RS.tot at hk; omega) hp.1 hs
  exact ⟨hh.1,hh.2 sCL (by simp [states]) hp.2.symm⟩

/-- An interior receipt row cannot emit a list-end message. -/
theorem Layout.interior_le_zero {y : RS} (h : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (k : Nat) (hk : k+1<y.tot) : tr.cell tt (y.s+k) le=0 := by
  have hf := h.row_flags hL k (by omega)
  have hfin := h.fin
  have hr := rl_row hL h k (by unfold RS.tot at hk; omega)
  rw [if_neg (by unfold RS.tot at hk; omega)] at hr
  have he := (le_eq hL (r := y.s+k) (by unfold RS.tot at hk; omega)).1
  rw [hr,hf.2] at he
  rw [he]
  grind

/-- A receipt followed by another receipt cannot finish the list. -/
theorem Layout.followed_le_zero {y z : RS}
    (hy : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (hz : Layout tr tt z.s z.h z.Lp z.Lv z.Ls z.kt)
    (hs : z.s=y.s+y.tot) : tr.cell tt (y.s+y.tot-1) le=0 := by
  have hp := total_pos y.h y.Lp y.Lv y.Ls y.kt
  have hfin := hy.fin
  have he : y.s+y.tot-1+1=z.s := by unfold RS.tot at *; omega
  have hh := (le_eq hL (r := y.s+y.tot-1) (by unfold RS.tot; omega)).1
  rw [he,(hz.start_flags hL).2.2] at hh
  rw [hh]
  grind

/-- The first eleven header rows cannot finish a list. -/
theorem ListBlockWf.header_interior_le_zero {B : ListBlock} (h : ListBlockWf tr tt B)
    (k : Nat) (hk : k<11) : tr.cell tt (B.start+k) le=0 := by
  have hfin := h.header_fin
  have hr := fld_rl0 hL (by omega) h.header (by simp [states]) (by decide) (by decide) k (by omega)
  have hf : tr.cell tt (B.start+k) fe=0 := by
    have hh := h.header.fe k (by omega)
    simpa only [if_neg (show ¬k+1=12 by omega)] using hh
  have hh := (le_eq hL (r := B.start+k) (by omega)).1
  rw [hr,hf] at hh
  rw [hh]
  grind

end ZkFormal.NearV3.RcptV3Proof
