import M5T1.SpecLink

/-!
# M5T1.T1 — non-vacuity on T1 (`d3c8/d3/02-h10196-s3`)

`t1Vals` is the decoded `RX` row of T1's proved trace (`rxvals.py` over the prover's `RX.bin`;
every value asserted by `tracegen.py` against the Lean checker's run, `m5t1-tool dump`).
`t1_rel`: it satisfies `RxRel` (kernel `decide`), so `RxField.rx_rel_of_row`'s conclusion and the
`SpecLink` premises are inhabited by T1. `t1_spec`: the spec's own functions on T1's receipt give
the Lean run's values — gas burnt `1009188008301`, refund `54888077387472000000000`, tokens burnt
`0`, the receiver's new balance `36001000000000000000000000` — through `SpecLink`.
-/

namespace M5T1.T1

open M5T1 M5T1.SpecLink

def t1Vals : RxVals :=
{ lm := 3, la := 5, gp := 1000000000, egp := 0, gas := 54000000000000,
  dep := 1000000000000000000000, amt := 36000000000000000000000000, lck := 0,
  vb := 121110620829, vu := 121110620829, vc := 275833884829,
  vbal := 36001000000000000000000000, vus := 573, vsub := 0, fcx := 780017887472,
  gb := 1009188008301, gu := 1009188008301, cu := 1163911272301, req := 5730000000000000000000,
  burn := 0, pexec := 888077387472, tot := 54888077387472, gross := 53878889379171,
  unu := 53878889379171000000000, gpb := 1000000000, sur := 1009188008301000000000, bc := 0,
  rf := 54888077387472000000000, tb := 0, q10 := 36333186248, rew := 0,
  amt2 := 36001000000000000000000000, txb := 0, glim := 1000000000000000, gin := 568551750000,
  cin := 568551750000, tbin := 0, sbin := 0, wgin := 0, gout := 1577739758301,
  cout := 1732463022301, tbout := 0, sbout := 0, wgout := 121110620829 }

theorem t1_rel : RxRel t1Vals := by
  constructor <;> decide

/-- On T1 the spec's refund, stake, merge, burnt and totals computations give the Lean run's values. -/
theorem t1_spec : storageStakeOk ⟨t1Vals.vbal, t1Vals.lck, t1Vals.vus, .none, false⟩ t1Vals.vbal = some true ∧
    t1Vals.gb = 1009188008301 ∧ t1Vals.rf = 54888077387472000000000 ∧ t1Vals.tb = 0 ∧
    t1Vals.amt2 = 36001000000000000000000000 ∧ t1Vals.gout = 1577739758301 :=
  ⟨stake_fc t1Vals t1_rel _, rfl, rfl, rfl, rfl, rfl⟩

end M5T1.T1
