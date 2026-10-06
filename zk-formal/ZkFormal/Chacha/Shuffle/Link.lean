import ZkFormal.Chacha.Shuffle.Contract
import ZkFormal.Chacha.Link

/-!
# ZkFormal.Chacha.Shuffle.Link — the shuffle table inside a v2 AIR

From `HoldsP`: the `gen_index` receives of `shufV3` are matched by `genV3` (the only sender on
`busGen`, `genRecv_of_holdsP`), and the private memory bus balances inside the table
(`memBal_of_holdsP`).  Hence `shuffle_sound`.
-/

namespace ZkFormal.Chacha

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3 ZkFormal.Chacha.Shuffle

variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

theorem tableBusCount_none {is : List Interaction} {t : Nat} {b : Nat} {s : Bool} {m : List Fp}
    (h : ∀ i ∈ is, i.bus ≠ b) : tableBusCount is tr t pub b s m = 0 := by
  apply Classical.byContradiction; intro hne
  obtain ⟨r, -, i, hi, hb, -⟩ := exists_of_tableBusCount hne
  exact h i hi hb

theorem busCount_go_single (b : Nat) (s : Bool) (m : List Fp) (ts : Nat) :
    ∀ (Ts : List Air.Table) (k : Nat),
      (∀ u, u < Ts.length → k + u ≠ ts → ∀ i ∈ Ts[u]!.interactions, i.bus ≠ b) →
      busCount.go tr pub b s m Ts k =
        if k ≤ ts ∧ ts < k + Ts.length then tableBusCount Ts[ts - k]!.interactions tr ts pub b s m else 0
  | [], k, _ => by simp [busCount.go]; intro h1 h2; omega
  | T :: Ts, k, h => by
    simp only [busCount.go]
    rw [busCount_go_single b s m ts Ts (k + 1) (fun u hu hne i hi => h (u + 1) (by simp; omega)
      (by omega) i (by simpa using hi))]
    by_cases e : k = ts
    · subst e
      rw [if_neg (by omega), if_pos (by simp)]
      simp
    · rw [tableBusCount_none (fun i hi => h 0 (by simp) (by omega) i (by simpa using hi)), Nat.zero_add]
      by_cases e2 : k + 1 ≤ ts ∧ ts < k + 1 + Ts.length
      · rw [if_pos e2, if_pos ⟨by omega, by simp; omega⟩]
        rw [show ts - k = (ts - (k + 1)) + 1 by omega]; simp
      · rw [if_neg e2, if_neg (by simp; omega)]

/-- **The private memory bus balances inside the shuffle table.** -/
theorem memBal_of_holdsP (hH : HoldsP AP pub tr) {ts : Nat} {B : Buses} (hts : ts < AP.tables.length)
    (hT : AP.tables[ts]! = Shuffle.Table.table B.bin B.bout B.mem B.gen B.shuf)
    (honly : ∀ u, u < AP.tables.length → u ≠ ts → ∀ i ∈ AP.tables[u]!.interactions, i.bus ≠ B.mem)
    (hpub : ∀ seg ∈ AP.pubSegs, seg.bus ≠ B.mem) : MemBal B tr ts pub := by
  intro m
  have hbal := hH.balance B.mem m
  rw [pubCount_zero (fun seg h1 h2 => absurd h2 (hpub seg h1)) _,
    pubCount_zero (fun seg h1 h2 => absurd h2 (hpub seg h1)) _] at hbal
  unfold busCount at hbal
  rw [busCount_go_single _ _ _ ts _ 0 (by simpa using honly),
    busCount_go_single _ _ _ ts _ 0 (by simpa using honly)] at hbal
  simp only [Nat.zero_le, Nat.zero_add, true_and, hts, if_true, Nat.sub_zero, hT] at hbal
  exact hbal

/-- **The `gen_index` receives of the shuffle table are `gen_index` results.** -/
theorem genRecv_of_holdsP (hH : HoldsP AP pub tr) {tc tg ts busChacha : Nat} {B : Buses}
    (hcg : busChacha ≠ B.gen)
    (htc : tc < AP.tables.length) (hTc : AP.tables[tc]! = Table.table busChacha)
    (htg : tg < AP.tables.length) (hTg : AP.tables[tg]! = Rng.Table.table busChacha B.gen)
    (hts : ts < AP.tables.length) (hTs : AP.tables[ts]! = Shuffle.Table.table B.bin B.bout B.mem B.gen B.shuf)
    (honlyC : ∀ t, t < AP.tables.length → t ≠ tc → ∀ i ∈ AP.tables[t]!.interactions,
      i.bus = busChacha → i.send = false)
    (hpubC : ∀ seg ∈ AP.pubSegs, seg.bus = busChacha → seg.send = false)
    (honlyG : ∀ t, t < AP.tables.length → t ≠ tg → ∀ i ∈ AP.tables[t]!.interactions,
      i.bus = B.gen → i.send = false)
    (hpubG : ∀ seg ∈ AP.pubSegs, seg.bus = B.gen → seg.send = false) :
    GenRecv tr ts pub := by
  intro r hr ha hf
  have hi : (Shuffle.Table.interactions B.bin B.bout B.mem B.gen B.shuf)[6]! ∈ AP.tables[ts]!.interactions := by
    rw [hTs]; simp [Shuffle.Table.table, Shuffle.Table.interactions]
  have hm : ((Shuffle.Table.interactions B.bin B.bout B.mem B.gen B.shuf)[6]!).multNat tr ts r pub ≠ 0 := by
    unfold Interaction.multNat
    simp only [Shuffle.Table.interactions, List.getElem!_cons_succ, List.getElem!_cons_zero,
      Interaction.multNat.go]
    have : Shuffle.Table.gStep.eval tr ts r pub = 1 := by
      rw [eval_eq]; simp only [Shuffle.Table.gStep, zev_sub, zev_c, cur_cv, ha, hf]; rfl
    simp [this]
  obtain ⟨r', hr', i', hi', hb', hs', hmsg, hm'⟩ := recv_matched hH htg honlyG hpubG hts hr hi
    (by simp [Shuffle.Table.interactions]) (by simp [Shuffle.Table.interactions]) hm
  rw [hTg] at hi'
  -- the sender is the `busGen` interaction of `genV3`, active on an accepting row
  have hi1 : i' = (Rng.Table.interactions busChacha B.gen)[1]! := by
    simp only [Rng.Table.table, Rng.Table.interactions, List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl
    · simp at hb'; exact absurd hb' hcg
    · rfl
  subst hi1
  have hacc : cv tr tg r' Rng.Table.colAcc = 1 := (Shuffle.mult_col rfl).mp hm'
  obtain ⟨key, kstart, n, j, kend, hk, hkey, hn1, hn2, hks, hke, hgen, -, hmv⟩ :=
    genIndex_sound hH htc hTc htg hTg honlyC hpubC hr' hacc
  refine ⟨key, kstart, n, j, kend, hk, hkey, hn1, hn2, hks, hke, hgen, ?_⟩
  rw [← hmv, hmsg]; rfl

end ZkFormal.Chacha
