import ZkFormal.NearV3.Sched.View.ProcBlock

/-!
# ZkFormal.NearV3.Sched.View.ProcRound — one round of `sprV3`: a header and its entries

For a header row `h` (`kH = 1`):

* `ents`: as long as no earlier entry is last, row `h + 1 + j` is entry `x = j` with the round
  constants and limbs of `h` and the next header's instance values
  (`Tq = T + Lr`, `kq = kend`, `Kq = K`, `zq = z`) — the facts `EF h j`;
* **`round_shape`**: `1 ≤ Lr ≤ height`, the round is the entries `h + 1 … h + Lr` (`EF h j`
  for `j < Lr`), `le = [j + 1 = Lr]` on entry `j`, and the row `h + 1 + Lr` exists;
* **`round_after`**: the row `h + 1 + Lr` after the round is padding, a new key block
  (`kc = 0`, `τ + 1`), or the next header with `τ`, the limbs, `T = T + Lr`, `kq = kend`,
  `Kq = K`, `zq = z` of `h`.
-/

namespace ZkFormal.NearV3.Sched.Proc

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E

/-- Entry `j` of the round with header `h` (row `h + 1 + j`). -/
def EF (tr : Trace Fp) (tp h j : Nat) : Prop :=
  h + 1 + j < tr.height tp ∧ cv tr tp (h + 1 + j) kE = 1 ∧ cv tr tp (h + 1 + j) x = j ∧
    (∀ col, col ∈ roundCols → cv tr tp (h + 1 + j) col = cv tr tp h col) ∧
    (∀ i, i < 16 → cv tr tp (h + 1 + j) (colL i) = cv tr tp h (colL i)) ∧
    cv tr tp (h + 1 + j) Tq = (cv tr tp h T + cv tr tp h Lr) % 2013265921 ∧
    cv tr tp (h + 1 + j) kq = cv tr tp h kend ∧ cv tr tp (h + 1 + j) Kq = cv tr tp h K ∧
    cv tr tp (h + 1 + j) zq = cv tr tp h z

section
variable {tr : Trace Fp} {tp : Nat} {pub : List Fp}

theorem ents (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) {h : Nat}
    (hh0 : h < tr.height tp) (hh : cv tr tp h kH = 1) :
    ∀ j, (∀ i, i < j → cv tr tp (h + 1 + i) le = 0) → EF tr tp h j := by
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨hw1, hE, hx, hTq, hkq, hKq, hzq⟩ := hdr_next hL hh0 hh
    obtain ⟨-, -, RC⟩ := round_next hL hh0 (Or.inl hh)
    have hK1 : cv tr tp (h + 1) kK = 0 := by have := kinds hL hw1; omega
    have LC := limb_next hL hh0 (Or.inl hh) hw1 hK1
    simp only [EF, Nat.add_zero]
    exact ⟨hw1, hE, hx, RC, LC, hTq, hkq, hKq, hzq⟩
  | succ j ih =>
    intro hle
    obtain ⟨hw, hE, hx, RC, LC, hTq, hkq, hKq, hzq⟩ := ih (fun i hi => hle i (by omega))
    have hl : cv tr tp (h + 1 + j) le = 0 := hle j (by omega)
    obtain ⟨hw1, hx1⟩ := ent_next hL hw hE hl
    obtain ⟨-, hE1, RC1⟩ := round_next hL hw (Or.inr ⟨hE, hl⟩)
    have hK1 : cv tr tp (h + 1 + j + 1) kK = 0 := by have := kinds hL hw1; omega
    have LC1 := limb_next hL hw (Or.inr hE) hw1 hK1
    have IC1 := inst_next hL hw (Or.inl hE) hw1 hK1
    unfold EF
    rw [show h + 1 + (j + 1) = h + 1 + j + 1 by omega]
    refine ⟨hw1, hE1, by rw [hx1, hx]; omega, fun col hc => by rw [RC1 col hc, RC col hc],
      fun i hi => by rw [LC1 i hi, LC i hi], ?_, ?_, ?_, ?_⟩
    · rw [IC1 Tq (by simp [instCols]), hTq]
    · rw [IC1 kq (by simp [instCols]), hkq]
    · rw [IC1 Kq (by simp [instCols]), hKq]
    · rw [IC1 zq (by simp [instCols]), hzq]

theorem round_end (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) {h : Nat}
    (hh0 : h < tr.height tp) (hh : cv tr tp h kH = 1) :
    ∃ L, (∀ i, i < L → cv tr tp (h + 1 + i) le = 0) ∧ cv tr tp (h + 1 + L) le = 1 := by
  apply Classical.byContradiction
  intro hne
  have all : ∀ j, ∀ i, i < j → cv tr tp (h + 1 + i) le = 0 := by
    intro j
    induction j with
    | zero => intro i hi; omega
    | succ j ih =>
      intro i hi
      rcases Nat.lt_or_ge i j with h1 | h1
      · exact ih i h1
      · have hij : i = j := by omega
        rw [hij]
        have hw := (ents hL hH hh0 hh j ih).1
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (kinds hL hw).2.2.2.2.2.2.2.1 with e | e
        · exact e
        · exact absurd ⟨j, ih, e⟩ hne
  have := (ents hL hH hh0 hh (tr.height tp) (all _)).1
  omega

/-- **Round shape.** -/
theorem round_shape (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) {h : Nat}
    (hh0 : h < tr.height tp) (hh : cv tr tp h kH = 1) :
    1 ≤ cv tr tp h Lr ∧ h + 1 + cv tr tp h Lr < tr.height tp ∧
      ∀ j, j < cv tr tp h Lr → EF tr tp h j ∧
        cv tr tp (h + 1 + j) le = (if j + 1 = cv tr tp h Lr then 1 else 0) := by
  obtain ⟨L, hpre, hlast⟩ := round_end hL hH hh0 hh
  obtain ⟨hw, hE, hx, RC, -⟩ := ents hL hH hh0 hh L hpre
  obtain ⟨-, hLr⟩ := le_entry hL hw hlast
  rw [hx, RC Lr (by simp [roundCols])] at hLr
  have hL1 : cv tr tp h Lr = L + 1 := by omega
  have hw1 := act_next hL hw (act_of hL hw (Or.inr (Or.inr hE)))
  refine ⟨by omega, by rw [hL1]; omega, fun j hj => ⟨?_, ?_⟩⟩
  · rcases Nat.lt_or_ge j L with h1 | h1
    · exact ents hL hH hh0 hh j (fun i hi => hpre i (by omega))
    · have hjL : j = L := by omega
      rw [hjL]; exact ents hL hH hh0 hh L hpre
  · rcases Nat.lt_or_ge j L with h1 | h1
    · rw [hpre j h1, if_neg (by omega)]
    · have hjL : j = L := by omega
      rw [hjL, hlast, if_pos (by omega)]

/-- **After the round.** -/
theorem round_after (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) {h : Nat}
    (hh0 : h < tr.height tp) (hh : cv tr tp h kH = 1) :
    h + 1 + cv tr tp h Lr < tr.height tp ∧
      (cv tr tp (h + 1 + cv tr tp h Lr) act = 0 ∨
        (cv tr tp (h + 1 + cv tr tp h Lr) kK = 1 ∧ cv tr tp (h + 1 + cv tr tp h Lr) kc = 0 ∧
          cv tr tp (h + 1 + cv tr tp h Lr) tau = (cv tr tp h tau + 1) % 2013265921) ∨
        (cv tr tp (h + 1 + cv tr tp h Lr) kH = 1 ∧
          cv tr tp (h + 1 + cv tr tp h Lr) tau = cv tr tp h tau ∧
          cv tr tp (h + 1 + cv tr tp h Lr) T = (cv tr tp h T + cv tr tp h Lr) % 2013265921 ∧
          cv tr tp (h + 1 + cv tr tp h Lr) kq = cv tr tp h kend ∧
          cv tr tp (h + 1 + cv tr tp h Lr) Kq = cv tr tp h K ∧
          cv tr tp (h + 1 + cv tr tp h Lr) zq = cv tr tp h z ∧
          ∀ i, i < 16 → cv tr tp (h + 1 + cv tr tp h Lr) (colL i) = cv tr tp h (colL i))) := by
  obtain ⟨h1, hn, RS⟩ := round_shape hL hH hh0 hh
  obtain ⟨⟨hw, hE, -, RC, LC, hTq, hkq, hKq, hzq⟩, hle⟩ := RS (cv tr tp h Lr - 1) (by omega)
  rw [if_pos (by omega)] at hle
  have e : h + 1 + cv tr tp h Lr = h + 1 + (cv tr tp h Lr - 1) + 1 := by omega
  rw [e] at hn ⊢
  generalize h + 1 + (cv tr tp h Lr - 1) = w at hw hE RC LC hTq hkq hKq hzq hle hn ⊢
  refine ⟨hn, ?_⟩
  have K := kinds hL hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K.1 with ha | ha
  · exact Or.inl ha
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K.2.1 with kk | kk
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 K.2.2.1 with kh | kh
      · have he : cv tr tp (w + 1) kE = 1 := by omega
        have := prev_ent hL hn he
        have := kinds hL hw
        omega
      · have IC := inst_next hL hw (Or.inl hE) hn kk
        have LC1 := limb_next hL hw (Or.inr hE) hn kk
        have hT := (hdr_valid hL hn kh).1
        refine Or.inr (Or.inr ⟨kh, ?_, ?_, ?_, ?_, ?_, fun i hi => by rw [LC1 i hi, LC i hi]⟩)
        · rw [IC tau (by simp [instCols]), RC tau (by simp [roundCols])]
        · rw [hT, IC Tq (by simp [instCols]), hTq]
        · rw [IC kq (by simp [instCols]), hkq]
        · rw [IC Kq (by simp [instCols]), hKq]
        · rw [IC zq (by simp [instCols]), hzq]
    · have := blk_next hL hw (Or.inr hle) hn kk
      rw [RC tau (by simp [roundCols])] at this
      exact Or.inr (Or.inl ⟨kk, this.1, this.2⟩)

end

end ZkFormal.NearV3.Sched.Proc
