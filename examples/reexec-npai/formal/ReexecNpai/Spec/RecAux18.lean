import ReexecNpai.Spec.RecAux17

/-!
# Record parse: branch records (positional facts, decoding)

A branch record at `o` (kind `k ∈ {4, 5, 6}`):
`[k] [u32 vl, value (k = 5)] [ex: u16] [tag] [u32 len, h: 32 (k ≠ 4)] [bm: u16] [slots: 32·popc bm] [mm: 8]`;
the preimage starts at the tag.
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

section
variable (pb : Bytes) (o : Nat)

/-- Position of the revealed-children bitmap `ex`. -/
def brP : Nat := if u8At pb o = 5 then o + 5 + leAt pb (o + 1) 4 else o + 1
/-- Length of the preimage header (tag, and the value fields for kinds 5/6). -/
def brHdr : Nat := if u8At pb o = 4 then 1 else 37
/-- Position of the present-children bitmap `bm`. -/
def brR : Nat := brP pb o + 2 + brHdr pb o
def brBm : Nat := leAt pb (brR pb o) 2
def brEx : Nat := leAt pb (brP pb o) 2
def brNp : Nat := popc 16 (brBm pb o)
def brSlots : List Bytes := chunks32 (brNp pb o) (sl pb (brR pb o + 2) (32 * brNp pb o))
def brEnd : Nat := brR pb o + 2 + 32 * brNp pb o + 8
def brMM : Nat := leAt pb (brR pb o + 2 + 32 * brNp pb o) 8

end

structure BrFacts (pb : Bytes) (o : Nat) : Prop where
  kind : u8At pb o = 4 ∨ u8At pb o = 5 ∨ u8At pb o = 6
  v5 : u8At pb o = 5 → o + 5 ≤ pb.length
  tag : u8At pb (brP pb o + 2) = if u8At pb o = 4 then 1 else 2
  sub : SubB 16 (brBm pb o) (brEx pb o)
  hend : brEnd pb o ≤ pb.length
  vlen : u8At pb o = 5 → sl pb (brP pb o + 3) 4 = sl pb (o + 1) 4
  vzero : u8At pb o = 5 → sl pb (brP pb o + 7) 32 = zeros 32
  zero : ZeroB 16 (brBm pb o) (brEx pb o) (brSlots pb o)

/-- The value slot of a decoded branch. -/
def brV (pb : Bytes) (o : Nat) : Option Slot :=
  if u8At pb o = 4 then none
  else if u8At pb o = 5 then some (.val (sl pb (o + 5) (leAt pb (o + 1) 4)))
  else some (.ref (leAt pb (brP pb o + 3) 4) (sl pb (brP pb o + 7) 32))

/-- The decoded branch, given the stack. -/
def brRes (pb : Bytes) (o : Nat) (stk : List PTrie) : Option (List PTrie × Nat) :=
  match popN (popc 16 (brEx pb o)) stk with
  | none => none
  | some (cs, stk') =>
    some (.branch (brV pb o) (kidsOf (fun q => ([] ++ cs).getD q (.hash []))
      (ksOf 16 (brBm pb o) (brEx pb o) (brSlots pb o)) ([] : List PTrie).length) (brMM pb o) :: stk', brEnd pb o)

theorem brPos_of_facts {pb : Bytes} {o : Nat} (hf : BrFacts pb o) (stk : List PTrie) :
    brPos pb (u8At pb o) (o + 1) stk = brRes pb o stk := by
  obtain ⟨hk, v5, tag, sub, hend, vlen, vzero, zero⟩ := hf
  have hRP : brR pb o = brP pb o + 2 + brHdr pb o := rfl
  have hPo : o + 1 ≤ brP pb o := by unfold brP; split <;> omega
  have hEnd : brEnd pb o = brR pb o + 2 + 32 * brNp pb o + 8 := rfl
  have hv : valPos pb (decide (u8At pb o = 5)) (o + 1) =
      some ((if u8At pb o = 5 then some (sl pb (o + 5) (leAt pb (o + 1) 4)) else none), brP pb o) := by
    by_cases h5 : u8At pb o = 5
    · have hp : brP pb o = o + 5 + leAt pb (o + 1) 4 := by simp [brP, h5]
      have : brP pb o + 2 ≤ pb.length := by unfold brHdr at hRP; split at hRP <;> omega
      simp only [h5, decide_true, valPos, ↓reduceIte, borshAt]
      rw [if_pos (by omega), if_pos (by simp only [leAt] at hp; omega)]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      exact ⟨rfl, by rw [hp]; rfl⟩
    · simp [h5, valPos, brP]
  have hh : brHeadPos pb (u8At pb o) (brP pb o + 2 + 1) =
      some ((if u8At pb o = 4 then (0, []) else (leAt pb (brP pb o + 3) 4, sl pb (brP pb o + 7) 32)),
        brR pb o) := by
    unfold brHeadPos
    by_cases h4 : u8At pb o = 4
    · simp only [h4, ↓reduceIte, hRP, brHdr]
    · simp only [h4, ↓reduceIte]
      have : brR pb o = brP pb o + 39 := by simp [hRP, brHdr, h4]
      rw [if_pos (by omega), if_pos (by omega)]
      simp only [Option.some.injEq, Prod.mk.injEq, this]
  have hs : (if u8At pb o = 4 then some none else
      Option.map some (mkSlot (if u8At pb o = 5 then some (sl pb (o + 5) (leAt pb (o + 1) 4)) else none)
        (if u8At pb o = 4 then (0, []) else (leAt pb (brP pb o + 3) 4, sl pb (brP pb o + 7) 32)).1
        (if u8At pb o = 4 then (0, []) else (leAt pb (brP pb o + 3) 4, sl pb (brP pb o + 7) 32)).2)) =
      some (brV pb o) := by
    by_cases h4 : u8At pb o = 4
    · simp [h4, brV]
    · by_cases h5 : u8At pb o = 5
      · have hp : brP pb o = o + 5 + leAt pb (o + 1) 4 := by simp [brP, h5]
        have hl : (sl pb (o + 5) (leAt pb (o + 1) 4)).length = leAt pb (o + 1) 4 :=
          sl_length_of (by unfold brHdr at hRP; split at hRP <;> omega)
        have hc : leAt pb (brP pb o + 3) 4 = (sl pb (o + 5) (leAt pb (o + 1) 4)).length ∧
            sl pb (brP pb o + 7) 32 = zeros 32 := ⟨by rw [hl]; simp only [leAt]; rw [vlen h5], vzero h5⟩
        simp [h4, h5, mkSlot, hc, brV]
      · simp [h4, h5, mkSlot, brV]
  unfold brPos brRes
  rw [hv]
  simp only
  rw [if_pos (by unfold brHdr at hRP; split at hRP <;> omega), if_pos (by unfold brHdr at hRP; split at hRP <;> omega),
    if_neg (by rw [tag]; simp), hh]
  simp only
  rw [show (popc 16 (leAt pb (brR pb o) 2)) = brNp pb o from rfl]
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  simp only [hs]
  rw [show leAt pb (brP pb o) 2 = brEx pb o from rfl, show leAt pb (brR pb o) 2 = brBm pb o from rfl]
  cases hp : popN (popc 16 (brEx pb o)) stk with
  | none => rfl
  | some x =>
    obtain ⟨cs, stk'⟩ := x
    obtain ⟨hcl, -⟩ := popN_some _ _ _ _ hp
    simp only
    rw [show chunks32 (brNp pb o) (sl pb (brR pb o + 2) (32 * brNp pb o)) = brSlots pb o from rfl,
      mkKids_of 16 _ _ _ cs [] (by rw [brSlots, chunks32_length]; rfl) sub zero hcl]
    rfl

theorem facts_of_brPos {pb : Bytes} {o : Nat} {stk stk' : List PTrie} {o' : Nat}
    (hk : u8At pb o = 4 ∨ u8At pb o = 5 ∨ u8At pb o = 6)
    (h : brPos pb (u8At pb o) (o + 1) stk = some (stk', o')) :
    BrFacts pb o ∧ o' = brEnd pb o ∧ ∃ cs stk'', popN (popc 16 (brEx pb o)) stk = some (cs, stk'') := by
  unfold brPos at h
  split at h
  · simp at h
  rename_i vo p hvp
  have hpv : p = brP pb o ∧ (u8At pb o = 5 → o + 5 ≤ pb.length ∧
      vo = some (sl pb (o + 5) (leAt pb (o + 1) 4)) ∧ o + 5 + leAt pb (o + 1) 4 ≤ pb.length) ∧
      (u8At pb o ≠ 5 → vo = none) := by
    by_cases h5 : u8At pb o = 5
    · simp only [h5, decide_true, valPos, ↓reduceIte, borshAt] at hvp
      split at hvp
      · split at hvp
        · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hvp
          obtain ⟨rfl, rfl⟩ := hvp
          refine ⟨by simp [brP, h5]; rfl, fun _ => ⟨by omega, rfl, by simp only [leAt]; omega⟩,
            fun h' => absurd h5 h'⟩
        · simp at hvp
      · simp at hvp
    · simp only [h5, decide_false, valPos, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
        Prod.mk.injEq] at hvp
      obtain ⟨rfl, rfl⟩ := hvp
      exact ⟨by simp [brP, h5], fun h' => absurd h' h5, fun _ => rfl⟩
  obtain ⟨rfl, hv5, hvn⟩ := hpv
  split at h
  case isFalse => simp at h
  rename_i c1
  split at h
  case isFalse => simp at h
  rename_i c2
  have htag : u8At pb (brP pb o + 2) = (if u8At pb o = 4 then 1 else 2) :=
    Decidable.byContradiction fun hc => by rw [if_pos hc] at h; simp at h
  rw [if_neg (fun h' => h' htag)] at h
  split at h
  · simp at h
  rename_i len hh r hhp
  have hr : r = brR pb o ∧ (u8At pb o ≠ 4 → len = leAt pb (brP pb o + 3) 4 ∧ hh = sl pb (brP pb o + 7) 32 ∧
      brP pb o + 2 + 1 + 4 + 32 ≤ pb.length) := by
    unfold brHeadPos at hhp
    by_cases h4 : u8At pb o = 4
    · simp only [h4, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hhp
      obtain ⟨-, rfl⟩ := hhp
      exact ⟨by simp [brR, brHdr, h4], fun h' => absurd h4 h'⟩
    · simp only [h4, ↓reduceIte] at hhp
      split at hhp
      · split at hhp
        · simp only [Option.some.injEq, Prod.mk.injEq] at hhp
          obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hhp
          refine ⟨by simp [brR, brHdr, h4], fun _ => ⟨rfl, rfl, by omega⟩⟩
        · simp at hhp
      · simp at hhp
  obtain ⟨rfl, hr4⟩ := hr
  rw [show popc 16 (leAt pb (brR pb o) 2) = brNp pb o from rfl,
    show leAt pb (brR pb o) 2 = brBm pb o from rfl, show leAt pb (brP pb o) 2 = brEx pb o from rfl] at h
  split at h
  case isFalse => simp at h
  rename_i c4
  split at h
  case isFalse => simp at h
  rename_i c5
  split at h
  case isFalse => simp at h
  rename_i c6
  split at h
  · simp at h
  rename_i v hvs
  split at h
  · simp at h
  rename_i cs stk'' hpop
  cases hkid : mkKids 16 (brBm pb o) (brEx pb o) (chunks32 (brNp pb o) (sl pb (brR pb o + 2) (32 * brNp pb o))) cs with
  | none => rw [hkid] at h; simp at h
  | some kids =>
  rw [hkid] at h
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  obtain ⟨sub, zero, -, -, -⟩ := mkKids_some _ _ _ _ _ [] _ hkid
  have hvl : u8At pb o = 5 → sl pb (brP pb o + 3) 4 = sl pb (o + 1) 4 ∧ sl pb (brP pb o + 7) 32 = zeros 32 := by
    intro h5
    obtain ⟨-, hvo, hb⟩ := hv5 h5
    obtain ⟨hl, hhv, hb2⟩ := hr4 (by omega)
    subst hvo
    simp only [show ¬ (u8At pb o = 4) by omega, ↓reduceIte, mkSlot] at hvs
    split at hvs
    · rename_i hc
      obtain ⟨hc1, hc2⟩ := hc
      refine ⟨sl4_of_leAt (by omega) (by omega) ?_, by rw [← hhv]; exact hc2⟩
      rw [← hl, hc1, sl_length_of (by omega)]
    · simp at hvs
  refine ⟨⟨hk, fun h5 => (hv5 h5).1, htag, sub, by simp only [brEnd]; omega,
    fun h5 => (hvl h5).1, fun h5 => (hvl h5).2, zero⟩, by simp only [brEnd, brNp, brBm], cs, stk'', hpop⟩

/-- The fields of the branch entry decoded at `o`. -/
def brNF (pb : Bytes) (o : Nat) : NF :=
  .branch (if u8At pb o = 4 then none else if u8At pb o = 5 then some none
      else some (some (leAt pb (brP pb o + 3) 4, sl pb (brP pb o + 7) 32)))
    (ksOf 16 (brBm pb o) (brEx pb o) (brSlots pb o)) (brMM pb o)

def brEnt (pb : Bytes) (o : Nat) (ps kid res lo : Nat) : Ent :=
  ⟨PF + brP pb o + 2, brHdr pb o + 32 * brNp pb o + 10, ps, kid, res,
    (if u8At pb o = 5 then PF + o + 5 else 0), brNF pb o, lo, PF + o⟩

theorem brSlots_length (pb : Bytes) (o : Nat) : (brSlots pb o).length = popc 16 (brBm pb o) := by
  simp [brSlots, chunks32_length, brNp]

theorem brLoc {pb : Bytes} {o : Nat} (hf : BrFacts pb o) (ps kid res lo : Nat) :
    LocalWF pb (brEnt pb o ps kid res lo) := by
  obtain ⟨hk, v5, tag, sub, hend, vlen, vzero, zero⟩ := hf
  have hRP : brR pb o = brP pb o + 2 + brHdr pb o := rfl
  have hPo : o + 1 ≤ brP pb o := by unfold brP; split <;> omega
  have hEnd : brEnd pb o = brR pb o + 2 + 32 * brNp pb o + 8 := rfl
  have hhdr : brHdr pb o = 1 ∨ brHdr pb o = 37 := by unfold brHdr; split <;> simp
  have hsl : (sl pb (brR pb o + 2) (32 * brNp pb o)).length = 32 * brNp pb o := sl_length_of (by omega)
  have hflat : (brSlots pb o).flatten = sl pb (brR pb o + 2) (32 * brNp pb o) := chunks32_flatten _ _ hsl
  have hsb := slotBytes_ksOf 16 (brBm pb o) (brEx pb o) (brSlots pb o) (brSlots_length pb o) sub zero
  rw [hflat] at hsb
  have hbp : bitsPres (ksOf 16 (brBm pb o) (brEx pb o) (brSlots pb o)) 0 = brBm pb o := by
    rw [bitsPres_ksOf]; have := leAt2_lt pb (brR pb o); simp only [brBm]; omega
  have hbr : bitsRev (ksOf 16 (brBm pb o) (brEx pb o) (brSlots pb o)) 0 = brEx pb o := by
    rw [bitsRev_ksOf _ _ _ _ _ sub]; have := leAt2_lt pb (brP pb o); simp only [brEx]; omega
  have hu16 : u16 (brBm pb o) = sl pb (brR pb o) 2 := u16_sl pb (brR pb o) (by omega)
  have hu16e : u16 (brEx pb o) = sl pb (brP pb o) 2 := u16_sl pb (brP pb o) (by omega)
  have hu64 := u64_sl pb (brR pb o + 2 + 32 * brNp pb o) (by omega)
  have hpre : pseg pb (PF + brP pb o + 2) (brHdr pb o + 32 * brNp pb o + 10) =
      sl pb (brP pb o + 2) (brHdr pb o + 32 * brNp pb o + 10) := by
    rw [show PF + brP pb o + 2 = PF + (brP pb o + 2) by omega, pseg_PF]
  have hnrev := nRev_ksOf 16 (brBm pb o) (brEx pb o) (brSlots pb o) sub
  have hks : NFOk (brNF pb o) := by
    simp only [brNF, NFOk]
    refine ⟨ksOf_length _ _ _ _, leAt8_lt _ _, ?_, ksOf_hashes _ _ _ _ (brSlots_length pb o)
      (chunks32_mem _ _ (Nat.le_of_eq hsl.symm))⟩
    by_cases h4 : u8At pb o = 4
    · rw [if_pos h4]; trivial
    · rw [if_neg h4]
      by_cases h5 : u8At pb o = 5
      · rw [if_pos h5]; trivial
      · rw [if_neg h5]
        have : brHdr pb o = 37 := by simp [brHdr, h4]
        exact ⟨leAt4_lt _ _, sl_length_of (by omega)⟩
  have hfl : pseg pb (PF + brP pb o + 2 - 2) 2 = u16 (brEx pb o) := by
    rw [show PF + brP pb o + 2 - 2 = PF + brP pb o by omega, pseg_PF, ← hu16e]
  rcases hk with h4 | h5 | h6
  · -- no value, header [1]
    have hh1 : brHdr pb o = 1 := by simp [brHdr, h4]
    have hsplit : sl pb (brP pb o + 2) (brHdr pb o + 32 * brNp pb o + 10) =
        sl pb (brP pb o + 2) 1 ++ (sl pb (brR pb o) 2 ++ (sl pb (brR pb o + 2) (32 * brNp pb o) ++
          sl pb (brR pb o + 2 + 32 * brNp pb o) 8)) := by
      rw [hh1, show 1 + 32 * brNp pb o + 10 = 1 + (2 + (32 * brNp pb o + 8)) by omega, sl_add, sl_add, sl_add,
        hRP, hh1]
    have ht := sl_one_of (show brP pb o + 2 < pb.length by omega) (by rw [tag, if_pos h4])
    refine ⟨hks, by simp [brEnt], by simp [brEnt]; omega, by simp only [brEnt]; omega,
      ⟨zeros 32, List.replicate (popc 16 (brEx pb o)) (zeros 32), by simp [zeros], ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [brEnt, brNF, nKids, hnrev]
    · intro x hx; rw [List.eq_of_mem_replicate hx]; simp [zeros]
    · simp only [brEnt, brNF, h4, ↓reduceIte, preImg, hpre, hsplit, ht, hbp, hu16, hsb, hu64, brMM,
        List.append_assoc]
      rfl
    · simp [brEnt, brNF, h4, hasVal]
    · simp only [brEnt, brNF]; rw [hfl, hbr]
  · -- revealed value
    have hh1 : brHdr pb o = 37 := by simp [brHdr, h5]
    have hp : brP pb o = o + 5 + leAt pb (o + 1) 4 := by simp [brP, h5]
    have hsplit : sl pb (brP pb o + 2) (brHdr pb o + 32 * brNp pb o + 10) =
        sl pb (brP pb o + 2) 1 ++ (sl pb (brP pb o + 3) 4 ++ (sl pb (brP pb o + 7) 32 ++ (sl pb (brR pb o) 2 ++
          (sl pb (brR pb o + 2) (32 * brNp pb o) ++ sl pb (brR pb o + 2 + 32 * brNp pb o) 8)))) := by
      rw [hh1, show 37 + 32 * brNp pb o + 10 = 1 + (4 + (32 + (2 + (32 * brNp pb o + 8)))) by omega,
        sl_add, sl_add, sl_add, sl_add, sl_add, hRP, hh1]
      try simp only [show brP pb o + 2 + 1 = brP pb o + 3 by omega, show brP pb o + 3 + 4 = brP pb o + 7 by omega,
        show brP pb o + 7 + 32 = brP pb o + 2 + 37 by omega]
    have ht := sl_one_of (show brP pb o + 2 < pb.length by omega) (by rw [tag, if_neg (by omega)])
    have hval : (brEnt pb o ps kid res lo).val = PF + (o + 1) + 4 := by simp [brEnt, h5]; omega
    have hvl : vlenAt pb (brEnt pb o ps kid res lo) = leAt pb (o + 1) 4 := vlenAt_val hval
    have hu32 : u32 (leAt pb (o + 1) 4) = sl pb (brP pb o + 3) 4 := by
      rw [vlen h5]; exact u32_sl pb (o + 1) (by omega)
    refine ⟨hks, by simp [brEnt], by simp [brEnt]; omega, by simp only [brEnt]; omega,
      ⟨sl pb (brP pb o + 7) 32, List.replicate (popc 16 (brEx pb o)) (zeros 32), sl_length_of (by omega),
        ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [brEnt, brNF, nKids, hnrev]
    · intro x hx; rw [List.eq_of_mem_replicate hx]; simp [zeros]
    · rw [hvl]
      simp only [brEnt, brNF, h5, ↓reduceIte, show ¬ (5 = 4) from by decide, preImg, hpre, hsplit, ht, hbp,
        hu16, hsb, hu64, brMM, hu32, List.append_assoc]
      rfl
    · have hhv : hasVal (brEnt pb o ps kid res lo).nf = true := by
        simp [brEnt, brNF, h5, hasVal]
      rw [if_pos hhv, hvl]
      simp only [brEnt, brNF, h5, ↓reduceIte, show ¬ (5 = 4) from by decide]
      refine ⟨?_, leAt4_lt _ _, ?_⟩
      · trivial
      · simp only [brP, h5, ↓reduceIte]; omega
    · simp only [brEnt, brNF]; rw [hfl, hbr]
  · -- value by reference
    have hh1 : brHdr pb o = 37 := by simp [brHdr, h6]
    have hsplit : sl pb (brP pb o + 2) (brHdr pb o + 32 * brNp pb o + 10) =
        sl pb (brP pb o + 2) 1 ++ (sl pb (brP pb o + 3) 4 ++ (sl pb (brP pb o + 7) 32 ++ (sl pb (brR pb o) 2 ++
          (sl pb (brR pb o + 2) (32 * brNp pb o) ++ sl pb (brR pb o + 2 + 32 * brNp pb o) 8)))) := by
      rw [hh1, show 37 + 32 * brNp pb o + 10 = 1 + (4 + (32 + (2 + (32 * brNp pb o + 8)))) by omega,
        sl_add, sl_add, sl_add, sl_add, sl_add, hRP, hh1]
      try simp only [show brP pb o + 2 + 1 = brP pb o + 3 by omega, show brP pb o + 3 + 4 = brP pb o + 7 by omega,
        show brP pb o + 7 + 32 = brP pb o + 2 + 37 by omega]
    have ht := sl_one_of (show brP pb o + 2 < pb.length by omega) (by rw [tag, if_neg (by omega)])
    have hu32 := u32_sl pb (brP pb o + 3) (by omega)
    refine ⟨hks, by simp [brEnt], by simp [brEnt]; omega, by simp only [brEnt]; omega,
      ⟨zeros 32, List.replicate (popc 16 (brEx pb o)) (zeros 32), by simp [zeros], ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [brEnt, brNF, nKids, hnrev]
    · intro x hx; rw [List.eq_of_mem_replicate hx]; simp [zeros]
    · simp only [brEnt, brNF, h6, ↓reduceIte, show ¬ (6 = 4) from by decide, show ¬ (6 = 5) from by decide,
        preImg, hpre, hsplit, ht, hbp, hu16, hsb, hu64, brMM, hu32, List.append_assoc]
      rfl
    · simp [brEnt, brNF, h6, hasVal]
    · simp only [brEnt, brNF]; rw [hfl, hbr]

end ReexecNpai
