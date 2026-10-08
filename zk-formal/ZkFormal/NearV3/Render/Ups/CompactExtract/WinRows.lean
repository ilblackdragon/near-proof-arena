import ZkFormal.NearV3.Render.Ups.CompactExtract.ByteRows
import ZkFormal.NearV3.Extract.Ups.WinRows
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

/-- **Derived part constants** on a part's first row. -/
theorem partSel {ci ti di si ki sdi : Nat} (hI : IxOf C ci ti di si ki sdi)
    (h1 : ci < 11) (h2 : si < 3) (h3 : ki < 12) (h4 : sdi < 3) (hpf : C pf = 1) :
    C vcp = vcpV ci ki ∧ C xcp = xcpV ci ki ∧ C ba0 = ba0V si ki ∧ C ba1 = ba1V si ki ∧
    C spY1 = spY1V ci si ki ∧ C spY2 = spY2V ci si ki := by
  obtain ⟨-, -, a3, a4, a5, a6, a7, a8⟩ := ixVals (D := D) hI h1 h2 h3 h4
  have lt : ∀ v, v ≤ 128 → v < P := fun v hv => by rw [P_lit]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← a6]; exact gsub_val hpf (hC _) (by rw [a6]; exact lt _ (by have := b2n_le (b := true); unfold vcpV; have := b2n_le (kdOf ki == .RDB || kdOf ki == .RBI || kdOf ki == .MVL || (kdOf ki == .SPB && csOf ci == .LSa)); omega))
      (factN ok hC hD (memPlan (by simp [cPlan, eVcp])))
  · rw [← a5]; exact gsub_val hpf (hC _) (by rw [a5]; exact lt _ (by unfold xcpV; have := b2n_le (kdOf ki == .SPB && (csOf ci == .ESl1 || csOf ci == .ESn1)); omega))
      (factN ok hC hD (memPlan (by simp [cPlan, eXcp])))
  · rw [← a7]; exact gsub_val hpf (hC _) (by rw [a7]; exact lt _ (by unfold ba0V; have := b2n_le (kdOf ki == .RBI && si == 0); omega))
      (factN ok hC hD (memPlan (by simp [cPlan, eBa0])))
  · rw [← a8]; exact gsub_val hpf (hC _) (by rw [a8]; exact lt _ (by unfold ba1V; have := b2n_le (kdOf ki == .RBI && si != 0); omega))
      (factN ok hC hD (memPlan (by simp [cPlan, eBa1])))
  · rw [← a3]; exact gsub_val hpf (hC _) (by rw [a3]; exact lt _ (by unfold spY1V; have := b2n_le (kdOf ki == .SPB && (csOf ci == .LSa || (si == 0 && twoV ci == 1))); omega))
      (factN ok hC hD (memPlan (by simp [cPlan, eSpY1])))
  · rw [← a4]; exact gsub_val hpf (hC _) (by rw [a4]; exact lt _ (by unfold spY2V; have := b2n_le (kdOf ki == .SPB && si != 0 && twoV ci == 1); omega))
      (factN ok hC hD (memPlan (by simp [cPlan, eSpY2])))

/-- The window sequence: entering a window sets `fw`; inside a window the window constants stay;
at a window end, the next window has `fw = 0` and `lastw` says whether `MEM` follows. -/
theorem winStep :
    (C sCH = 0 → D sCH = 1 → D fw = 1) ∧
    (C sCH = 1 → C fe = 0 → D fw = C fw ∧ D lastw = C lastw ∧ D wfr = C wfr ∧ D tgt = C tgt ∧ D wy = C wy ∧
      D wn = C wn) ∧
    (C sCH = 1 → C fe = 1 → D sCH = 1 → D fw = 0) ∧
    (C sCH = 1 → C fe = 1 → C lastw = D sMEM) := by
  have f1 := factN ok hC hD (e := mul3 (not (c sCH)) (n sCH) (not (n fw))) (memFields (by simp [cFields]))
  have f2 := factN ok hC hD (e := mul3 (c sCH) (not (c fe)) (sub (n fw) (c fw))) (memFields (by simp [cFields]))
  have f3 := factN ok hC hD (e := mul3 (c sCH) (c fe) (.mul (n sCH) (n fw))) (memFields (by simp [cFields]))
  have f4 := factN ok hC hD (e := mul3 (c fe) (c sCH) (sub (c lastw) (n sMEM))) (memFields (by simp [cFields]))
  have g : ∀ x ∈ [lastw, wfr, tgt, wy, wn], nev C D (Dsl.mul3 (c sCH) (not (c fe)) (sub (n x) (c x))) = 0 :=
    fun x hx => factN ok hC hD (memFields (by
      unfold cFields; simp only [List.mem_append, List.mem_map]
      exact Or.inl (Or.inr ⟨x, hx, rfl⟩)))
  have g1 := g lastw (by simp); have g2 := g wfr (by simp); have g3 := g tgt (by simp)
  have g4 := g wy (by simp); have g5 := g wn (by simp)
  have a := fun x => hC x
  have b := fun x => hD x
  simp only [P_lit] at a b
  have := a fw; have := a lastw; have := a wfr; have := a tgt; have := a wy; have := a wn
  have := b fw; have := b lastw; have := b wfr; have := b tgt; have := b wy; have := b wn; have := b sMEM
  have bD := rowBool ok hC (x := sCH) (by simp [rowBools, states])
  nev_simp at f1 f2 f3 f4 g1 g2 g3 g4 g5
  refine ⟨fun h h' => ?_, fun h h' => ?_, fun h h' h'' => ?_, fun h h' => ?_⟩
  · simp only [h, h'] at f1; simp at f1; omega
  · simp only [h, h'] at f2 g1 g2 g3 g4 g5; simp at f2 g1 g2 g3 g4 g5; omega
  · simp only [h, h', h''] at f3; simp at f3; omega
  · simp only [h, h'] at f4; simp at f4; omega

/-- **Window roles** on a window row, by kind. -/
theorem winRole {ci ti di si ki sdi : Nat} (hI : IxOf C ci ti di si ki sdi)
    (h1 : ci < 11) (h2 : si < 3) (h3 : ki < 12) (h4 : sdi < 3) (hch : C sCH = 1)
    (hY1 : C spY1 = spY1V ci si ki) (hY2 : C spY2 = spY2V ci si ki) (hX : C xcp = xcpV ci ki) :
    C tgt = (if s15V ki sdi si = 1 then C lastw else C fw) ∧
    (ki = 0 ∨ ki = 5 → C wfr = C tgt) ∧
    (ki = 1 ∨ ki = 9 ∨ ki = 11 → C wfr = 1) ∧
    (ki = 3 ∨ ki = 4 ∨ ki = 7 → C wfr = 0) ∧
    (ki = 10 → C wy = (if C fw = 1 then spY1V ci si ki else spY2V ci si ki) ∧
      C wfr + (1 - C wy) * xcpV ci ki = 1 ∧
      (C fw = 1 → C lastw + twoV ci = 1) ∧ (C fw = 0 → C lastw = 1)) ∧
    C wn = (if ki = 5 then C tgt else 0) + (if ki = 10 then C wy else 0) ∧
    C rdc = C fs * C tgt * C UpsV3.up ∧ (C rdc = 1 → C rcid = C cN) := by
  obtain ⟨a1, a2, -, -, -, -, -, -⟩ := ixVals (D := D) hI h1 h2 h3 h4
  have k0 : C kRDB = if 0 = ki then 1 else 0 := hI.kd 0 (by omega)
  have k1 : C kRDE = if 1 = ki then 1 else 0 := hI.kd 1 (by omega)
  have k3 : C kRBR = if 3 = ki then 1 else 0 := hI.kd 3 (by omega)
  have k4 : C kRBV = if 4 = ki then 1 else 0 := hI.kd 4 (by omega)
  have k5 : C kRBI = if 5 = ki then 1 else 0 := hI.kd 5 (by omega)
  have k7 : C kMVE = if 7 = ki then 1 else 0 := hI.kd 7 (by omega)
  have k9 : C kWEX = if 9 = ki then 1 else 0 := hI.kd 9 (by omega)
  have k10 : C kSPB = if 10 = ki then 1 else 0 := hI.kd 10 (by omega)
  have k11 : C kPT = if 11 = ki then 1 else 0 := hI.kd 11 (by omega)
  have bb := fun {x} (hx : x ∈ rowBools) => le1 (rowBool ok hC hx)
  have bfw := bb (x := fw) (by decide); have blw := bb (x := lastw) (by decide)
  have bwfr := bb (x := wfr) (by decide); have btgt := bb (x := tgt) (by decide)
  have bwy := bb (x := wy) (by decide); have bwn := bb (x := wn) (by decide)
  have bfs := bb (x := fs) (by decide); have brdc := bb (x := rdc) (by decide)
  have hs15 := s15V ki sdi si
  have l1 : s15V ki sdi si ≤ 1 := by unfold s15V; exact b2n_le _
  have l2 : twoV ci ≤ 1 := by unfold twoV; exact b2n_le _
  have l3 : spY1V ci si ki ≤ 1 := by unfold spY1V; exact b2n_le _
  have l4 : spY2V ci si ki ≤ 1 := by unfold spY2V; exact b2n_le _
  have l5 : xcpV ci ki ≤ 1 := by unfold xcpV; exact b2n_le _
  have e1 : nev C D s15E = s15V ki sdi si := a1
  have e2 : nev C D twoE = twoV ci := a2
  have f1 := factN ok hC hD (e := .mul (c sCH) (sub (c tgt) (.add (.mul (c fw) (not s15E)) (.mul (c lastw) s15E))))
    (memFields (by simp [cFields]))
  have f2 := factN ok hC hD (e := mul3 (.add (c kRDB) (c kRBI)) (c sCH) (sub (c wfr) (c tgt))) (memFields (by simp [cFields]))
  have f3 := factN ok hC hD (e := mul3 (sumc [kRDE, kWEX, kPT]) (c sCH) (not (c wfr))) (memFields (by simp [cFields]))
  have f4 := factN ok hC hD (e := mul3 (sumc [kRBR, kRBV, kMVE]) (c sCH) (c wfr)) (memFields (by simp [cFields]))
  have f5 := factN ok hC hD (e := mul3 (c kSPB) (c sCH) (sub (c wy) (.add (.mul (c fw) (c spY1)) (.mul (not (c fw)) (c spY2)))))
    (memFields (by simp [cFields]))
  have f6 := factN ok hC hD (e := mul3 (c kSPB) (c sCH) (sub (c wfr) (sub (k 1) (.mul (not (c wy)) (c xcp)))))
    (memFields (by simp [cFields]))
  have f7 := factN ok hC hD (e := .mul (c sCH) (sub (c wn) (.add (.mul (c kRBI) (c tgt)) (.mul (c kSPB) (c wy)))))
    (memFields (by simp [cFields]))
  have f8 := factN ok hC hD (e := sub (c rdc) (.mul (mul3 (c sCH) (c fs) (c tgt)) (c UpsV3.up))) (memFields (by simp [cFields]))
  have f9 := factN ok hC hD (e := .mul (c rdc) (sub (c rcid) (c cN))) (memFields (by simp [cFields]))
  have f10 := factN ok hC hD (e := .mul (mul3 (c kSPB) (c sCH) (c fw)) (sub (c lastw) (not twoE))) (memFields (by simp [cFields]))
  have f11 := factN ok hC hD (e := mul3 (c kSPB) (c sCH) (.mul (not (c fw)) (not (c lastw)))) (memFields (by simp [cFields]))
  have a := fun x => hC x
  simp only [P_lit] at a
  have := a rcid; have := a cN
  have hu : C UpsV3.up < 2013265921 := a _
  simp only [sumc, List.map_cons, List.map_nil] at f3 f4
  nev_simp at f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
  simp only [hch, e1, e2, k0, k1, k3, k4, k5, k7, k9, k10, k11, hY1, hY2, hX] at f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
  refine ⟨?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, ?_, ?_, fun h => ?_⟩
  · rcases (show s15V ki sdi si = 0 ∨ s15V ki sdi si = 1 by omega) with h0 | h0 <;> rw [h0] at f1 <;> simp at f1 <;>
      simp [h0] <;> omega
  · rcases h with rfl | rfl <;> simp at f2 <;> omega
  · rcases h with rfl | rfl | rfl <;> simp at f3 <;> omega
  · rcases h with rfl | rfl | rfl <;> simp at f4 <;> omega
  · subst h
    simp at f5 f6 f10 f11
    refine ⟨?_, ?_, fun h => ?_, fun h => ?_⟩
    · rcases (show C fw = 0 ∨ C fw = 1 by omega) with h0 | h0 <;> rw [h0] at f5 <;> simp [h0] at f5 ⊢ <;> omega
    · rcases (show C wy = 0 ∨ C wy = 1 by omega) with h0 | h0 <;>
      rcases (show xcpV ci 10 = 0 ∨ xcpV ci 10 = 1 by omega) with h1 | h1 <;>
        rw [h0, h1] at f6 <;> simp at f6 <;> simp [h0, h1] <;> omega
    · rw [h] at f10; rcases (show twoV ci = 0 ∨ twoV ci = 1 by omega) with h0 | h0 <;> rw [h0] at f10 <;>
        simp at f10 <;> omega
    · rw [h] at f11; simp at f11; omega
  · by_cases h5 : ki = 5
    · subst h5; simp at f7 ⊢; omega
    · by_cases h10 : ki = 10
      · subst h10; simp at f7 ⊢; omega
      · simp [h5, h10, show ¬ 5 = ki by omega, show ¬ 10 = ki by omega] at f7 ⊢; omega
  · rcases (show C fs = 0 ∨ C fs = 1 by omega) with h0 | h0 <;>
    rcases (show C tgt = 0 ∨ C tgt = 1 by omega) with h1 | h1 <;> rw [h0, h1] at f8 <;> simp at f8 <;> simp [h0, h1] <;>
      omega
  · rw [h] at f9; simp at f9; omega

/-- Off windows nothing reads a child id. -/
theorem rdcOff (hch : C sCH = 0) : C rdc = 0 := by
  have f := factN ok hC hD (e := sub (c rdc) (.mul (mul3 (c sCH) (c fs) (c tgt)) (c UpsV3.up))) (memFields (by simp [cFields]))
  have := hC rdc
  rw [P_lit] at this
  nev_simp at f; simp [hch] at f; omega

/-- **The insertion offset** of `RBV` / `RBI` parts, by field. -/
theorem aftRow {ci ti di si ki sdi : Nat} (hI : IxOf C ci ti di si ki sdi) (hq : C qb = 1)
    (hoh : C sTAG + C sHPL + C sHPF + C sKEY + C sVLEN + C sVH + C sBM + C sCH + C sMEM = 1) :
    (ki = 4 → (C sBM + C sCH + C sMEM = 1 → C aft = 1) ∧ (C sTAG + C sVLEN + C sVH = 1 → C aft = 0)) ∧
    (ki = 5 → (C sTAG + C sVLEN + C sVH + C sBM = 1 → C aft = 0) ∧
      (C sCH = 1 → C aft = (1 - C fw) * (if si = 0 then 1 else 0)) ∧ (C sMEM = 1 → C aft = 1)) := by
  have k4 : C kRBV = if 4 = ki then 1 else 0 := hI.kd 4 (by omega)
  have k5 : C kRBI = if 5 = ki then 1 else 0 := hI.kd 5 (by omega)
  have t1 : C ts1 = if 0 = si then 1 else 0 := hI.ts 0 (by omega)
  have f1 := factN ok hC hD (e := mul3 (c kRBV) (sumc [sBM, sCH, sMEM]) (not (c aft))) (memBytes (by simp [cBytes]))
  have f2 := factN ok hC hD (e := mul3 (c kRBV) (sumc [sTAG, sVLEN, sVH]) (c aft)) (memBytes (by simp [cBytes]))
  have f3 := factN ok hC hD (e := mul3 (c kRBI) (sumc [sTAG, sVLEN, sVH, sBM]) (c aft)) (memBytes (by simp [cBytes]))
  have f4 := factN ok hC hD (e := mul3 (c kRBI) (c sCH) (sub (c aft) (.mul (not (c fw)) (c ts1)))) (memBytes (by simp [cBytes]))
  have f5 := factN ok hC hD (e := mul3 (c kRBI) (c sMEM) (not (c aft))) (memBytes (by simp [cBytes]))
  have bb := fun {x} (hx : x ∈ rowBools) => le1 (rowBool ok hC hx)
  have := bb (x := aft) (by decide); have := bb (x := fw) (by decide)
  have := bb (x := sTAG) (by decide); have := bb (x := sVLEN) (by decide); have := bb (x := sVH) (by decide)
  have := bb (x := sBM) (by decide); have := bb (x := sCH) (by decide); have := bb (x := sMEM) (by decide)
  simp only [sumc, List.map_cons, List.map_nil] at f1 f2 f3
  nev_simp at f1 f2 f3 f4 f5
  simp only [k4, k5, t1] at f1 f2 f3 f4 f5
  refine ⟨fun h => ⟨fun h' => ?_, fun h' => ?_⟩, fun h => ⟨fun h' => ?_, fun h' => ?_, fun h' => ?_⟩⟩
  · subst h; simp at f1
    rw [show C sBM + (C sCH + C sMEM) = 1 by omega, Nat.one_mul] at f1; omega
  · subst h; simp at f2
    rw [show C sTAG + (C sVLEN + C sVH) = 1 by omega, Nat.one_mul] at f2; omega
  · subst h; simp at f3
    rw [show C sTAG + (C sVLEN + (C sVH + C sBM)) = 1 by omega, Nat.one_mul] at f3; omega
  · subst h; simp [h'] at f4
    rcases (show C fw = 0 ∨ C fw = 1 by omega) with h0 | h0 <;> by_cases hs : si = 0 <;>
      simp [h0, hs, show (0 = si) ↔ si = 0 from eq_comm] at f4 ⊢ <;> omega
  · subst h; simp [h'] at f5; omega

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
