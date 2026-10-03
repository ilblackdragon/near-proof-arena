import ReexecNpai.Spec.RcptAux5

/-!
# Receipts phase, part 6: distinct receipt ids
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore Interp NearSpec NearSpec.TransferV1

namespace RcptProof

def nInner : Stmt := seqs [CST 1 64, MUL 1 3 1, ADDI 1 1 (RT + 16), ld32 0 1, CST 1 32, MEMEQ 1 2 0 1, assertZ 1]
def nHead : List Stmt := [CST 1 64, MUL 1 8 1, ADDI 1 1 (RT + 16), ld32 2 1, ADDI 3 8 1]
def nBody : Stmt := seqs (nHead ++ [forUp 3 7 4 nInner])

/-- Pointer to the receipt id of entry `j`. -/
def qp (M0 : Nat → UInt8) (j : Nat) : Nat := Bytes.leToNat (readMem M0 (j * 64 + 3600) 4)

/-- The receipt ids in memory. -/
def RidOK (M0 : Nat → UInt8) (n : Nat) (ids : List NearSpec.Bytes) : Prop :=
  ∀ j, j < n → readMem M0 (qp M0 j) 32 = ids.getD j [] ∧ qp M0 j + 32 ≤ 13844304

section
variable {pub cb pb : NearSpec.Bytes}

theorem inner_wp {x : M} {M0 : Nat → UInt8} {n i j : Nat} {ids : List NearSpec.Bytes} (hm : x.mem = M0)
    (hk8 : x.regs 14 = 8) (h3 : x.regs 3 = j) (h2 : x.regs 2 = qp M0 i) (hj : j < n) (hi : i < n)
    (hn : n ≤ 256) (hr : RidOK M0 n ids) :
    wp P (Inp pub cb pb) nInner x (fun x' => ids.getD i [] ≠ ids.getD j [] ∧ x'.mem = M0 ∧
      Frame [0, 1, 12, 13] x x') := by
  obtain ⟨hri, hbi⟩ := hr i hi
  obtain ⟨hrj, hbj⟩ := hr j hj
  simp only [qp] at hri hbi hrj hbj h2
  simp only [nInner]
  rcpt_auto [hm, hk8, h3, h2, hri, hrj]
  exact ⟨by assumption, by rcpt_frame_tac⟩

theorem inner_twp {x : M} {M0 : Nat → UInt8} {n i j : Nat} {ids : List NearSpec.Bytes} (hm : x.mem = M0)
    (hk8 : x.regs 14 = 8) (h3 : x.regs 3 = j) (h2 : x.regs 2 = qp M0 i) (hj : j < n) (hi : i < n)
    (hn : n ≤ 256) (hr : RidOK M0 n ids) (hne : ids.getD i [] ≠ ids.getD j []) :
    twp P (Inp pub cb pb) nInner x (fun x' c => x'.mem = M0 ∧ Frame [0, 1, 12, 13] x x' ∧ c ≤ 30) := by
  obtain ⟨hri, hbi⟩ := hr i hi
  obtain ⟨hrj, hbj⟩ := hr j hj
  simp only [qp] at hri hbi hrj hbj h2
  simp only [nInner]
  rcpt_auto [hm, hk8, h3, h2, hri, hrj, hne]
  exact ⟨by omega, by omega, by rcpt_frame_tac⟩

theorem frame_ext {C D : List Nat} {y x x' : M} (hF : Frame D y x) (hF' : Frame C x x')
    (hCD : ∀ k ∈ C, k ∈ D) : Frame D y x' :=
  fun k hk => by rw [hF' k (fun h => hk (hCD k h)), hF k hk]

theorem innerLoop_wp {y : M} {M0 : Nat → UInt8} {n i : Nat} {ids : List NearSpec.Bytes} (hm : y.mem = M0)
    (hk8 : y.regs 14 = 8) (h2 : y.regs 2 = qp M0 i) (h3 : y.regs 3 = i + 1) (h7 : y.regs 7 = n) (hi : i < n)
    (hn : n ≤ 256) (hr : RidOK M0 n ids) :
    wp P (Inp pub cb pb) (forUp 3 7 4 nInner) y (fun y' =>
      (∀ b, i < b → b < n → ids.getD i [] ≠ ids.getD b []) ∧ y'.mem = M0 ∧
      Frame [0, 1, 3, 4, 12, 13] y y') := by
  refine AccountIdProof.wp_forUpFrom (i := 3) (n := 7) (t := 4) (by decide) (by decide) (by decide)
    (J := fun j x => x.mem = M0 ∧ Frame [0, 1, 3, 4, 12, 13] y x ∧
      ∀ b, i < b → b < j → ids.getD i [] ≠ ids.getD b []) (S := i + 1) (N := n) (by omega) (by omega)
    ?_ ⟨hm, Frame.refl _ _, fun b h1 h2 => absurd h2 (by omega)⟩ h3 h7 ?_ ?_
  · intro j x v w ⟨hxm, hF, hP⟩
    exact ⟨hxm, AccountIdProof.fsr (by simp) (AccountIdProof.fsr (by simp) hF), hP⟩
  · intro j x hS hj ⟨hxm, hF, hP⟩ hx3 hx7
    refine wp_mono (inner_wp hxm (by rw [hF 14 (by decide), hk8]) hx3 (by rw [hF 2 (by decide), h2]) hj hi hn hr) ?_
    rintro x' ⟨hne, hm', hF'⟩
    refine ⟨⟨hm', frame_ext hF hF' (by decide), fun b h1 h2 => ?_⟩, by rw [hF' 3 (by decide), hx3],
      by rw [hF' 7 (by decide), hx7]⟩
    by_cases hb : b = j
    · subst hb; exact hne
    · exact hP b h1 (by omega)
  · intro x ⟨hxm, hF, hP⟩ _
    exact ⟨hP, hxm, hF⟩


theorem innerLoop_twp {y : M} {M0 : Nat → UInt8} {n i : Nat} {ids : List NearSpec.Bytes} (hm : y.mem = M0)
    (hk8 : y.regs 14 = 8) (h2 : y.regs 2 = qp M0 i) (h3 : y.regs 3 = i + 1) (h7 : y.regs 7 = n) (hi : i < n)
    (hn : n ≤ 256) (hr : RidOK M0 n ids) (hnd : ∀ b, i < b → b < n → ids.getD i [] ≠ ids.getD b []) :
    twp P (Inp pub cb pb) (forUp 3 7 4 nInner) y (fun y' c => y'.mem = M0 ∧
      Frame [0, 1, 3, 4, 12, 13] y y' ∧ c ≤ 8706) := by
  refine AccountIdProof.twp_forUpFrom (i := 3) (n := 7) (t := 4) (by decide) (by decide) (by decide)
    (J := fun j x => x.mem = M0 ∧ Frame [0, 1, 3, 4, 12, 13] y x) (S := i + 1) (N := n) (B := 30) (by omega)
    (by omega) ?_ ⟨hm, Frame.refl _ _⟩ h3 h7 ?_ ?_
  · intro j x v w ⟨hxm, hF⟩
    exact ⟨hxm, AccountIdProof.fsr (by simp) (AccountIdProof.fsr (by simp) hF)⟩
  · intro j x hS hj ⟨hxm, hF⟩ hx3 hx7
    refine twp_mono (inner_twp hxm (by rw [hF 14 (by decide), hk8]) hx3 (by rw [hF 2 (by decide), h2]) hj hi hn hr
      (hnd j (by omega) hj)) ?_
    rintro x' c ⟨hm', hF', hc⟩
    exact ⟨⟨hm', frame_ext hF hF' (by decide)⟩, by rw [hF' 3 (by decide), hx3], by rw [hF' 7 (by decide), hx7], hc⟩
  · intro x c ⟨hxm, hF⟩ _ hc
    refine ⟨hxm, hF, ?_⟩
    have : (n - (i + 1)) * (30 + 4) ≤ 256 * 34 := Nat.mul_le_mul (by omega) (by omega)
    omega

theorem head_wp {x : M} {i : Nat} (hk8 : x.regs 14 = 8) (h8 : x.regs 8 = i) (hi : i < 256) :
    wp P (Inp pub cb pb) (seqs nHead) x (fun y => y.mem = x.mem ∧ y.regs 2 = qp x.mem i ∧ y.regs 3 = i + 1 ∧
      Frame [1, 2, 3, 12] x y) := by
  simp only [nHead, qp]
  rcpt_auto [hk8, h8]
  rename_i j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  obtain ⟨a1, a2, a3, a4⟩ := hj
  simp [a1, a2, a3, a4]

theorem head_twp {x : M} {i : Nat} (hk8 : x.regs 14 = 8) (h8 : x.regs 8 = i) (hi : i < 256) :
    twp P (Inp pub cb pb) (seqs nHead) x (fun y c => y.mem = x.mem ∧ y.regs 2 = qp x.mem i ∧
      y.regs 3 = i + 1 ∧ Frame [1, 2, 3, 12] x y ∧ c ≤ 20) := by
  simp only [nHead, qp]
  rcpt_auto [hk8, h8]
  rename_i j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  obtain ⟨a1, a2, a3, a4⟩ := hj
  simp [a1, a2, a3, a4]

theorem nodup_wp {z : M} {M0 : Nat → UInt8} {n : Nat} {ids : List NearSpec.Bytes} (hm : z.mem = M0)
    (hk8 : z.regs 14 = 8) (h8 : z.regs 8 = 0) (h7 : z.regs 7 = n) (hn : n ≤ 256) (hr : RidOK M0 n ids) :
    wp P (Inp pub cb pb) (forUp 8 7 5 nBody) z (fun z' =>
      (∀ a b, a < b → b < n → ids.getD a [] ≠ ids.getD b []) ∧ z'.mem = M0 ∧
      Frame [0, 1, 2, 3, 4, 5, 8, 11, 12, 13] z z') := by
  refine wp_forUp (i := 8) (n := 7) (t := 5) (by decide) (by decide) (by decide)
    (J := fun i x => x.mem = M0 ∧ Frame [0, 1, 2, 3, 4, 5, 8, 11, 12, 13] z x ∧
      ∀ a b, a < i → a < b → b < n → ids.getD a [] ≠ ids.getD b []) (N := n) (by omega) ?_
    ⟨hm, Frame.refl _ _, fun a b h => absurd h (by omega)⟩ h8 h7 ?_ ?_
  · intro j x v w ⟨hxm, hF, hP⟩
    exact ⟨hxm, AccountIdProof.fsr (by simp) (AccountIdProof.fsr (by simp) hF), hP⟩
  · intro i x hi ⟨hxm, hF, hP⟩ hx8 hx7
    simp only [nBody]
    refine wp_seqs_append _ _ _ _ (by simp [nHead]) (by simp) ?_
    refine wp_mono (head_wp (by rw [hF 14 (by decide), hk8]) hx8 (by omega)) ?_
    rintro y ⟨hym, hy2, hy3, hFy⟩
    simp only [seqs]
    rw [hxm] at hym hy2
    refine wp_mono (innerLoop_wp hym (by rw [hFy 14 (by decide), hF 14 (by decide), hk8]) hy2 hy3
      (by rw [hFy 7 (by decide), hx7]) hi hn hr) ?_
    rintro y' ⟨hP', hm', hFy'⟩
    refine ⟨⟨hm', frame_ext (frame_ext hF hFy (by decide)) hFy' (by decide), fun a b ha hab hb => ?_⟩,
      by rw [hFy' 8 (by decide), hFy 8 (by decide), hx8], by rw [hFy' 7 (by decide), hFy 7 (by decide), hx7]⟩
    by_cases h : a = i
    · subst h; exact hP' b hab hb
    · exact hP a b (by omega) hab hb
  · intro x ⟨hxm, hF, hP⟩ _
    exact ⟨fun a b hab hb => hP a b (by omega) hab hb, hxm, hF⟩

theorem nodup_twp {z : M} {M0 : Nat → UInt8} {n : Nat} {ids : List NearSpec.Bytes} (hm : z.mem = M0)
    (hk8 : z.regs 14 = 8) (h8 : z.regs 8 = 0) (h7 : z.regs 7 = n) (hn : n ≤ 256) (hr : RidOK M0 n ids)
    (hnd : ∀ a b, a < b → b < n → ids.getD a [] ≠ ids.getD b []) :
    twp P (Inp pub cb pb) (forUp 8 7 5 nBody) z (fun z' c => z'.mem = M0 ∧
      Frame [0, 1, 2, 3, 4, 5, 8, 11, 12, 13] z z' ∧ c ≤ 2240000) := by
  refine twp_forUp (i := 8) (n := 7) (t := 5) (by decide) (by decide) (by decide)
    (J := fun i x => x.mem = M0 ∧ Frame [0, 1, 2, 3, 4, 5, 8, 11, 12, 13] z x) (N := n) (B := 8726) (by omega) ?_
    ⟨hm, Frame.refl _ _⟩ h8 h7 ?_ ?_
  · intro j x v w ⟨hxm, hF⟩
    exact ⟨hxm, AccountIdProof.fsr (by simp) (AccountIdProof.fsr (by simp) hF)⟩
  · intro i x hi ⟨hxm, hF⟩ hx8 hx7
    simp only [nBody]
    refine twp_seqs_append _ _ _ _ (by simp [nHead]) (by simp) ?_
    refine twp_mono (head_twp (by rw [hF 14 (by decide), hk8]) hx8 (by omega)) ?_
    rintro y c1 ⟨hym, hy2, hy3, hFy, hc1⟩
    simp only [seqs]
    rw [hxm] at hym hy2
    refine twp_mono (innerLoop_twp hym (by rw [hFy 14 (by decide), hF 14 (by decide), hk8]) hy2 hy3
      (by rw [hFy 7 (by decide), hx7]) hi hn hr (fun b h1 h2 => hnd i b h1 h2)) ?_
    rintro y' c2 ⟨hm', hFy', hc2⟩
    exact ⟨⟨hm', frame_ext (frame_ext hF hFy (by decide)) hFy' (by decide)⟩,
      by rw [hFy' 8 (by decide), hFy 8 (by decide), hx8], by rw [hFy' 7 (by decide), hFy 7 (by decide), hx7],
      by omega⟩
  · intro x c ⟨hxm, hF⟩ _ hc
    refine ⟨hxm, hF, ?_⟩
    have : n * (8726 + 4) ≤ 256 * 8730 := Nat.mul_le_mul (by omega) (by omega)
    omega
end

end RcptProof

end ReexecNpai
