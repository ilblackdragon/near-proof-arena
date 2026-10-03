import ReexecNpai.Spec.State
import ReexecNpai.Spec.WalkAux4

/-!
# Batch, part 1: target keys and walks

* `pKey`: the target key `accountKeyPath receiver` as one nibble per byte at `S_KEY`;
* `pWalk`: `PTrie.get` on the arena (the `Walk` relation of `Trie/Arena.lean`).
-/

set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

open WalkProof WalkAux

section
variable {pub cb pb : Bytes}

theorem key_wp {m : M} (hb : Base m) (hp : m.regs 1 + m.regs 2 ≤ P.memSize) (hlen : m.regs 2 ≤ 64)
    (hdis : S_KEY + 130 ≤ m.regs 1 ∨ m.regs 1 + m.regs 2 ≤ S_KEY) :
    wp P (Inp pub cb pb) pKey m (fun m' =>
      readMem m'.mem S_KEY (2 + 2 * m.regs 2) = nibBytes (accountKeyPath (readMem m.mem (m.regs 1) (m.regs 2))) ∧
      m'.regs 3 = 2 + 2 * m.regs 2 ∧ KeepOut S_KEY (S_KEY + 130) m m' ∧ Frame [0, 3, 4, 11, 12, 13] m m') := by
  obtain ⟨hk1, hk8, -⟩ := hb
  simp only [P_memSize] at hp
  simp only [pKey]
  walk_vc [hk1, hk8]
  refine wp_forUp (i := 3) (n := 2) (t := 4) (by decide) (by decide) (by decide)
    (J := fun j x => Frame [0, 3, 4, 11, 12, 13] m x ∧
      (∀ a, (a < S_KEY ∨ S_KEY + 2 + 2 * j ≤ a) → x.mem a = m.mem a) ∧
      readMem x.mem S_KEY (2 + 2 * j) = nibBytes (nibbles (0 :: readMem m.mem (m.regs 1) j)))
    (N := m.regs 2) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · omega
  · intro j x v w ⟨hF, hM, hR⟩
    exact ⟨fsr (by simp) (fsr (by simp) hF), hM, hR⟩
  · refine ⟨?_, ?_, ?_⟩
    · repeat (first | exact fun _ _ => rfl | refine fsr (by simp) ?_)
    · intro a ha; simp only [wm1, S_KEY] at ha ⊢; rw [ite_neg (by omega), ite_neg (by omega)]
    · simp only [wm1, S_KEY, readMem, List.range, List.range.loop]; simp [nibbles, nibBytes]
  · simp
  · simp [setReg_apply]
  · intro j x hj ⟨hF, hM, hR⟩ hi hn
    have hx1 := hF 1 (by simp)
    have hx14 := hF 14 (by simp)
    have hx15 := hF 15 (by simp)
    walk_vc [hx1, hi, hn, hx14, hx15, hk1, hk8]
    intro m1 h1 e1; subst e1; intro m2 h2 e2; subst e2
    walk_vc
    have hb : x.mem (m.regs 1 + j) = m.mem (m.regs 1 + j) := hM _ (by simp only [S_KEY] at hdis ⊢; omega)
    have hbl := byte_lt (m.mem (m.regs 1 + j))
    rw [hb, evShr4 _ hbl, evAnd15]
    refine ⟨?_, ?_, ?_, hi, hn⟩
    · repeat (first | exact hF | refine fsr (by simp) ?_)
    · intro a ha; rw [wm1, wm1, ite_neg (by omega), ite_neg (by omega)]; exact hM a (by simp only [S_KEY]; omega)
    · rw [show 2 + 2 * (j + 1) = (2 + 2 * j) + 1 + 1 by omega, readMem_snoc, readMem_snoc, wm1, wm1, wm1, wm1,
        readMem_wm1_out _ _ _ _ _ (by omega), readMem_wm1_out _ _ _ _ _ (by omega)]
      simp only [S_KEY] at hR
      rw [hR, readMem_snoc, nibbles_snoc, nibBytes_append]
      simp only [ite_neg (show ¬ 512 + (2 + 2 * j) = j + j + 514 + 1 by omega),
        ite_pos (show 512 + (2 + 2 * j) = j + j + 514 by omega),
        ite_pos (show 512 + (2 + 2 * j + 1) = j + j + 514 + 1 by omega), List.append_assoc, nibBytes,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      congr 3 <;> (congr 1; omega)
  · intro x ⟨hF, hM, hR⟩ hn
    walk_vc [hn]
    refine ⟨hR, by omega, ⟨?_, ?_, ?_⟩, ?_⟩
    · simp [setReg_apply]; exact hF 14 (by simp)
    · simp [setReg_apply]; exact hF 15 (by simp)
    · intro a ha; exact hM a (by simp only [S_KEY]; omega)
    · repeat (first | exact hF | refine fsr (by simp) ?_)

theorem key_twp {m : M} (hb : Base m) (hp : m.regs 1 + m.regs 2 ≤ P.memSize) (hlen : m.regs 2 ≤ 64)
    (hdis : S_KEY + 130 ≤ m.regs 1 ∨ m.regs 1 + m.regs 2 ≤ S_KEY) :
    twp P (Inp pub cb pb) pKey m (fun m' c =>
      readMem m'.mem S_KEY (2 + 2 * m.regs 2) = nibBytes (accountKeyPath (readMem m.mem (m.regs 1) (m.regs 2))) ∧
      m'.regs 3 = 2 + 2 * m.regs 2 ∧ KeepOut S_KEY (S_KEY + 130) m m' ∧ Frame [0, 3, 4, 11, 12, 13] m m' ∧
      c ≤ 2000) := by
  obtain ⟨hk1, hk8, -⟩ := hb
  simp only [P_memSize] at hp
  simp only [pKey]
  walk_vc [hk1, hk8]
  refine twp_forUp (i := 3) (n := 2) (t := 4) (by decide) (by decide) (by decide)
    (J := fun j x => Frame [0, 3, 4, 11, 12, 13] m x ∧
      (∀ a, (a < S_KEY ∨ S_KEY + 2 + 2 * j ≤ a) → x.mem a = m.mem a) ∧
      readMem x.mem S_KEY (2 + 2 * j) = nibBytes (nibbles (0 :: readMem m.mem (m.regs 1) j)))
    (N := m.regs 2) (B := 11) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · omega
  · intro j x v w ⟨hF, hM, hR⟩
    exact ⟨fsr (by simp) (fsr (by simp) hF), hM, hR⟩
  · refine ⟨?_, ?_, ?_⟩
    · repeat (first | exact fun _ _ => rfl | refine fsr (by simp) ?_)
    · intro a ha; simp only [wm1, S_KEY] at ha ⊢; rw [ite_neg (by omega), ite_neg (by omega)]
    · simp only [wm1, S_KEY, readMem, List.range, List.range.loop]; simp [nibbles, nibBytes]
  · simp
  · simp [setReg_apply]
  · intro j x hj ⟨hF, hM, hR⟩ hi hn
    have hx1 := hF 1 (by simp)
    have hx14 := hF 14 (by simp)
    have hx15 := hF 15 (by simp)
    walk_vc [hx1, hi, hn, hx14, hx15, hk1, hk8]
    refine ⟨by omega, by omega, ?_⟩
    have hb : x.mem (m.regs 1 + j) = m.mem (m.regs 1 + j) := hM _ (by simp only [S_KEY] at hdis ⊢; omega)
    have hbl := byte_lt (m.mem (m.regs 1 + j))
    rw [hb, evShr4 _ hbl, evAnd15]
    refine ⟨?_, ?_, ?_⟩
    · repeat (first | exact hF | refine fsr (by simp) ?_)
    · intro a ha; rw [wm1, wm1, ite_neg (by omega), ite_neg (by omega)]; exact hM a (by simp only [S_KEY]; omega)
    · rw [show 2 + 2 * (j + 1) = (2 + 2 * j) + 1 + 1 by omega, readMem_snoc, readMem_snoc, wm1, wm1, wm1, wm1,
        readMem_wm1_out _ _ _ _ _ (by omega), readMem_wm1_out _ _ _ _ _ (by omega)]
      simp only [S_KEY] at hR
      rw [hR, readMem_snoc, nibbles_snoc, nibBytes_append]
      simp only [ite_neg (show ¬ 512 + (2 + 2 * j) = j + j + 514 + 1 by omega),
        ite_pos (show 512 + (2 + 2 * j) = j + j + 514 by omega),
        ite_pos (show 512 + (2 + 2 * j + 1) = j + j + 514 + 1 by omega), List.append_assoc, nibBytes,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append]
      congr 3 <;> (congr 1; omega)
  · intro x c ⟨hF, hM, hR⟩ hn hc
    walk_vc [hn]
    refine ⟨hR, by omega, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · simp [setReg_apply]; exact hF 14 (by simp)
    · simp [setReg_apply]; exact hF 15 (by simp)
    · intro a ha; exact hM a (by simp only [S_KEY]; omega)
    · repeat (first | exact hF | refine fsr (by simp) ?_)
    · have : m.regs 2 * (11 + 4) ≤ 64 * 15 := Nat.mul_le_mul hlen (Nat.le_refl _)
      omega

/-- The entry the walk starts from. -/
def rootRes (A : List Ent) : Nat := (A.getD (A.length - 1) default).res

/-- One iteration of the walk loop. -/
def walkBody : Stmt := seqs [lt 0 7, CST 4 24, MUL 4 0 4, ADDI 4 4 AR, ld32 5 4, LD8 6 5,
  .ite 6 (seqs [CST 10 3, EQ 10 6 10, .ite 10 pWalkExt pWalkBranch]) pWalkLeaf]

theorem pWalk_eq : pWalk = seqs [ldCell 7 C_NODES, SUB 4 7 15, CST 5 24, MUL 4 4 5, ADDI 4 4 (AR + 16), ld32 0 4,
    CST 1 0, CST 2 1, .loop 2 walkBody] := rfl

/-- Loop invariant of the walk (soundness). -/
def WI (key : List Nat) (A : List Ent) (K : List Nat) (m x : M) : Prop :=
  Com key.length A.length m x ∧
  (x.regs 2 ≠ 0 → x.regs 1 ≤ key.length ∧
    ∀ f, Walk A K (x.regs 0) (key.drop (x.regs 1)) f → Walk A K (rootRes A) key f) ∧
  (x.regs 2 = 0 → x.regs 0 < A.length ∧
    ((A.getD (x.regs 0) default).val ≠ 0 → Walk A K (rootRes A) key (x.regs 0)))

theorem drop_cons_getD {key : List Nat} {o : Nat} (h : o < key.length) :
    key.drop o = key.getD o 0 :: key.drop (o + 1) := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem drop_take_append {key k : List Nat} {o : Nat} (h : (key.drop o).take k.length = k) :
    key.drop o = k ++ key.drop (o + k.length) := by
  conv => lhs; rw [← List.take_append_drop k.length (key.drop o)]
  rw [h, List.drop_drop, Nat.add_comm]

set_option maxHeartbeats 1000000 in
theorem walkBody_wp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes}
    (h : TrieSt cb pb rs R A K vals m) {key : List Nat}
    (hkey : readMem m.mem S_KEY key.length = nibBytes key) (hk16 : ∀ x ∈ key, x < 16)
    (hkl : key.length ≤ 130) {x : M} (hI : WI key A K m x) (h2 : x.regs 2 ≠ 0) :
    wp P (Inp pub cb pb) walkBody x (WI key A K m) := by
  obtain ⟨hc, hcont, -⟩ := hI
  obtain ⟨ho, hs⟩ := hcont h2
  obtain ⟨hc3, hc7, hc9, hc14, hc15, hcm⟩ := hc
  simp only [walkBody]
  walk_vc [hc7, hc14, hc15]
  intro hjN
  obtain ⟨e, hj⟩ : ∃ e, A[x.regs 0]? = some e := ⟨_, List.getElem?_eq_getElem hjN⟩
  obtain ⟨hpf, hpe, -, -, hval, -⟩ := ent_bounds h hj
  simp only [PF] at hpf
  have hpre : ArenaCore.Bytes.leToNat (readMem x.mem (x.regs 0 * 24 + 117000) 4) = e.pre := by
    rw [rd_m hcm (by simp only [S_HP]; omega), show x.regs 0 * 24 + 117000 = AR + 24 * x.regs 0 by
      simp only [AR]; omega]
    exact (ent_mem h hj).1
  have hN := h.tok.wf.len_le
  simp only [NCAP] at hN
  rw [wp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, hc14])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]
        rw [evM _ _ (by omega), evAddi _ _ (by omega)]; omega) (by simp)]
  walk_vc [hpre]
  intro y _ ey; subst ey
  have hcy : ∀ r : Nat → Nat, r 3 = x.regs 3 → r 7 = x.regs 7 → r 9 = x.regs 9 → r 14 = x.regs 14 →
      r 15 = x.regs 15 → Com key.length A.length m { regs := r, mem := x.mem } :=
    fun r e3 e7 e9 e14 e15 => ⟨e3.trans hc3, e7.trans hc7, e9.trans hc9, e14.trans hc14, e15.trans hc15, hcm⟩
  have htag : (x.mem e.pre).toNat = (m.mem e.pre).toNat := by rw [hcm _ (by simp only [S_HP]; omega)]
  cases hnf : e.nf with
  | leaf k ref mm =>
    have ht := (leaf_hdr h hj hnf).1
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, htag, ht]
    refine ⟨fun _ => ?_, fun h0 => absurd rfl h0⟩
    refine wp_mono (walkLeaf_wp h hkey hk16 hkl (hcy _ (by simp [setReg_apply]) (by simp [setReg_apply])
      (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])) hj hnf (by simp [setReg_apply]) (by simp [setReg_apply])
      (by simp [setReg_apply]) ho) ?_
    rintro y' ⟨hc', h2', h0', hkd⟩
    refine ⟨hc', fun h => absurd h2' h, fun _ => ⟨by rw [h0']; exact hjN, fun hv => ?_⟩⟩
    rw [h0'] at hv ⊢
    rw [getD_of hj] at hv
    have hv' := hval hv
    rw [hnf] at hv'
    cases ref with
    | some _ => simp [hasVal] at hv'
    | none => exact hs _ (hkd ▸ Walk.leaf hj hnf)
  | ext k hh mm =>
    have ht := (ext_hdr h hj hnf).1
    simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, htag, ht]
    refine ⟨fun h => h.elim, fun _ => ⟨fun h => absurd trivial h, fun _ => ?_⟩⟩
    refine wp_mono (walkExt_wp h hkey hk16 hkl (hcy _ (by simp [setReg_apply]) (by simp [setReg_apply])
      (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])) hj hnf (by simp [setReg_apply])
      (by simp [setReg_apply]) (by simp [setReg_apply]) ho) ?_
    rintro y' ⟨hc', h2', hhn, hkL, htk, h1', h0'⟩
    subst hhn
    have h2'' : y'.regs 2 ≠ 0 := by rw [h2']; simpa [setReg_apply] using h2
    refine ⟨hc', fun _ => ⟨by rw [h1']; exact hkL, fun f hw => ?_⟩, fun h => absurd h h2''⟩
    rw [h1', h0'] at hw
    apply hs
    rw [drop_take_append htk]
    exact Walk.ext hj hnf hw
  | branch v ks mm =>
    have ht := (br_hdr h hj hnf).1
    have hpost : ∀ y', (Com key.length A.length m y' ∧
        ((x.regs 1 = key.length ∧ y'.regs 2 = 0 ∧ y'.regs 0 = x.regs 0) ∨
         (x.regs 1 < key.length ∧ y'.regs 2 = x.regs 2 ∧ ks[key.getD (x.regs 1) 0]? = some (some none) ∧
          y'.regs 1 = x.regs 1 + 1 ∧
          y'.regs 0 = (A.getD (childIdx K e.kid (nRev ks) (revBelow ks (key.getD (x.regs 1) 0))) default).res))) →
        WI key A K m y' := by
      rintro y' ⟨hc', (⟨hoL, h2', h0'⟩ | ⟨hoL, h2', hks, h1', h0'⟩)⟩
      · refine ⟨hc', fun h => absurd h2' h, fun _ => ⟨by rw [h0']; exact hjN, fun hv => ?_⟩⟩
        rw [h0'] at hv ⊢
        rw [getD_of hj] at hv
        have hv' := hval hv
        rw [hnf] at hv'
        rcases v with _ | _ | _
        · simp [hasVal] at hv'
        · apply hs; rw [hoL, List.drop_length]; exact Walk.brv hj hnf
        · simp [hasVal] at hv'
      · refine ⟨hc', fun _ => ⟨by rw [h1']; omega, fun f hw => ?_⟩, fun h => absurd h (by rw [h2']; exact h2)⟩
        rw [h1', h0'] at hw
        apply hs
        rw [drop_cons_getD hoL]
        exact Walk.br hj hnf hks hw
    rcases ht with ht | ht
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, htag, ht]
      refine ⟨fun h => absurd h (by decide), fun _ => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
      refine wp_mono (walkBr_wp h hkey hk16 hkl (hcy _ (by simp [setReg_apply]) (by simp [setReg_apply])
        (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])) hj hnf (by simp [setReg_apply])
        (by simp [setReg_apply]) (by simp [setReg_apply]) ho) (fun y' hy => hpost y' (by simpa [setReg_apply] using hy))
    · simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, htag, ht]
      refine ⟨fun h => absurd h (by decide), fun _ => ⟨fun _ => ?_, fun h => absurd h (by decide)⟩⟩
      refine wp_mono (walkBr_wp h hkey hk16 hkl (hcy _ (by simp [setReg_apply]) (by simp [setReg_apply])
        (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])) hj hnf (by simp [setReg_apply])
        (by simp [setReg_apply]) (by simp [setReg_apply]) ho) (fun y' hy => hpost y' (by simpa [setReg_apply] using hy))

theorem walk_preImg_len (nf : NF) (vl : Nat) (z : Bytes) (zs : List Bytes) : 1 ≤ (preImg nf vl z zs).length := by
  cases nf with
  | leaf k ref mm => simp [preImg]
  | ext k h mm => simp [preImg]
  | branch v ks mm => rcases v with _ | _ | _ <;> simp [preImg] <;> omega

theorem walk_f_lt {A : List Ent} {K : List Nat} {r : Nat} {key : List Nat} {f : Nat}
    (h : Walk A K r key f) : f < A.length := by
  induction h with
  | leaf he _ => exact lt_of_get he
  | brv he _ => exact lt_of_get he
  | ext _ _ _ ih => exact ih
  | br _ _ _ _ ih => exact ih

/-- Loop invariant of the walk (completeness), for the target entry `f`. -/
def TI (key : List Nat) (A : List Ent) (K : List Nat) (m : M) (f : Nat) (x : M) : Prop :=
  Com key.length A.length m x ∧
  (x.regs 2 ≠ 0 → x.regs 1 ≤ key.length ∧ Walk A K (x.regs 0) (key.drop (x.regs 1)) f ∧
    ∃ i : Nat, ∃ ei : Ent, A[i]? = some ei ∧ ei.res = x.regs 0) ∧
  (x.regs 2 = 0 → x.regs 0 = f)

/-- Potential of the walk loop. -/
def TPot (key : List Nat) (x : M) : Nat := if x.regs 2 = 0 then 0 else 400 * (key.length - x.regs 1) + 400

set_option maxHeartbeats 1000000 in
theorem walkBody_twp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes}
    (h : TrieSt cb pb rs R A K vals m) {key : List Nat}
    (hkey : readMem m.mem S_KEY key.length = nibBytes key) (hk16 : ∀ x ∈ key, x < 16)
    (hkl : key.length ≤ 130) {f : Nat} {x : M} (hI : TI key A K m f x) (h2 : x.regs 2 ≠ 0) :
    twp P (Inp pub cb pb) walkBody x (fun x' c => TI key A K m f x' ∧ c + 2 + TPot key x' ≤ TPot key x) := by
  obtain ⟨hc, hcont, -⟩ := hI
  obtain ⟨ho, hw, i, ei, hi, hres⟩ := hcont h2
  obtain ⟨hc3, hc7, hc9, hc14, hc15, hcm⟩ := hc
  have hjN := walk_lt hw
  obtain ⟨e, hj⟩ : ∃ e, A[x.regs 0]? = some e := ⟨_, List.getElem?_eq_getElem hjN⟩
  obtain ⟨hpf, hpe, -, ⟨z, zs, hpm⟩, -, -⟩ := ent_bounds h hj
  have hpl := congrArg List.length hpm
  rw [readMem_length] at hpl
  have := walk_preImg_len e.nf (vlenAt pb e) z zs
  simp only [PF] at hpf
  have hpre : ArenaCore.Bytes.leToNat (readMem x.mem (x.regs 0 * 24 + 117000) 4) = e.pre := by
    rw [rd_m hcm (by simp only [S_HP]; omega), show x.regs 0 * 24 + 117000 = AR + 24 * x.regs 0 by
      simp only [AR]; omega]
    exact (ent_mem h hj).1
  have hN := h.tok.wf.len_le
  simp only [NCAP] at hN
  have hcy : ∀ r : Nat → Nat, r 3 = x.regs 3 → r 7 = x.regs 7 → r 9 = x.regs 9 → r 14 = x.regs 14 →
      r 15 = x.regs 15 → Com key.length A.length m { regs := r, mem := x.mem } :=
    fun r e3 e7 e9 e14 e15 => ⟨e3.trans hc3, e7.trans hc7, e9.trans hc9, e14.trans hc14, e15.trans hc15, hcm⟩
  have htag : (x.mem e.pre).toNat = (m.mem e.pre).toNat := by rw [hcm _ (by simp only [S_HP]; omega)]
  have hpot : TPot key x = 400 * (key.length - x.regs 1) + 400 := by simp [TPot, h2]
  simp only [walkBody]
  walk_vc [hc7, hc14, hc15]
  refine ⟨by decide, ?_⟩
  rw [twp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, hc14])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
  walk_vc [hpre]
  have hcyy := hcy (setReg (setReg (setReg (setReg (setReg (setReg (setReg x.regs 13 1) 4 24) 4 (x.regs 0 * 24)) 4
    (x.regs 0 * 24 + 117000)) 12 (x.mem (x.regs 0 * 24 + 117000)).toNat) 5 e.pre) 6 (x.mem e.pre).toNat)
    (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
    (by simp [setReg_apply])
  have hcyz := hcy (setReg (setReg (setReg (setReg (setReg (setReg (setReg (setReg (setReg x.regs 13 1) 4 24) 4
    (x.regs 0 * 24)) 4 (x.regs 0 * 24 + 117000)) 12 (x.mem (x.regs 0 * 24 + 117000)).toNat) 5 e.pre) 6
    (x.mem e.pre).toNat) 10 3) 10 (if (x.mem e.pre).toNat = 3 then 1 else 0))
    (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply])
    (by simp [setReg_apply])
  -- the node is a `res` target, so not an extension with an empty key
  have hne : ∀ mm, e.nf ≠ .ext [] none mm := by
    rcases res_spec h.tok.wf (vals := vals) hi with ⟨hr, -⟩ | ⟨e', he', -, hx1, -, -⟩
    · rw [hres] at hr; simp only [RNONE] at hr; omega
    · rw [hres, hj] at he'; cases he'; exact hx1
  rcases walk_inv hw hj with ⟨mm, hnf, hf⟩ | ⟨ks, mm, hnf, hdr, hf⟩ | ⟨k, mm, rest, hnf, hdr, hw'⟩ |
      ⟨v, ks, mm, n, rest, hnf, hks, hdr, hw'⟩
  · -- leaf
    have ht := (leaf_hdr h hj hnf).1
    refine Or.inl ⟨by rw [htag, ht], twp_mono (walkLeaf_twp h hkey hk16 hkl hcyy hj hnf (by simp [setReg_apply])
      (by simp [setReg_apply]) (by simp [setReg_apply]) ho rfl) ?_⟩
    rintro y' c ⟨hc', h2', h0', hcst⟩
    refine ⟨⟨hc', fun h => absurd h2' h, fun _ => by rw [h0', hf]⟩, ?_⟩
    rw [hpot]; simp only [TPot, h2', ↓reduceIte]
    omega
  · -- branch with the value, key exhausted
    have hoL : x.regs 1 = key.length := by
      have := congrArg List.length hdr; simp at this; omega
    have ht := (br_hdr h hj hnf).1
    have ht' : (x.mem e.pre).toNat = 1 ∨ (x.mem e.pre).toNat = 2 := by rw [htag]; exact ht
    refine Or.inr ⟨by omega, Or.inl ⟨by omega, twp_mono (walkBrStop_twp h hkey hk16 hkl hcyz hj hnf
      (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) hoL) ?_⟩⟩
    rintro y' c ⟨hc', h2', h0', hcst⟩
    refine ⟨⟨hc', fun h => absurd h2' h, fun _ => by rw [h0', hf]⟩, ?_⟩
    rw [hpot]; simp only [TPot, h2', ↓reduceIte]
    omega
  · -- extension
    have hk0 : k ≠ [] := by rintro rfl; exact hne mm hnf
    have hkL : x.regs 1 + k.length ≤ key.length := by
      have := congrArg List.length hdr; simp at this; omega
    have htk : (key.drop (x.regs 1)).take k.length = k := by rw [hdr, List.take_left' rfl]
    have hrest : rest = key.drop (x.regs 1 + k.length) := by
      have := congrArg (List.drop k.length) hdr
      rw [List.drop_left' rfl, List.drop_drop] at this; exact this.symm
    have ht := (ext_hdr h hj hnf).1
    have ht' : (x.mem e.pre).toNat = 3 := by rw [htag]; exact ht
    obtain ⟨ec, hec, -, -, -⟩ := ext_child h.tok.wf hj hnf
    refine Or.inr ⟨by omega, Or.inr ⟨ht', twp_mono (walkExt_twp h hkey hk16 hkl hcyz hj hnf
      (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) ho rfl hkL htk) ?_⟩⟩
    rintro y' c ⟨hc', h2', h1', h0', hcst⟩
    have h2'' : y'.regs 2 ≠ 0 := by rw [h2']; simpa [setReg_apply] using h2
    have hkpos : 1 ≤ k.length := by cases k with | nil => exact absurd rfl hk0 | cons _ _ => simp
    refine ⟨⟨hc', fun _ => ⟨by rw [h1']; exact hkL, by rw [h1', h0', ← hrest]; exact hw',
      K.getD e.kid 0, ec, hec, by rw [h0', getD_of hec]⟩, fun h => absurd h h2''⟩, ?_⟩
    rw [hpot]; simp only [TPot, h2'', ↓reduceIte, h1']
    have : 400 * (key.length - x.regs 1) = 400 * (key.length - (x.regs 1 + k.length)) + 400 * k.length := by
      rw [← Nat.mul_add]; congr 1; omega
    omega
  · -- branch step
    have hoL : x.regs 1 < key.length := by
      have := congrArg List.length hdr; simp at this; omega
    rw [drop_cons_getD hoL, List.cons.injEq] at hdr
    obtain ⟨hn, hrest⟩ := hdr
    rw [← hn] at hks
    have ht := (br_hdr h hj hnf).1
    have ht' : (x.mem e.pre).toNat = 1 ∨ (x.mem e.pre).toNat = 2 := by rw [htag]; exact ht
    have hlt := revBelow_lt ks _ hks
    obtain ⟨ec, hec, -, -, -⟩ := child_info h.tok.wf hj (q := revBelow ks (key.getD (x.regs 1) 0))
      (by rw [hnf]; exact hlt)
    simp only [hnf, nKids] at hec
    refine Or.inr ⟨by omega, Or.inl ⟨by omega, twp_mono (walkBrStep_twp h hkey hk16 hkl hcyz hj hnf
      (by simp [setReg_apply]) (by simp [setReg_apply]) (by simp [setReg_apply]) hoL hks) ?_⟩⟩
    rintro y' c ⟨hc', h2', h1', h0', hcst⟩
    have h2'' : y'.regs 2 ≠ 0 := by rw [h2']; simpa [setReg_apply] using h2
    refine ⟨⟨hc', fun _ => ⟨by rw [h1']; omega, by rw [h1', h0', hrest, hn]; exact hw',
      _, ec, hec, by rw [h0', getD_of hec]⟩, fun h => absurd h h2''⟩, ?_⟩
    rw [hpot]; simp only [TPot, h2'', ↓reduceIte, h1']
    omega

theorem walk_wp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes}
    (h : TrieSt cb pb rs R A K vals m) {key : List Nat}
    (hkey : readMem m.mem S_KEY key.length = nibBytes key) (hk16 : ∀ x ∈ key, x < 16)
    (hkl : key.length ≤ 130) (h3 : m.regs 3 = key.length) :
    wp P (Inp pub cb pb) pWalk m (fun m' => ∃ f, f < A.length ∧ m'.regs 0 = f ∧
      ((A.getD f default).val ≠ 0 → Walk A K (rootRes A) key f) ∧
      m'.regs 9 = m.regs 9 ∧ KeepOut S_HP (S_HP + 128) m m') := by
  have hk1 : m.regs 15 = 1 := h.k1
  have hk8 : m.regs 14 = 8 := h.k8
  have hN0 := h.tok.wf.len_pos
  have hN := h.tok.wf.len_le
  simp only [NCAP] at hN
  have hnodes : ArenaCore.Bytes.leToNat (readMem m.mem 3120 4) = A.length := h.tmem.nodes
  obtain ⟨er, her⟩ : ∃ er, A[A.length - 1]? = some er := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hroot : ArenaCore.Bytes.leToNat (readMem m.mem ((A.length - 1) * 24 + 117016) 4) = rootRes A := by
    rw [show (A.length - 1) * 24 + 117016 = AR + 24 * (A.length - 1) + 16 by simp only [AR]; omega,
      (ent_mem h her).2.2, rootRes, getD_of her]
  rw [pWalk_eq]
  simp only [ldCell]
  walk_vc [hk1, hk8]
  rw [wp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, hk8])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
  walk_vc [hk1, hk8, hnodes]
  rw [wp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, hk8])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
  walk_vc [hk1, hk8, hroot]
  refine wp_loop (I := WI key A K m) ⟨⟨by simp [setReg_apply, h3], by simp [setReg_apply],
    by simp [setReg_apply], by simp [setReg_apply, hk8], by simp [setReg_apply, hk1], fun _ _ => rfl⟩,
    fun _ => ⟨by simp [setReg_apply], fun f hw => by simpa [setReg_apply] using hw⟩, fun h => by simp [setReg_apply] at h⟩
    (fun x hI h2 => walkBody_wp h hkey hk16 hkl hI h2) ?_
  rintro x ⟨⟨-, -, hc9, hc14, hc15, hcm⟩, -, hfin⟩ h2
  obtain ⟨hlt, hw⟩ := hfin h2
  exact ⟨x.regs 0, hlt, rfl, hw, hc9, ⟨by rw [hc14, hk8], by rw [hc15, hk1], hcm⟩⟩

theorem walk_twp {m : M} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat} {vals : Nat → Bytes}
    (h : TrieSt cb pb rs R A K vals m) {key : List Nat}
    (hkey : readMem m.mem S_KEY key.length = nibBytes key) (hk16 : ∀ x ∈ key, x < 16)
    (hkl : key.length ≤ 130) (h3 : m.regs 3 = key.length) {f : Nat} (hw : Walk A K (rootRes A) key f) :
    twp P (Inp pub cb pb) pWalk m (fun m' c => m'.regs 0 = f ∧ f < A.length ∧ m'.regs 9 = m.regs 9 ∧
      KeepOut S_HP (S_HP + 128) m m' ∧ c ≤ 60000) := by
  have hk1 : m.regs 15 = 1 := h.k1
  have hk8 : m.regs 14 = 8 := h.k8
  have hN0 := h.tok.wf.len_pos
  have hN := h.tok.wf.len_le
  simp only [NCAP] at hN
  have hnodes : ArenaCore.Bytes.leToNat (readMem m.mem 3120 4) = A.length := h.tmem.nodes
  obtain ⟨er, her⟩ : ∃ er, A[A.length - 1]? = some er := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hroot : ArenaCore.Bytes.leToNat (readMem m.mem ((A.length - 1) * 24 + 117016) 4) = rootRes A := by
    rw [show (A.length - 1) * 24 + 117016 = AR + 24 * (A.length - 1) + 16 by simp only [AR]; omega,
      (ent_mem h her).2.2, rootRes, getD_of her]
  have hfl := walk_f_lt hw
  rw [pWalk_eq]
  simp only [ldCell]
  walk_vc [hk1, hk8]
  rw [twp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, hk8])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
  walk_vc [hk1, hk8, hnodes]
  rw [twp_ld32 (by decide) (by decide) (by decide) (by decide) (by simp [setReg_apply, hk8])
    (by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, P_memSize]; omega) (by simp)]
  walk_vc [hk1, hk8, hroot]
  refine twp_loop (I := TI key A K m f) (Pot := TPot key) ⟨⟨by simp [setReg_apply, h3], by simp [setReg_apply],
    by simp [setReg_apply], by simp [setReg_apply, hk8], by simp [setReg_apply, hk1], fun _ _ => rfl⟩,
    fun _ => ⟨by simp [setReg_apply], by simpa [setReg_apply] using hw,
      A.length - 1, er, her, by simp only [setReg_apply, Nat.reduceEqDiff, ↓reduceIte, rootRes, getD_of her]⟩,
    fun h => by simp [setReg_apply] at h⟩
    (fun x hI h2 => walkBody_twp h hkey hk16 hkl hI h2) ?_
  rintro x c ⟨⟨-, -, hc9, hc14, hc15, hcm⟩, -, hfin⟩ h2 hc
  have h0 := hfin h2
  simp only [TPot, h2, ↓reduceIte, setReg_apply, Nat.reduceEqDiff] at hc
  refine ⟨h0, hfl, hc9, ⟨by rw [hc14, hk8], by rw [hc15, hk1], hcm⟩, ?_⟩
  omega

end

end ReexecNpai
