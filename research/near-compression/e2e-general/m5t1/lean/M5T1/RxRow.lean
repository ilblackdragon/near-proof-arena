import M5T1.RxField

/-!
# M5T1.RxRow — `rx_rel_of_row`: an `RX` row's constraints give `RxRel` of its decoded values

Every gadget instance of `Rx.arith` (`RxField.lean`: `p_fcx`, `p_sum2`, `p_sum3`, `p_mul`, `p_burn`, …)
read as a natural-number equation, assembled into `RxRel (decode …)`.
-/

namespace M5T1.RxField

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound M5T1

variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

/-- an element of one of `Rx.arith`'s literal lists -/
macro "inL" H:term : term =>
  `(arith_zero $H _ (by unfold Rx.arith; simp only [List.mem_append, List.mem_cons, true_or, or_true]))

theorem bytes_of (H : Hyps tr t r pub) {g : String} {w : Nat} (hg : (g, w) ∈ Rx.byteGroups) :
    gv tr t r pub g w < 256 ^ w := val_lt' _ w (byt H g w hg)

/-- `Σ bytes ≠ 0` from `Rx.nonzero` -/
theorem p_nz {g : String} {w : Nat} (inv : String)
    (hz : ev tr t r pub (Rx.nonzero (Rx.bv g) w inv) = 0) (hw : w ≤ 32)
    (hb : ∀ k < w, cb tr t r pub g k < 256) :
    ((List.range w).map (cb tr t r pub g)).sum ≠ 0 := by
  have h := nz_lemma hz
  intro h0
  apply h
  apply ev_of_ize 0 _ (by unfold PP; omega)
  rw [ize_sumE, List.map_map]
  have key : ∀ l : List Nat, (l.map (cb tr t r pub g)).sum = 0 →
      (l.map (ize tr t r pub ∘ Rx.bv g)).sum = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons x l ih =>
      simp only [List.map_cons, List.sum_cons] at hl ⊢
      have := ih (by omega)
      simp only [Function.comp, ize_bv]; omega
  have := key _ h0
  rw [this]; rfl

theorem sum_zero_val {f : Nat → Nat} {n : Nat} (h : ((List.range n).map f).sum = 0) : val f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append] at h
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at h
    have hf : f n = 0 := by omega
    simp only [val, ih (by omega), hf, Nat.mul_zero]

theorem val_full {f : Nat → Nat} {n : Nat} (hb : ∀ k < n, f k < 256) (h : val f n = 256 ^ n - 1) :
    ∀ k < n, f k = 255 := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    simp only [val] at h
    have hlt := val_lt f n (fun j hj => hb j (by omega))
    have hn := hb n (by omega)
    have hp : 0 < 256 ^ n := Nat.pow_pos (by decide)
    have e1 : 256 ^ (n + 1) = 256 ^ n * 256 := by rw [Nat.pow_succ]
    rw [e1] at h
    -- the top byte is 255 and the rest is full
    have htop : f n = 255 := by
      rcases Nat.lt_or_ge (f n) 255 with hl | hge
      · exfalso
        have : 256 ^ n * f n ≤ 256 ^ n * 254 := Nat.mul_le_mul_left _ (by omega)
        omega
      · omega
    rcases Nat.lt_or_ge k n with hk' | hk'
    · have hrest : val f n = 256 ^ n - 1 := by
        rw [htop] at h; omega
      exact ih (fun j hj => hb j (by omega)) hrest k hk'
    · have : k = n := by omega
      subst this; exact htop

theorem sum_zero_of {f : Nat → Nat} {n : Nat} (h : ∀ k < n, f k = 0) : ((List.range n).map f).sum = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h n (by omega),
      ih (fun k hk => h k (by omega)), Nat.add_zero]

theorem u64_eq : U64 = 256 ^ 8 := by decide
theorem u128_eq : U128 = 256 ^ 16 := by decide

set_option maxHeartbeats 8000000 in
/-- **The `RX` row is `RxRel`**: on any trace, a row whose constraints vanish, with `act = 1` and the
`RNG` facts, carries values in the relation the spec's receipt step computes (`SpecLink`). -/
theorem rx_rel_of_row (H : Hyps tr t r pub) : RxRel (decode tr t r pub) := by
  have L := lens H
  have hfcx := p_fcx H
  have hgb := p_sum3 H "vb" "gb" "cgb" (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (inA H)
  have hgu := p_sum3 H "vu" "gu" "cgu" (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (inA H)
  have hcu := p_sum3 H "vc" "cu" "ccu" (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (inA H)
  have hdv := p_sum2 H 8 (by decide) "vb" "dvu" "vu" "cdv" 0 0 (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups]) rfl (by omega) (inA H)
  have had := p_sum2 H 16 (by decide) "amt" "dep" "ad" "cad" 0 0 (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups]) rfl (by omega) (inA H)
  -- amount ≠ u128::MAX
  have ba := byt H "amt" 16 (by simp [Rx.byteGroups])
  have hiam : ((List.range 16).map fun k => 255 - cb tr t r pub "amt" k).sum ≠ 0 := by
    have hz : ev tr t r pub (Rx.nonzero (fun k => K 255 - Rx.c "amt" k) 16 "iam") = 0 := inL H
    have h := nz_lemma hz
    intro h0; apply h
    apply ev_of_ize 0 _ (by unfold PP; omega)
    rw [ize_sumE, List.map_map]
    have key : ∀ l : List Nat, (∀ k ∈ l, k < 16) → (l.map fun k => 255 - cb tr t r pub "amt" k).sum = 0 →
        (l.map (ize tr t r pub ∘ fun k => K 255 - Rx.c "amt" k)).sum = 0 := by
      intro l hl h0
      induction l with
      | nil => rfl
      | cons x l ih =>
        simp only [List.map_cons, List.sum_cons] at h0 ⊢
        have := ih (fun k hk => hl k (List.mem_cons_of_mem _ hk)) (by omega)
        have hx := ba x (hl x (List.mem_cons_self ..))
        simp only [Function.comp, ize_hsub, ize_K, ize_c]; omega
    have := key _ (fun k hk => List.mem_range.1 hk) h0
    rw [this]; rfl
  -- storage stake
  have hreq := p_mul H (na := 8) (nb := 8) (by decide) (by decide) (by decide)
    (a := Rx.bv "vus") (b := Rx.kb STORAGE_PER_BYTE) (A := cb tr t r pub "vus")
    (B := fun j => STORAGE_PER_BYTE / 256 ^ j % 256) "req" "crq" (inA H) (fun i _ => rfl) (fun j _ => rfl)
    (byt H "vus" 8 (by simp [Rx.byteGroups])) (fun j _ => kb_lt _ _) (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups])
  rw [conv_8_8, show val (fun j => STORAGE_PER_BYTE / 256 ^ j % 256) 8 = STORAGE_PER_BYTE by decide] at hreq
  have hak := p_sum2 H 16 (by decide) "vbal" "lck" "ak" "cak" 0 0 (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups]) rfl (by omega) (inA H)
  have hb1 := bit1 H "b1" (by simp [Rx.bitGroups])
  have hb2 := bit1 H "b2" (by simp [Rx.bitGroups])
  have hs1 := p_sum2 H 16 (by decide) "req" "s1" "ak" "cs1" (Rx.c "b1") (cb tr t r pub "b1" 0)
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups])
    rfl hb1 (inA H)
  have hs2 := L_sum2 (N := 8) (by decide) (a := Rx.bv "vus") (b := Rx.bv "s2") (rr := Rx.kb ZERO_BALANCE_LIMIT)
    (cy := Rx.bv "cs2") (top := Rx.c "b2") (inA H) (A := cb tr t r pub "vus") (B := cb tr t r pub "s2")
    (R := fun k => ZERO_BALANCE_LIMIT / 256 ^ k % 256) (C := cb tr t r pub "cs2") (tp := cb tr t r pub "b2" 0)
    (fun k _ => rfl) (fun k _ => rfl) (fun k _ => rfl) (fun k _ => rfl) rfl
    (byt H "vus" 8 (by simp [Rx.byteGroups])) (byt H "s2" 8 (by simp [Rx.byteGroups])) (fun k _ => kb_lt _ _)
    (fun k hk => bit H "cs2" 7 (by simp [Rx.bitGroups]) k (by omega)) (by omega)
  rw [show val (fun k => ZERO_BALANCE_LIMIT / 256 ^ k % 256) 8 = ZERO_BALANCE_LIMIT by decide] at hs2
  have hb12 : ev tr t r pub (Rx.c "b1") = 0 ∨ ev tr t r pub (Rx.c "b2") = 0 := by
    have hz : ev tr t r pub (Rx.c "b1" * Rx.c "b2") = 0 := inL H
    exact ev_mul_eq_zero hz
  -- prices, refunds
  have hburn := p_burn H
  have hpx := L_sum2 (N := 8) (by decide) (a := Rx.bv "fcx") (b := Rx.kb NAR_EXEC) (rr := Rx.bv "pexec")
    (cy := Rx.bv "cpx") (top := 0) (inA H) (A := cb tr t r pub "fcx") (B := fun k => NAR_EXEC / 256 ^ k % 256)
    (R := cb tr t r pub "pexec") (C := cb tr t r pub "cpx") (tp := 0)
    (fun k _ => rfl) (fun k _ => rfl) (fun k _ => rfl) (fun k _ => rfl) rfl
    (byt H "fcx" 8 (by simp [Rx.byteGroups])) (fun k _ => kb_lt _ _) (byt H "pexec" 8 (by simp [Rx.byteGroups]))
    (fun k hk => bit H "cpx" 7 (by simp [Rx.bitGroups]) k (by omega)) (by omega)
  rw [show val (fun k => NAR_EXEC / 256 ^ k % 256) 8 = NAR_EXEC by decide] at hpx
  have htot := p_sum2 H 8 (by decide) "gas" "pexec" "tot" "cto" 0 0 (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups]) rfl (by omega) (inA H)
  have hgr := p_sum2 H 8 (by decide) "gu" "gross" "tot" "cgr" 0 0 (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups]) rfl (by omega) (inA H)
  have hunu := p_mulbb H (na := 16) (nb := 8) (by decide) (by decide) (by decide) "gp" "gross" "unu" "cun"
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (inA H)
  rw [conv_16_8] at hunu
  have hgpb := p_sum2 H 16 (by decide) "burn" "gpb" "gp" "cgp" 0 0 (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups]) rfl (by omega) (inA H)
  have hsur := p_mulbb H (na := 16) (nb := 8) (by decide) (by decide) (by decide) "gpb" "gb" "sur" "csu"
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (inA H)
  rw [conv_16_8] at hsur
  have hbc := p_mul H (na := 16) (nb := 6) (by decide) (by decide) (by decide)
    (a := Rx.bv "burn") (b := Rx.kb CREATE_ACCOUNT_EXEC) (A := cb tr t r pub "burn")
    (B := fun j => CREATE_ACCOUNT_EXEC / 256 ^ j % 256) "bc" "cbc" (inA H) (fun i _ => rfl) (fun j _ => rfl)
    (byt H "burn" 16 (by simp [Rx.byteGroups])) (fun j _ => kb_lt _ _) (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups])
  rw [conv_16_6, show val (fun j => CREATE_ACCOUNT_EXEC / 256 ^ j % 256) 6 = CREATE_ACCOUNT_EXEC by decide] at hbc
  have hrf := p_sum2 H 16 (by decide) "unu" "sur" "rf" "crf" 0 0 (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups]) rfl (by omega) (inA H)
  have hrfnz := p_nz (g := "rf") (w := 16) "irf" (inL H) (by omega) (byt H "rf" 16 (by simp [Rx.byteGroups]))
  -- burnt amounts, reward
  have htb := p_mulbb H (na := 16) (nb := 8) (by decide) (by decide) (by decide) "burn" "gb" "tb" "ctb"
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (inA H)
  rw [conv_16_8] at htb
  have bvb := byt H "vb" 8 (by simp [Rx.byteGroups])
  have bf3 := byt H "fc3" 8 (by simp [Rx.byteGroups])
  have bcf3 := byt H "cf3" 7 (by simp [Rx.byteGroups])
  have hf3 := lin_val (N := 8) (terms := fun k => K 3 * Rx.c "vb" k) (rr := Rx.bv "fc3") (cy := Rx.bv "cf3")
    (top := 0) (by decide) (inA H) (fun k => 3 * cb tr t r pub "vb" k) (cb tr t r pub "fc3") (cb tr t r pub "cf3") 0
    (fun k _ => by simp only [ize_hmul, ize_K, ize_c]; omega) (fun k _ => rfl) (fun k _ => rfl) rfl
    (fun k hk => by
      have := bvb k hk
      split
      · unfold PP; omega
      · have := bcf3 (k - 1) (by omega); unfold PP; omega)
    (fun k hk => by
      have := bf3 k hk
      split
      · unfold PP; omega
      · have := bcf3 k (by omega); unfold PP; omega)
  rw [val_smul] at hf3
  have bq := byt H "q10" 8 (by simp [Rx.byteGroups])
  have bcq := byt H "cq" 7 (by simp [Rx.byteGroups])
  have hr10 := H.r10
  have hq := lin_val (N := 8) (terms := fun k => K 10 * Rx.c "q10" k + (if k = 0 then Rx.c "r10" else K 0))
    (rr := Rx.bv "fc3") (cy := Rx.bv "cq") (top := 0) (by decide) (inA H)
    (fun k => 10 * cb tr t r pub "q10" k + (if k = 0 then cb tr t r pub "r10" 0 else 0))
    (cb tr t r pub "fc3") (cb tr t r pub "cq") 0
    (fun k _ => by
      by_cases hk0 : k = 0
      · subst hk0; simp only [ize_hadd, ize_hmul, ize_K, ize_c, ite_true]; omega
      · simp only [ize_hadd, ize_hmul, ize_K, ize_c, hk0, ite_false]; omega)
    (fun k _ => rfl) (fun k _ => rfl) rfl
    (fun k hk => by
      have := bq k hk
      by_cases hk0 : k = 0
      · subst hk0; simp only [ite_true]; unfold PP; omega
      · have := bcq (k - 1) (by omega)
        simp only [hk0, ite_false]; unfold PP; omega)
    (fun k hk => by
      have := bf3 k hk
      split
      · unfold PP; omega
      · have := bcq k (by omega); unfold PP; omega)
  rw [val_add, val_smul, val_first _ _ (by decide)] at hq
  have hrew := p_mulbb H (na := 16) (nb := 8) (by decide) (by decide) (by decide) "burn" "q10" "rew" "crw"
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (inA H)
  rw [conv_16_8] at hrew
  have ham := p_sum2 H 16 (by decide) "vbal" "rew" "amt2" "cam" 0 0 (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups]) rfl (by omega) (inA H)
  have htx := p_sum2 H 16 (by decide) "rew" "txb" "tb" "ctx" 0 0 (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups]) rfl (by omega) (inA H)
  -- totals
  have htbo := p_sum2 H 16 (by decide) "tbin" "txb" "tbout" "ctbo" 0 0 (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups]) rfl (by omega) (inA H)
  have hsbo := p_sum2 H 16 (by decide) "sbin" "vsub" "sbout" "csbo" 0 0 (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups]) rfl (by omega) (inA H)
  have hwg := L_sum2 (N := 16) (by decide) (a := Rx.bv "wgin") (b := Rx.bytes 8 (Rx.bv "vb")) (rr := Rx.bv "wgout")
    (cy := Rx.bv "cwg") (top := 0) (inA H) (A := cb tr t r pub "wgin")
    (B := fun k => if k < 8 then cb tr t r pub "vb" k else 0) (R := cb tr t r pub "wgout") (C := cb tr t r pub "cwg")
    (tp := 0) (fun k _ => rfl) (fun k _ => by rw [ize_bytes]; split <;> simp) (fun k _ => rfl) (fun k _ => rfl) rfl
    (byt H "wgin" 16 (by simp [Rx.byteGroups]))
    (fun k _ => by
      split
      · exact bvb k ‹_›
      · omega)
    (byt H "wgout" 16 (by simp [Rx.byteGroups]))
    (fun k hk => bit H "cwg" 15 (by simp [Rx.bitGroups]) k (by omega)) (by omega)
  rw [val_pad _ _ _ (by decide)] at hwg
  have hgo := p_sum2 H 8 (by decide) "gin" "gb" "gout" "cgo" 0 0 (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups]) rfl (by omega) (inA H)
  have hco := p_sum2 H 8 (by decide) "cin" "cu" "cout" "cco" 0 0 (by simp [Rx.byteGroups])
    (by simp [Rx.byteGroups]) (by simp [Rx.byteGroups]) (by simp [Rx.bitGroups]) rfl (by omega) (inA H)
  have bci := byt H "cin" 8 (by simp [Rx.byteGroups])
  have bdg := byt H "dgl" 8 (by simp [Rx.byteGroups])
  have bgl := byt H "glim" 8 (by simp [Rx.byteGroups])
  have hgl := lin_val (N := 8) (terms := fun k => Rx.c "cin" k + Rx.c "dgl" k + (if k = 0 then K 1 else K 0))
    (rr := Rx.bv "glim") (cy := Rx.bv "cgl") (top := 0) (by decide) (inA H)
    (fun k => cb tr t r pub "cin" k + cb tr t r pub "dgl" k + (if k = 0 then 1 else 0))
    (cb tr t r pub "glim") (cb tr t r pub "cgl") 0
    (fun k _ => by
      by_cases hk0 : k = 0
      · subst hk0; simp only [ize_hadd, ize_K, ize_c, ite_true]; omega
      · simp only [ize_hadd, ize_K, ize_c, hk0, ite_false]; omega)
    (fun k _ => rfl) (fun k _ => rfl) rfl
    (fun k hk => by
      have := bci k hk; have := bdg k hk
      by_cases hk0 : k = 0
      · subst hk0; simp only [ite_true]; unfold PP; omega
      · have := bit H "cgl" 7 (by simp [Rx.bitGroups]) (k - 1) (by omega)
        simp only [hk0, ite_false]; unfold PP; omega)
    (fun k hk => by
      have := bgl k hk
      split
      · unfold PP; omega
      · have := bit H "cgl" 7 (by simp [Rx.bitGroups]) k (by omega); unfold PP; omega)
  rw [val_add, val_add, val_first _ _ (by decide)] at hgl
  have hgasnz := p_nz (g := "gas") (w := 8) "igs" (inL H) (by omega) (byt H "gas" 8 (by simp [Rx.byteGroups]))
  -- the size limits
  have hlim1 : ev tr t r pub (Rx.c "lm" + Rx.c "e1" 0 + K 256 * Rx.c "e1" 1 - K MAX_METHOD_NAME) = 0 := inL H
  have hlim2 : ev tr t r pub
      (Rx.c "la" + Rx.c "e2" 0 + K 256 * Rx.c "e2" 1 + K 65536 * Rx.c "e2" 2 - K MAX_ARGS) = 0 := inL H
  have be1 := byt H "e1" 2 (by simp [Rx.byteGroups])
  have be2 := byt H "e2" 3 (by simp [Rx.byteGroups])
  have z1 := ize_eq_zero hlim1
  have z2 := ize_eq_zero hlim2
  simp only [ize_hsub, ize_hadd, ize_hmul, ize_K, ize_c] at z1 z2
  have e10 := be1 0 (by omega); have e11 := be1 1 (by omega)
  have e20 := be2 0 (by omega); have e21 := be2 1 (by omega); have e22 := be2 2 (by omega)
  have q1 := z1 (by unfold PP MAX_METHOD_NAME; omega) (by unfold PP MAX_METHOD_NAME; omega)
  have q2 := z2 (by unfold PP MAX_ARGS; omega) (by unfold PP MAX_ARGS; omega)
  have hlm : cb tr t r pub "lm" 0 ≤ MAX_METHOD_NAME := by unfold MAX_METHOD_NAME at q1 ⊢; omega
  have hla : cb tr t r pub "la" 0 ≤ MAX_ARGS := by unfold MAX_ARGS at q2 ⊢; omega
  -- bounds of every group
  have B8 : ∀ g, (g, 8) ∈ Rx.byteGroups → val (cb tr t r pub g) 8 < 256 ^ 8 := fun g hg => bytes_of H hg
  have B16 : ∀ g, (g, 16) ∈ Rx.byteGroups → val (cb tr t r pub g) 16 < 256 ^ 16 := fun g hg => bytes_of H hg
  -- zero tests
  have hamtv : val (cb tr t r pub "amt") 16 ≠ 256 ^ 16 - 1 := by
    intro h; apply hiam
    have := val_full ba h
    exact sum_zero_of (fun k hk => by rw [this k hk])
  have hrf0 : val (cb tr t r pub "rf") 16 ≠ 0 := by
    intro h; apply hrfnz
    -- a zero value has zero bytes
    have hb := byt H "rf" 16 (by simp [Rx.byteGroups])
    apply sum_zero_of
    intro k hk
    have key : ∀ n, n ≤ 16 → val (cb tr t r pub "rf") n = 0 → ∀ j < n, cb tr t r pub "rf" j = 0 := by
      intro n hn hv j hj
      induction n with
      | zero => omega
      | succ n ih =>
        simp only [val] at hv
        have hp : 0 < 256 ^ n := Nat.pow_pos (by decide)
        have h1 : val (cb tr t r pub "rf") n = 0 := by omega
        have h2 : 256 ^ n * cb tr t r pub "rf" n = 0 := by omega
        rcases Nat.lt_or_ge j n with hj' | hj'
        · exact ih (by omega) h1 hj'
        · have : j = n := by omega
          subst this
          rcases Nat.mul_eq_zero.1 h2 with h3 | h3
          · omega
          · exact h3
    have hv16 : val (cb tr t r pub "rf") 16 = 0 := h
    exact key 16 (Nat.le_refl _) hv16 k hk
  have hgas0 : val (cb tr t r pub "gas") 8 ≠ 0 := by
    intro h; apply hgasnz
    apply sum_zero_of
    intro k hk
    have key : ∀ n, n ≤ 8 → val (cb tr t r pub "gas") n = 0 → ∀ j < n, cb tr t r pub "gas" j = 0 := by
      intro n hn hv j hj
      induction n with
      | zero => omega
      | succ n ih =>
        simp only [val] at hv
        have h1 : val (cb tr t r pub "gas") n = 0 := by omega
        have h2 : 256 ^ n * cb tr t r pub "gas" n = 0 := by omega
        rcases Nat.lt_or_ge j n with hj' | hj'
        · exact ih (by omega) h1 hj'
        · have : j = n := by omega
          subst this
          rcases Nat.mul_eq_zero.1 h2 with h3 | h3
          · have : 0 < 256 ^ j := Nat.pow_pos (by decide)
            omega
          · exact h3
    exact key 8 (Nat.le_refl _) h k hk
  -- assemble
  have bd_gas := bytes_of H (g := "gas") (w := 8) (by simp [Rx.byteGroups])
  have bd_vb := bytes_of H (g := "vb") (w := 8) (by simp [Rx.byteGroups])
  have bd_vu := bytes_of H (g := "vu") (w := 8) (by simp [Rx.byteGroups])
  have bd_vc := bytes_of H (g := "vc") (w := 8) (by simp [Rx.byteGroups])
  have bd_vus := bytes_of H (g := "vus") (w := 8) (by simp [Rx.byteGroups])
  have bd_glim := bytes_of H (g := "glim") (w := 8) (by simp [Rx.byteGroups])
  have bd_gin := bytes_of H (g := "gin") (w := 8) (by simp [Rx.byteGroups])
  have bd_cin := bytes_of H (g := "cin") (w := 8) (by simp [Rx.byteGroups])
  have bd_fcx := bytes_of H (g := "fcx") (w := 8) (by simp [Rx.byteGroups])
  have bd_gb := bytes_of H (g := "gb") (w := 8) (by simp [Rx.byteGroups])
  have bd_gu := bytes_of H (g := "gu") (w := 8) (by simp [Rx.byteGroups])
  have bd_cu := bytes_of H (g := "cu") (w := 8) (by simp [Rx.byteGroups])
  have bd_pexec := bytes_of H (g := "pexec") (w := 8) (by simp [Rx.byteGroups])
  have bd_tot := bytes_of H (g := "tot") (w := 8) (by simp [Rx.byteGroups])
  have bd_fc3 := bytes_of H (g := "fc3") (w := 8) (by simp [Rx.byteGroups])
  have bd_gout := bytes_of H (g := "gout") (w := 8) (by simp [Rx.byteGroups])
  have bd_cout := bytes_of H (g := "cout") (w := 8) (by simp [Rx.byteGroups])
  have bd_s2 := bytes_of H (g := "s2") (w := 8) (by simp [Rx.byteGroups])
  have bd_gross := bytes_of H (g := "gross") (w := 8) (by simp [Rx.byteGroups])
  have bd_dgl := bytes_of H (g := "dgl") (w := 8) (by simp [Rx.byteGroups])
  have bd_gp := bytes_of H (g := "gp") (w := 16) (by simp [Rx.byteGroups])
  have bd_egp := bytes_of H (g := "egp") (w := 16) (by simp [Rx.byteGroups])
  have bd_dep := bytes_of H (g := "dep") (w := 16) (by simp [Rx.byteGroups])
  have bd_amt := bytes_of H (g := "amt") (w := 16) (by simp [Rx.byteGroups])
  have bd_lck := bytes_of H (g := "lck") (w := 16) (by simp [Rx.byteGroups])
  have bd_vbal := bytes_of H (g := "vbal") (w := 16) (by simp [Rx.byteGroups])
  have bd_vsub := bytes_of H (g := "vsub") (w := 16) (by simp [Rx.byteGroups])
  have bd_tbin := bytes_of H (g := "tbin") (w := 16) (by simp [Rx.byteGroups])
  have bd_sbin := bytes_of H (g := "sbin") (w := 16) (by simp [Rx.byteGroups])
  have bd_wgin := bytes_of H (g := "wgin") (w := 16) (by simp [Rx.byteGroups])
  have bd_wgout := bytes_of H (g := "wgout") (w := 16) (by simp [Rx.byteGroups])
  have bd_ad := bytes_of H (g := "ad") (w := 16) (by simp [Rx.byteGroups])
  have bd_req := bytes_of H (g := "req") (w := 16) (by simp [Rx.byteGroups])
  have bd_ak := bytes_of H (g := "ak") (w := 16) (by simp [Rx.byteGroups])
  have bd_s1 := bytes_of H (g := "s1") (w := 16) (by simp [Rx.byteGroups])
  have bd_unu := bytes_of H (g := "unu") (w := 16) (by simp [Rx.byteGroups])
  have bd_sur := bytes_of H (g := "sur") (w := 16) (by simp [Rx.byteGroups])
  have bd_bc := bytes_of H (g := "bc") (w := 16) (by simp [Rx.byteGroups])
  have bd_rf := bytes_of H (g := "rf") (w := 16) (by simp [Rx.byteGroups])
  have bd_tb := bytes_of H (g := "tb") (w := 16) (by simp [Rx.byteGroups])
  have bd_rew := bytes_of H (g := "rew") (w := 16) (by simp [Rx.byteGroups])
  have bd_amt2 := bytes_of H (g := "amt2") (w := 16) (by simp [Rx.byteGroups])
  have bd_tbout := bytes_of H (g := "tbout") (w := 16) (by simp [Rx.byteGroups])
  have bd_sbout := bytes_of H (g := "sbout") (w := 16) (by simp [Rx.byteGroups])
  have bd_gpb := bytes_of H (g := "gpb") (w := 16) (by simp [Rx.byteGroups])
  have bd_txb := bytes_of H (g := "txb") (w := 16) (by simp [Rx.byteGroups])
  unfold gv at *
  simp only [Nat.mul_zero, Nat.add_zero, Nat.reducePow] at *
  have b1v : ev tr t r pub (Rx.c "b1") = cb tr t r pub "b1" 0 := rfl
  have b2v : ev tr t r pub (Rx.c "b2") = cb tr t r pub "b2" 0 := rfl
  rw [b1v, b2v] at hb12
  have hfcx' : val (cb tr t r pub "fcx") 8 = FC_BASE_EXEC + FC_BYTE_EXEC * (cb tr t r pub "lm" 0 + cb tr t r pub "la" 0) := by
    rw [hfcx, L.2.2]
  exact
    { gp_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      egp_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      gas_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      dep_lt' := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      amt_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      lck_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      vb_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      vu_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      vc_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      vbal_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      vus_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      vsub_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      glim_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      gin_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      cin_lt' := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      tbin_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      sbin_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      wgin_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      wgout_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      fcx_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      gb := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      gb_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      gu := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      gu_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      cu := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      cu_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      vb_le := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      dep_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      amt_ne := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      req_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      bal_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      pexec := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      pexec_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      tot := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      tot_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      gross := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      unu_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      gpb := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      sur_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      bc_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      rf := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      rf_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      rf_pos := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      tb_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      fc3_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      q10 := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      rew_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      amt2 := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      amt2_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      txb := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      tbout := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      tbout_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      sbout := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      sbout_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      wgout := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      gout := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      gout_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      cout := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      cout_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      cin_lt := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      gas_ne := by simp only [decode, gv, U64, U128, MAX_METHOD_NAME, MAX_ARGS, Nat.reducePow]; omega,
      lm_le := by simp only [decode]; exact hlm,
      la_le := by simp only [decode]; exact hla,
      fcx := by simp only [decode, gv]; exact hfcx',
      req := by simp only [decode, gv]; rw [← hreq, Nat.mul_comm],
      stake := by
        simp only [decode, gv]
        try unfold gv at hs1 hs2 hak
        rcases hb12 with h0 | h0
        · rw [h0] at hs1; left; (try simp only [Nat.mul_zero, Nat.add_zero] at hs1 hak); omega
        · rw [h0] at hs2; right; try simp only [Nat.mul_zero, Nat.add_zero] at hs2
          have := bytes_of H (g := "s2") (w := 8) (by simp [Rx.byteGroups]); (try unfold gv at this); omega,
      burn := by simp only [decode, gv]; exact hburn,
      unu := by simp only [decode, gv]; exact hunu.symm,
      sur := by simp only [decode, gv]; exact hsur.symm,
      bc := by simp only [decode, gv]; exact hbc.symm,
      tb := by simp only [decode, gv]; exact htb.symm,
      rew := by simp only [decode, gv]; exact hrew.symm }

end M5T1.RxField
