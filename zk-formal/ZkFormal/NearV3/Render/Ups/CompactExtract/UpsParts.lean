import ZkFormal.NearV3.Render.Ups.CompactExtract.NlfBytes
import ZkFormal.NearV3.Render.Ups.CompactExtract.SpbBytes
import ZkFormal.NearV3.Extract.Ups.UpsParts
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
  {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- **`RBI`** without the `si ≤ 1` hypothesis (`rbiSi`). -/
theorem rbiBytes' (k : Nat) (hk : k < ps.length) (hkd : kd k = 5) (val : NearSpec.Bytes)
    (Pb : Nat → List Nat) (bv : Option NearSpec.Slot) (cs : NearSpec.Kids) (m : Nat)
    (hR : UpbReads s Pb)
    (hsrc : Pb (s.row ps[k].1 sN) = (nodeEnc (.branch bv cs m)).map UInt8.toNat)
    (hsl : (nodeEnc (.branch bv cs m)).length < 2 ^ 22)
    (hbv : ∀ sl, bv = some sl → sl.valueRef.length = 36) (hm : m < 2 ^ 64)
    (hkl : UpsSpec.kidsLen cs = 16) (hslot : UpsSpec.kidAt cs (UpsSpec.yOf si) = none)
    (hlen : val.length = s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2)
    (hLb : s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256)
    (hdN : ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) k →
      s.row i dL = 50 → regN (s.row i) = (UpsSpec.qNLF si val).hashOf.map UInt8.toNat)
    (hbyte : ∀ d, d < ps[k].2 → s.row (ps[k].1 + d) b < 256) :
    rowsB s ps[k].1 ps[k].2 = (nodeEnc (UpsSpec.qRBI bv cs m si val)).map UInt8.toNat ∧
      limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 = (UpsSpec.qRBI bv cs m si val).memD :=
  ups_rbiBytes hw hs hL hP k hk hkd val (rbiSi hw hs hL hP k hk hkd) Pb bv cs m hR hsrc hsl hbv hm hkl hslot hlen hLb
    hdN hbyte

/-- Plan facts of part `k`: below an `RBI` / a split branch with a new leaf is the new leaf; a
receiving part is not the first. -/
theorem partPlan (k : Nat) (hk : k < ps.length) :
    ((kd k = 5 ∨ (kd k = 10 ∧ spYN ci = 1)) → 1 ≤ k ∧ kd (k - 1) = 8) ∧
    (recvK ci (kd k) → 1 ≤ k) ∧ (kd k = 9 → 1 ≤ ti) := by
  have i1 := hP.ix.1; have i2 := hP.ix.2.1
  rcases Nat.lt_or_ge k (nTof ci ti) with hT | hT
  · have h4 : k < 4 := by have := nTof_le ci i1 ti i2; omega
    obtain ⟨hTk, hk1, hk2, -⟩ := hP.term k hk hT
    have hkl : kd k < 12 := (hP.part k hk).1
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have e : (termPlan (UCase.all.getD ci .LP) ti).getD k .RDB = .RBI ∨
          ((termPlan (UCase.all.getD ci .LP) ti).getD k .RDB = .SPB ∧ spYN ci = 1) := by
        rcases h with h | ⟨h, h'⟩
        · left; rw [← hTk, h]; rfl
        · right; exact ⟨by rw [← hTk, h]; rfl, h'⟩
      obtain ⟨hk1', hN⟩ := termNLF ci i1 ti i2 k h4 e
      refine ⟨hk1', ?_⟩
      have hT' := (hP.term (k - 1) (by omega) (by omega)).1
      rw [hN] at hT'
      exact kdNLF _ (hP.part (k - 1) (by omega)).1 hT'
    · rcases h with h | h | h | h | ⟨h, h'⟩
      · omega
      · omega
      · exact (termWEX ci i1 ti i2 k h4 (by rw [← hTk, h]; rfl)).1
      · omega
      · exact termSPB ci i1 ti i2 k h4 (by rw [← hTk, h]; rfl) h'
    · exact (termWEX ci i1 ti i2 k h4 (by rw [← hTk, h]; rfl)).2
  · have hU := (hP.upper k hk hT).1
    have := nTof_pos' ci i1 ti i2
    refine ⟨fun h => by omega, fun _ => by omega, fun h => by omega⟩

set_option maxHeartbeats 4000000 in
/-- **Part `k`** emits `nodeEnc (upsQ … k)`, and (unless it is the new leaf) its `MEMD` limbs `rx` are
the node's exact `memory_usage`. -/
theorem ups_part {Pb : Nat → List Nat} {src : Nat → NearSpec.PTrie} {val : NearSpec.Bytes}
    (X0 : UpsExt0 s ps ci ti si kd sdx Pb src val) (k : Nat) (hk : k < ps.length)
    (X : UpsExtK s ps ci ti si kd sdx src val k hk) :
      rowsB s ps[k].1 ps[k].2 = (nodeEnc (upsQ ci si ti (s.row 0 tX) val kd sdx src k)).map UInt8.toNat ∧
      (kd k ≠ 8 → limbs (fun i => s.row (ps[k].1 + ps[k].2 - 8 + i) rx) 8 =
        (upsQ ci si ti (s.row 0 tX) val kd sdx src k).memD) := by
  have hkl : kd k < 12 := (hP.part k hk).1
  have i4 := hP.ix.2.2.2
  obtain ⟨hNLF, hRecv, hWti⟩ := partPlan hw hs hL hP k hk
  obtain ⟨hsl, o0, o1, o2, o3, o4, o5, o6, o7, o10, o11⟩ := X0.srcOk k hk
  have hsrc := X0.srcEnc k hk
  have hR := X0.reads
  have hRd : ∀ i, i < s.rows.length → s.row i rd = 1 → s.row i rb = (Pb (s.row i sN)).getD (s.row i spos) 0 :=
    fun i hi hrd => (hR i hi hrd).1
  -- `upsQ k` through `qPart`, with the part below and part 0
  have hQj := upsQ_eq ci si ti (s.row 0 tX) val kd sdx src
  have hQ : ∀ (h1 : 1 ≤ k), upsQ ci si ti (s.row 0 tX) val kd sdx src k =
      qPart ci si ti (sdx k) (s.row 0 tX) val (kd k) (src k) (upsQ ci si ti (s.row 0 tX) val kd sdx src (k - 1))
        (upsQ ci si ti (s.row 0 tX) val kd sdx src 0) (src (k - 1)).memD := by
    intro h1; rw [hQj k, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hQ0 := hQj k
  -- the new leaf below (`RBI`, split branch with a new leaf)
  have hdN : (kd k = 5 ∨ (kd k = 10 ∧ spYN ci = 1)) → ∀ i, i < s.rows.length → s.row i gD = 1 →
      s.row i dI = upsIdN (s.row 0 tau) k → s.row i dL = 50 →
      regN (s.row i) = (UpsSpec.qNLF si val).hashOf.map UInt8.toNat := by
    intro h i hi hg hI hL'
    obtain ⟨h1, h8⟩ := hNLF h
    have e : upsQ ci si ti (s.row 0 tX) val kd sdx src (k - 1) = UpsSpec.qNLF si val := by
      rw [hQj (k - 1), h8]; simp only [qPart]
    have := X.dig i hi hg (k - 1) (by omega) (by rw [hI, Nat.sub_add_cancel h1])
      (by rw [hL', e, qNLF_len si val i4])
    rwa [e] at this
  -- the part below for receiving parts
  have hdC : recvK ci (kd k) → ∀ i, i < s.rows.length → s.row i gD = 1 →
      s.row i dI = upsIdN (s.row 0 tau) (childK (kd k) k + 1) → s.row i dL = s.row ps[k].1 UpsV3.clen →
      regN (s.row i) = (upsQ ci si ti (s.row 0 tX) val kd sdx src (childK (kd k) k)).hashOf.map UInt8.toNat := by
    intro h i hi hg hI hL'
    have h1 := hRecv h
    exact X.dig i hi hg _ (by unfold childK; split <;> omega) hI (by rw [hL', X.clen h])
  rcases (show kd k = 0 ∨ kd k = 1 ∨ kd k = 2 ∨ kd k = 3 ∨ kd k = 4 ∨ kd k = 5 ∨ kd k = 6 ∨ kd k = 7 ∨
      kd k = 8 ∨ kd k = 9 ∨ kd k = 10 ∨ kd k = 11 by omega) with
    h | h | h | h | h | h | h | h | h | h | h | h
  · -- `RDB`
    have hr : recvK ci (kd k) := Or.inl h
    have h1 := hRecv hr
    obtain ⟨bv, cs, m, c, hP', hbv, hm, hkl', hsl', hc32⟩ := o0 h
    have hd := hdC hr
    simp only [childK, h, show ¬ ((0 : Nat) = 10) by omega, ite_false, Nat.sub_add_cancel h1] at hd
    rw [hQ h1, h, hP']
    simp only [qPart]
    rw [hP'] at hsrc
    exact andImp <| ups_rdbBytes hw hs hL hP k hk h Pb bv cs c _ m _ hR hsrc hbv hm hkl' hsl' hc32 hd
      (fun i hi => X.memB hr i hi)
      (by have := (X.memV hr).1; simp only [childK, h, show ¬ ((0 : Nat) = 10) by omega, ite_false] at this; exact this)
      (by have := (X.memV hr).2; simp only [childK, h, show ¬ ((0 : Nat) = 10) by omega, ite_false] at this; exact this)
      (X.bytes)
  · -- `RDE`
    have hr : recvK ci (kd k) := Or.inr (Or.inl h)
    have h1 := hRecv hr
    obtain ⟨key, c, m, hP', hc32, hm⟩ := o1 h
    have hd := hdC hr
    simp only [childK, h, show ¬ ((1 : Nat) = 10) by omega, ite_false, Nat.sub_add_cancel h1] at hd
    rw [hQ h1, h, hP']
    simp only [qPart]
    rw [hP'] at hsrc hsl
    exact andImp <| ups_rdeBytes hw hs hL hP k hk h Pb key c _ m _ hRd hsrc (by omega) hc32 hm hd
      (fun i hi => X.memB hr i hi)
      (by have := (X.memV hr).1; simp only [childK, h, show ¬ ((1 : Nat) = 10) by omega, ite_false] at this; exact this)
      (by have := (X.memV hr).2; simp only [childK, h, show ¬ ((1 : Nat) = 10) by omega, ite_false] at this; exact this)
      (X.bytes)
  · -- `RLP`
    obtain ⟨key, sl, m, hP'⟩ := o2 h
    rw [hQ0, h, hP']
    simp only [qPart]
    rw [hP'] at hsrc hsl
    exact andImp <| ups_rlpBytes hw hs hL hP k hk h val Pb key sl m X0.vlen X0.digV hRd hsrc (by omega) (X.bytes)
  · -- `RBR`
    obtain ⟨sl, cs, m, hP', h36, hsl32, hm⟩ := o3 h
    rw [hQ0, h, hP']
    simp only [qPart]
    rw [hP'] at hsrc
    exact andImp <| ups_rbrBytes hw hs hL hP k hk h val Pb sl cs m X0.vlen X0.digV hR hsrc h36 hsl32 hm (X.bytes)
  · -- `RBV`
    obtain ⟨cs, m, hP', hm⟩ := o4 h
    rw [hQ0, h, hP']
    simp only [qPart]
    rw [hP'] at hsrc
    exact andImp <| ups_rbvBytes hw hs hL hP k hk h val Pb cs m X0.vlen X0.digV hR hsrc hm (X.bytes)
  · -- `RBI`
    obtain ⟨bv, cs, m, hP', hbv, hm, hkl', hslot⟩ := o5 h
    rw [hQ0, h, hP']
    simp only [qPart]
    rw [hP'] at hsrc hsl
    exact andImp <| rbiBytes' hw hs hL hP k hk h val Pb bv cs m hR hsrc hsl hbv hm hkl' hslot X0.vlen X0.vbytes
      (hdN (Or.inl h)) (X.bytes)
  · -- `MVL`
    obtain ⟨key, sl, m, hP', hkey, hI, hkl', h36, hsl32⟩ := o6 h
    rw [hQ0, h, hP']
    simp only [qPart]
    rw [hP'] at hsrc hsl
    exact andImp <| ups_mvlBytes hw hs hL hP k hk h Pb key sl m hR hsrc hsl hkey hI hkl' h36 hsl32 (X.bytes)
  · -- `MVE`
    obtain ⟨key, c, m, hP', hkey, hI, hkl', hc32, hm⟩ := o7 h
    rw [hQ0, h, hP']
    simp only [qPart]
    rw [hP'] at hsrc hsl
    exact andImp <| ups_mveBytes hw hs hL hP k hk h Pb key c m hR hsrc hsl hkey hI hkl' hc32 hm (X.bytes)
  · -- `NLF`
    rw [hQ0, h]
    simp only [qPart]
    exact ⟨ups_nlfBytes hw hs hL hP k hk h val X0.vlen X0.digV (X.bytes), fun h' => absurd rfl h'⟩
  · -- `WEX`
    have hr : recvK ci (kd k) := Or.inr (Or.inr (Or.inl h))
    have h1 := hRecv hr
    have hd := hdC hr
    simp only [childK, h, show ¬ ((9 : Nat) = 10) by omega, ite_false, Nat.sub_add_cancel h1] at hd
    rw [hQ h1, h]
    simp only [qPart]
    exact andImp <| ups_wexBytes hw hs hL hP k hk h _ (hWti h) X0.tiLe hd
      (fun i hi => (X.memB hr i hi).1)
      (by have := (X.memV hr).1; simp only [childK, h, show ¬ ((9 : Nat) = 10) by omega, ite_false] at this; exact this)
      (X.bytes)
  · -- `SPB`
    obtain ⟨oL, oE⟩ := o10 h
    have e : upsQ ci si ti (s.row 0 tX) val kd sdx src k =
        UpsSpec.qSPB ci (src k) (if k = 0 then .hash [] else upsQ ci si ti (s.row 0 tX) val kd sdx src 0)
          (s.row 0 tX) si val := by
      rw [hQ0, h]; simp only [qPart]
    rw [e]
    exact andImp <| ups_spbBytes hw hs hL hP k hk h val Pb hR (src k) _ hsrc hsl oL oE
      (fun hr i hi hg hI hL' => by
        have hr' : recvK ci (kd k) := Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hr⟩)))
        have := hdC hr' i hi hg (by simp only [childK, h, ite_true]; exact hI) hL'
        rw [if_neg (show ¬ k = 0 by have := hRecv hr'; omega)]
        simpa only [childK, h, ite_true] using this)
      (fun hr i hi => (X.memB (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hr⟩)))) i hi).1)
      (fun hr => by
        have := (X.memV (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hr⟩))))).1
        rw [if_neg (show ¬ k = 0 by have := hRecv (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hr⟩)))); omega)]
        simpa only [childK, h, ite_true] using this)
      X0.vlen X0.vbytes X0.digV (fun hy => hdN (Or.inr ⟨h, hy⟩)) X0.xy (X.bytes)
  · -- `PT`
    have hr : recvK ci (kd k) := Or.inr (Or.inr (Or.inr (Or.inl h)))
    have h1 := hRecv hr
    obtain ⟨c, m, hP', hc32, hm⟩ := o11 h
    have hd := hdC hr
    simp only [childK, h, show ¬ ((11 : Nat) = 10) by omega, ite_false, Nat.sub_add_cancel h1] at hd
    rw [hQ h1, h, hP']
    simp only [qPart]
    rw [hP'] at hsrc hsl
    exact andImp <| ups_ptBytes hw hs hL hP k hk h Pb c _ m _ hRd hsrc (by omega) hc32 hm hd
      (fun i hi => X.memB hr i hi)
      (by have := (X.memV hr).1; simp only [childK, h, show ¬ ((11 : Nat) = 10) by omega, ite_false] at this; exact this)
      (by have := (X.memV hr).2; simp only [childK, h, show ¬ ((11 : Nat) = 10) by omega, ite_false] at this; exact this)
      (X.bytes)

end

end ZkFormal.NearV3.Render.UpsRelay.Extract
