import ZkFormal.NearV3.Assembly.RcptCandidateFB1
-- Source FB2.lean SHA256: 290239adb6f19e9201926489daf6955036bf8a1c45ede0bfe1f34b4a16875875.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.FB1

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.FB2 (v1 `RcptFB2`) — the `BYTES` messages of each receipt field

`fb_X`: the messages of the rows of field `X` are, up to permutation, the
`emitAt` chunks of the view's encodings that the field emits.
-/

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3
open ZkFormal.Near.RcptProof (sumL chain chainC convS convR sumL_congr sumL_lt le256_map_range sumL_add convS_id)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt) {oN o2N rN : Nat}
  (ho : tr.cell tt s o = (oN : Fp)) (ho2 : tr.cell tt s o2 = (o2N : Fp))
  (hrN : tr.cell tt s RcptV3.r = (rN : Fp)) {jN : Nat}
  (hj : ∀ q, s ≤ q → q < s + total h Lp Lv Ls kt → tr.cell tt q j = (jN : Fp))
include hL lay ho ho2 hrN hj

omit hL lay ho ho2 hrN hj in
theorem xrh_val (r0 : Nat) : ∀ k (hk : k < 16),
    ((pubs PH_HEIGHT 8 ++ ks (List.replicate 8 0))[k]'(by simp [pubs, ks]; omega)).eval tr tt r0 pub =
      (((pubBytes pub PH_HEIGHT 8 ++ List.replicate 8 0).getD k 0 : Nat) : Fp) := by
  intro k hk
  by_cases h8 : k < 8
  · rw [List.getElem_append_left (by simp [pubs]; omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [pubBytes]; omega)]
    simp [pubs, pubBytes, List.getElem?_range h8, pubNat, cell_eq_cast, natCast_eq, Fp.ofNat_toNat]
  · have e1 : (pubs PH_HEIGHT 8 ++ ks (List.replicate 8 0))[k]'(by simp [pubs, ks]; omega) = Dsl.k 0 := by
      rw [List.getElem_append_right (by simp [pubs]; omega)]
      simp only [ks, List.getElem_map, List.getElem_replicate]
    have e2 : (pubBytes pub PH_HEIGHT 8 ++ List.replicate 8 0).getD k 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [pubBytes]; omega),
        List.getElem?_replicate]
      split <;> rfl
    rw [e1, e2]; rfl

theorem fb_PK :
    (fieldRows tr tt (s + (46 + Lp + Lv + Ls)) (32 + 32 * kt)).Perm
      (((emitAt (msgId K_RC jN) (oN + (46 + Lp + Lv + Ls)) (colAt tr tt (s + (46 + Lp + Lv + Ls)) (32 + 32 * kt) b)).map Msg.toFp) ++ (if h then (emitAt (K_RF) (o2N + (52 + 2 * Ls)) (colAt tr tt (s + (46 + Lp + Lv + Ls)) (32 + 32 * kt) b)).map Msg.toFp else []) ++ []) := by
  cases h
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sPK) (off := (46 + Lp + Lv + Ls)) (L := (32 + 32 * kt)) (by simp [plan, hN])
    have hX : (sPK, [(RC, at' [c o, k 46, c RcptV3.Lp, c RcptV3.Lv, c RcptV3.Ls], bE, k 1), (RF, at' [c o2, k 52, smul 2 (c RcptV3.Ls)], bE, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (46 + Lp + Lv + Ls)) (colAt tr tt (s + (46 + Lp + Lv + Ls)) (32 + 32 * kt) b)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk),
      fld_chunk_off hL hH F hX (e := 1) (by decide) rfl (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl),
      fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sPK) (off := (46 + Lp + Lv + Ls)) (L := (32 + 32 * kt)) (by simp [plan, hN])
    have hX : (sPK, [(RC, at' [c o, k 46, c RcptV3.Lp, c RcptV3.Lv, c RcptV3.Ls], bE, k 1), (RF, at' [c o2, k 52, smul 2 (c RcptV3.Ls)], bE, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (46 + Lp + Lv + Ls)) (colAt tr tt (s + (46 + Lp + Lv + Ls)) (32 + 32 * kt) b)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk),
      fld_chunk hL hH F hX (e := 1) (by decide) rfl (K_RF) (o2N + (52 + 2 * Ls)) (colAt tr tt (s + (46 + Lp + Lv + Ls)) (32 + 32 * kt) b)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl) (fun _ _ => rfl)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk),
      fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]

theorem fb_GP :
    (fieldRows tr tt (s + (78 + Vt Lp Lv Ls kt)) 16).Perm
      (((emitAt (msgId K_RC jN) (oN + (78 + Vt Lp Lv Ls kt)) (colAt tr tt (s + (78 + Vt Lp Lv Ls kt)) 16 b)).map Msg.toFp) ++ ((emitAt (msgId K_PEO rN) (12 + 32 * hN h) (colAt tr tt (s + (78 + Vt Lp Lv Ls kt)) 16 burnt)).map Msg.toFp) ++ (if h then (emitAt (K_RF) (o2N + (113 + 2 * Ls + 32 * kt)) (colAt tr tt (s + (78 + Vt Lp Lv Ls kt)) 16 ramt)).map Msg.toFp else [])) := by
  cases h
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sGP) (off := (78 + Vt Lp Lv Ls kt)) (L := 16) (by simp [plan, hN])
    have hX : (sGP, [(RC, at' [c o, k 78, varE], bE, k 1), (PEO, at' [k 12, smul 32 (c hr)], c burnt, k 1), (RF, at' [c o2, k 113, smul 2 (c RcptV3.Ls), smul 32 (c RcptV3.kt)], c ramt, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (78 + Vt Lp Lv Ls kt)) (colAt tr tt (s + (78 + Vt Lp Lv Ls kt)) 16 b)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk),
      fld_chunk hL hH F hX (e := 1) (by decide) rfl (msgId K_PEO rN) (12 + 32 * hN false) (colAt tr tt (s + (78 + Vt Lp Lv Ls kt)) 16 burnt)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [PEO, eval_mid, eval_c, eval_k, eval_smul, V.r, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk),
      fld_chunk_off hL hH F hX (e := 2) (by decide) rfl (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl)]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sGP) (off := (78 + Vt Lp Lv Ls kt)) (L := 16) (by simp [plan, hN])
    have hX : (sGP, [(RC, at' [c o, k 78, varE], bE, k 1), (PEO, at' [k 12, smul 32 (c hr)], c burnt, k 1), (RF, at' [c o2, k 113, smul 2 (c RcptV3.Ls), smul 32 (c RcptV3.kt)], c ramt, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (78 + Vt Lp Lv Ls kt)) (colAt tr tt (s + (78 + Vt Lp Lv Ls kt)) 16 b)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk),
      fld_chunk hL hH F hX (e := 1) (by decide) rfl (msgId K_PEO rN) (12 + 32 * hN true) (colAt tr tt (s + (78 + Vt Lp Lv Ls kt)) 16 burnt)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [PEO, eval_mid, eval_c, eval_k, eval_smul, V.r, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk),
      fld_chunk hL hH F hX (e := 2) (by decide) rfl (K_RF) (o2N + (113 + 2 * Ls + 32 * kt)) (colAt tr tt (s + (78 + Vt Lp Lv Ls kt)) 16 ramt)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl) (fun _ _ => rfl)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk)]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]

theorem fb_TL :
    (fieldRows tr tt (s + (94 + Vt Lp Lv Ls kt)) 13).Perm
      (((emitAt (msgId K_RC jN) (oN + (94 + Vt Lp Lv Ls kt)) (tailN)).map Msg.toFp) ++ (if h then (emitAt (K_RF) (o2N + (100 + 2 * Ls + 32 * kt)) (tailN)).map Msg.toFp else []) ++ []) := by
  cases h
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sTL) (off := (94 + Vt Lp Lv Ls kt)) (L := 13) (by simp [plan, hN])
    have hX : (sTL, [(RC, at' [c o, k 94, varE], bE, k 1), (RF, at' [c o2, k 100, smul 2 (c RcptV3.Ls), smul 32 (c RcptV3.kt)], bE, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (94 + Vt Lp Lv Ls kt)) (tailN)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (reg_val hL hH F (by decide) (by decide) (l := ks [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3]) (by simp [loads, ks]) (by simp [ks, G_LE]) (by omega) _
          (fun k hk => ks_get _ k (by simp [G_LE]; omega) _)),
      fld_chunk_off hL hH F hX (e := 1) (by decide) rfl (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl),
      fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sTL) (off := (94 + Vt Lp Lv Ls kt)) (L := 13) (by simp [plan, hN])
    have hX : (sTL, [(RC, at' [c o, k 94, varE], bE, k 1), (RF, at' [c o2, k 100, smul 2 (c RcptV3.Ls), smul 32 (c RcptV3.kt)], bE, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (94 + Vt Lp Lv Ls kt)) (tailN)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (reg_val hL hH F (by decide) (by decide) (l := ks [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3]) (by simp [loads, ks]) (by simp [ks, G_LE]) (by omega) _
          (fun k hk => ks_get _ k (by simp [G_LE]; omega) _)),
      fld_chunk hL hH F hX (e := 1) (by decide) rfl (K_RF) (o2N + (100 + 2 * Ls + 32 * kt)) (tailN)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl) (fun _ _ => rfl)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (reg_val hL hH F (by decide) (by decide) (l := ks [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 3]) (by simp [loads, ks]) (by simp [ks, G_LE]) (by omega) _
          (fun k hk => ks_get _ k (by simp [G_LE]; omega) _)),
      fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]

theorem fb_DEP :
    (fieldRows tr tt (s + (107 + Vt Lp Lv Ls kt)) 16).Perm
      (((emitAt (msgId K_RC jN) (oN + (107 + Vt Lp Lv Ls kt)) (colAt tr tt (s + (107 + Vt Lp Lv Ls kt)) 16 b)).map Msg.toFp) ++ [] ++ []) := by
  obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sDEP) (off := (107 + Vt Lp Lv Ls kt)) (L := 16) (by simp [plan])
  have hX : (sDEP, [(RC, at' [c o, k 107, varE], bE, k 1)]) ∈ emits := by simp [emits]
  refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
  rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (107 + Vt Lp Lv Ls kt)) (colAt tr tt (s + (107 + Vt Lp Lv Ls kt)) 16 b)
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId]
        try simp only [Vt]
        grind)
      (fun k hk => col_val _ _ _ _ hk),
    fld_chunk_none hL hH F hX (e := 1) (by decide) rfl,
    fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]

theorem fb_XP0 :
    (fieldRows tr tt (s + (123 + Vt Lp Lv Ls kt)) 4).Perm
      (((emitAt (msgId K_PEO rN) (0) (u32r (hN h))).map Msg.toFp) ++ [] ++ []) := by
  obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sXP0) (off := (123 + Vt Lp Lv Ls kt)) (L := 4) (by simp [plan])
  have hX : (sXP0, [(PEO, ix, bE, k 1)]) ∈ emits := by simp [emits]
  refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
  rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_PEO rN) (0) (u32r (hN h))
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [PEO, eval_mid, eval_c, eval_k, eval_smul, V.r, msgId]; grind)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId]
        try simp only [Vt]
        grind)
      (reg_val hL hH F (by decide) (by decide) (l := [c hr, k 0, k 0, k 0]) (by simp [loads]) (by simp) (by omega) _
        (fun k hk => by
          have V0 := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) F.fld.pos; simp only [Nat.add_zero] at V0
          rcases k with _ | _ | _ | _ | k <;> simp [u32r, V0.Lp, V0.Lv, V0.Ls, V0.kt, V0.hr] <;> first | rfl | omega)),
    fld_chunk_none hL hH F hX (e := 1) (by decide) rfl,
    fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]

theorem fb_XRI (hh : h = true) :
    (fieldRows tr tt (s + (127 + Vt Lp Lv Ls kt)) 32).Perm
      (((emitAt (msgId K_PEO rN) (4) (colAt tr tt (s + (127 + Vt Lp Lv Ls kt)) 32 b)).map Msg.toFp) ++ ((emitAt (K_RF) (o2N + (14 + Ls)) (colAt tr tt (s + (127 + Vt Lp Lv Ls kt)) 32 b)).map Msg.toFp) ++ []) := by
  subst hh
  obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sXRI) (off := (127 + Vt Lp Lv Ls kt)) (L := 32) (by simp [plan, hN])
  have hX : (sXRI, [(PEO, at' [k 4], bE, k 1), (RF, at' [c o2, k 14, c RcptV3.Ls], bE, k 1)]) ∈ emits := by simp [emits]
  refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
  rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_PEO rN) (4) (colAt tr tt (s + (127 + Vt Lp Lv Ls kt)) 32 b)
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [PEO, eval_mid, eval_c, eval_k, eval_smul, V.r, msgId]; grind)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
        try simp only [Vt]
        grind)
      (fun k hk => col_val _ _ _ _ hk),
    fld_chunk hL hH F hX (e := 1) (by decide) rfl (K_RF) (o2N + (14 + Ls)) (colAt tr tt (s + (127 + Vt Lp Lv Ls kt)) 32 b)
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
        try simp only [Vt]
        grind)
      (fun k hk => col_val _ _ _ _ hk),
    fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]

theorem fb_XG :
    (fieldRows tr tt (s + (127 + 32 * hN h + Vt Lp Lv Ls kt)) 8).Perm
      (((emitAt (msgId K_PEO rN) (4 + 32 * hN h) (G_LEn)).map Msg.toFp) ++ [] ++ []) := by
  obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sXG) (off := (127 + 32 * hN h + Vt Lp Lv Ls kt)) (L := 8) (by simp [plan])
  have hX : (sXG, [(PEO, at' [k 4, smul 32 (c hr)], bE, k 1)]) ∈ emits := by simp [emits]
  refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
  rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_PEO rN) (4 + 32 * hN h) (G_LEn)
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [PEO, eval_mid, eval_c, eval_k, eval_smul, V.r, msgId]; grind)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId]
        try simp only [Vt]
        grind)
      (reg_val hL hH F (by decide) (by decide) (l := ks G_LE) (by simp [loads, ks]) (by simp [ks, G_LE]) (by omega) _
        (fun k hk => ks_get _ k (by simp [G_LE]; omega) _)),
    fld_chunk_none hL hH F hX (e := 1) (by decide) rfl,
    fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]

theorem fb_XST :
    (fieldRows tr tt (s + (135 + 32 * hN h + Vt Lp Lv Ls kt)) 5).Perm
      (((emitAt (msgId K_PEO rN) (32 + 32 * hN h + Lv) ([2, 0, 0, 0, 0])).map Msg.toFp) ++ [] ++ []) := by
  obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sXST) (off := (135 + 32 * hN h + Vt Lp Lv Ls kt)) (L := 5) (by simp [plan])
  have hX : (sXST, [(PEO, at' [k 32, smul 32 (c hr), c RcptV3.Lv], bE, k 1)]) ∈ emits := by simp [emits]
  refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
  rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_PEO rN) (32 + 32 * hN h + Lv) ([2, 0, 0, 0, 0])
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [PEO, eval_mid, eval_c, eval_k, eval_smul, V.r, msgId]; grind)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId]
        try simp only [Vt]
        grind)
      (reg_val hL hH F (by decide) (by decide) (l := ks [2, 0, 0, 0, 0]) (by simp [loads, ks]) (by simp [ks, G_LE]) (by omega) _
        (fun k hk => ks_get _ k (by simp [G_LE]; omega) _)),
    fld_chunk_none hL hH F hX (e := 1) (by decide) rfl,
    fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]

theorem fb_XL0 :
    (fieldRows tr tt (s + (140 + 32 * hN h + Vt Lp Lv Ls kt)) 4).Perm
      (((emitAt (msgId K_LEAF rN) (0) ([2, 0, 0, 0])).map Msg.toFp) ++ [] ++ []) := by
  obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sXL0) (off := (140 + 32 * hN h + Vt Lp Lv Ls kt)) (L := 4) (by simp [plan])
  have hX : (sXL0, [(LEAF, ix, bE, k 1)]) ∈ emits := by simp [emits]
  refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
  rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_LEAF rN) (0) ([2, 0, 0, 0])
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [LEAF, eval_mid, eval_c, eval_k, eval_smul, V.r, msgId]; grind)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId]
        try simp only [Vt]
        grind)
      (reg_val hL hH F (by decide) (by decide) (l := ks [2, 0, 0, 0]) (by simp [loads, ks]) (by simp [ks, G_LE]) (by omega) _
        (fun k hk => ks_get _ k (by simp [G_LE]; omega) _)),
    fld_chunk_none hL hH F hX (e := 1) (by decide) rfl,
    fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]

theorem fb_XLH :
    (fieldRows tr tt (s + (144 + 32 * hN h + Vt Lp Lv Ls kt)) 32).Perm
      (((emitAt (msgId K_LEAF rN) (36) (colAt tr tt (s + (144 + 32 * hN h + Vt Lp Lv Ls kt)) 32 b)).map Msg.toFp) ++ [] ++ []) := by
  obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sXLH) (off := (144 + 32 * hN h + Vt Lp Lv Ls kt)) (L := 32) (by simp [plan])
  have hX : (sXLH, [(LEAF, at' [k 36], bE, k 1)]) ∈ emits := by simp [emits]
  refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
  rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_LEAF rN) (36) (colAt tr tt (s + (144 + 32 * hN h + Vt Lp Lv Ls kt)) 32 b)
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [LEAF, eval_mid, eval_c, eval_k, eval_smul, V.r, msgId]; grind)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId]
        try simp only [Vt]
        grind)
      (fun k hk => col_val _ _ _ _ hk),
    fld_chunk_none hL hH F hX (e := 1) (by decide) rfl,
    fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]

theorem fb_XRH (hh : h = true) :
    (fieldRows tr tt (s + (208 + Vt Lp Lv Ls kt)) 16).Perm
      (((emitAt (msgId K_RID rN) (32) (pubBytes pub PH_HEIGHT 8 ++ List.replicate 8 0)).map Msg.toFp) ++ [] ++ []) := by
  subst hh
  obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sXRH) (off := (208 + Vt Lp Lv Ls kt)) (L := 16) (by simp [plan, hN])
  have hX : (sXRH, [(RIDm, at' [k 32], bE, k 1)]) ∈ emits := by simp [emits]
  refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
  rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RID rN) (32) (pubBytes pub PH_HEIGHT 8 ++ List.replicate 8 0)
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RIDm, eval_mid, eval_c, eval_k, eval_smul, V.r, msgId]; grind)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
        try simp only [Vt]
        grind)
      (reg_val hL hH F (by decide) (by decide) (l := pubs PH_HEIGHT 8 ++ ks (List.replicate 8 0)) (by simp [loads]) (by simp [pubs, ks]) (by omega) _ (xrh_val _)),
    fld_chunk_none hL hH F hX (e := 1) (by decide) rfl,
    fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]

theorem fb_XRF (hh : h = true) :
    (fieldRows tr tt (s + (224 + Vt Lp Lv Ls kt)) 10).Perm
      (((emitAt (K_RF) (o2N) ([6, 0, 0, 0] ++ systemN)).map Msg.toFp) ++ [] ++ []) := by
  subst hh
  obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sXRF) (off := (224 + Vt Lp Lv Ls kt)) (L := 10) (by simp [plan, hN])
  have hX : (sXRF, [(RF, at' [c o2], bE, k 1)]) ∈ emits := by simp [emits]
  refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
  rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (K_RF) (o2N) ([6, 0, 0, 0] ++ systemN)
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
        try simp only [Vt]
        grind)
      (reg_val hL hH F (by decide) (by decide) (l := ks [6, 0, 0, 0, 115, 121, 115, 116, 101, 109]) (by simp [loads, ks]) (by simp [ks, G_LE]) (by omega) _
        (fun k hk => ks_get _ k (by simp [G_LE]; omega) _)),
    fld_chunk_none hL hH F hX (e := 1) (by decide) rfl,
    fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]

theorem fb_XRZ (hh : h = true) :
    (fieldRows tr tt (s + (234 + Vt Lp Lv Ls kt)) 16).Perm
      (((emitAt (K_RF) (o2N + (84 + 2 * Ls + 32 * kt)) (List.replicate 16 0)).map Msg.toFp) ++ [] ++ []) := by
  subst hh
  obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sXRZ) (off := (234 + Vt Lp Lv Ls kt)) (L := 16) (by simp [plan, hN])
  have hX : (sXRZ, [(RF, at' [c o2, k 84, smul 2 (c RcptV3.Ls), smul 32 (c RcptV3.kt)], bE, k 1)]) ∈ emits := by simp [emits]
  refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
  rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (K_RF) (o2N + (84 + 2 * Ls + 32 * kt)) (List.replicate 16 0)
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
        try simp only [Vt]
        grind)
      (reg_val hL hH F (by decide) (by decide) (l := ks (List.replicate 16 0)) (by simp [loads, ks]) (by simp [ks, G_LE]) (by omega) _
        (fun k hk => ks_get _ k (by simp [G_LE]; omega) _)),
    fld_chunk_none hL hH F hX (e := 1) (by decide) rfl,
    fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]


end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
