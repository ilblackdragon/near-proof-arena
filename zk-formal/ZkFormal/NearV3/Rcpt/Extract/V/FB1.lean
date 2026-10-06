import ZkFormal.NearV3.Rcpt.Extract.V.Chunks

/-!
# ZkFormal.NearV3.Rcpt.Extract.V.FB1 (v1 `RcptFB1`) — the `BYTES` messages of each receipt field

`fb_X`: the messages of the rows of field `X` are, up to permutation, the
`emitAt` chunks of the view's encodings that the field emits.
-/

namespace ZkFormal.NearV3.RcptV3Proof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.RcptV3
open ZkFormal.Near.Rcpt (bitsX bitsXn pubs ks leE G_LE S_LE conv ovf SS hiE loE sepE sepN hexE hexN sq lb' DE DEn pE surE aftE)
open ZkFormal.Near.RcptProof (sumL chain chainC convS convR sumL_congr sumL_lt le256_map_range sumL_add convS_id)

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- `BYTES` messages of the rows `r0 … r0+L−1` (row order). -/
def fieldRows (tr : Trace Fp) (tt r0 L : Nat) : List (List Fp) :=
  (List.range' r0 L).flatMap fun q => (List.range 3).flatMap (slotT tr tt q)

variable (hL : TableLocal RcptV3.table tr tt pub)
variable {s : Nat} {h : Bool} {Lp Lv Ls kt : Nat} (lay : Layout tr tt s h Lp Lv Ls kt) {oN o2N rN : Nat}
  (ho : tr.cell tt s o = (oN : Fp)) (ho2 : tr.cell tt s o2 = (o2N : Fp))
  (hrN : tr.cell tt s RcptV3.r = (rN : Fp)) {jN : Nat}
  (hj : ∀ q, s ≤ q → q < s + total h Lp Lv Ls kt → tr.cell tt q j = (jN : Fp))
include hL lay ho ho2 hrN hj

theorem fb_PL :
    (fieldRows tr tt (s + 0) 4).Perm
      (((emitAt (msgId K_RC jN) (oN) (u32r Lp)).map Msg.toFp) ++ [] ++ []) := by
  obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sPL) (off := 0) (L := 4) (by simp [plan])
  have hX : (sPL, [(RC, at' [c o], bE, k 1)]) ∈ emits := by simp [emits]
  refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
  rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN) (u32r Lp)
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId]
        try simp only [Vt]
        grind)
      (reg_val hL hH F (by decide) (by decide) (l := [c RcptV3.Lp, k 0, k 0, k 0]) (by simp [loads]) (by simp) (by omega) _
        (fun k hk => by
          have V0 := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) F.fld.pos; simp only [Nat.add_zero] at V0
          rcases k with _ | _ | _ | _ | k <;> simp [u32r, V0.Lp, V0.Lv, V0.Ls, V0.kt, V0.hr] <;> first | rfl | omega)),
    fld_chunk_none hL hH F hX (e := 1) (by decide) rfl,
    fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]

theorem fb_P :
    (fieldRows tr tt (s + 4) Lp).Perm
      (((emitAt (msgId K_RC jN) (oN + 4) (colAt tr tt (s + 4) Lp b)).map Msg.toFp) ++ [] ++ []) := by
  obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sP) (off := 4) (L := Lp) (by simp [plan])
  have hX : (sP, [(RC, at' [c o, k 4], bE, k 1)]) ∈ emits := by simp [emits]
  refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
  rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + 4) (colAt tr tt (s + 4) Lp b)
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId]
        try simp only [Vt]
        grind)
      (fun k hk => col_val _ _ _ _ hk),
    fld_chunk_none hL hH F hX (e := 1) (by decide) rfl,
    fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]

theorem fb_VL :
    (fieldRows tr tt (s + (4 + Lp)) 4).Perm
      (((emitAt (msgId K_RC jN) (oN + (4 + Lp)) (u32r Lv)).map Msg.toFp) ++ ((emitAt (msgId K_PEO rN) (28 + 32 * hN h) (u32r Lv)).map Msg.toFp) ++ []) := by
  obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sVL) (off := (4 + Lp)) (L := 4) (by simp [plan])
  have hX : (sVL, [(RC, at' [c o, k 4, c RcptV3.Lp], bE, k 1), (PEO, at' [k 28, smul 32 (c hr)], bE, k 1)]) ∈ emits := by simp [emits]
  refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
  rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (4 + Lp)) (u32r Lv)
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId]
        try simp only [Vt]
        grind)
      (reg_val hL hH F (by decide) (by decide) (l := [c RcptV3.Lv, k 0, k 0, k 0]) (by simp [loads]) (by simp) (by omega) _
        (fun k hk => by
          have V0 := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) F.fld.pos; simp only [Nat.add_zero] at V0
          rcases k with _ | _ | _ | _ | k <;> simp [u32r, V0.Lp, V0.Lv, V0.Ls, V0.kt, V0.hr] <;> first | rfl | omega)),
    fld_chunk hL hH F hX (e := 1) (by decide) rfl (msgId K_PEO rN) (28 + 32 * hN h) (u32r Lv)
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [PEO, eval_mid, eval_c, eval_k, eval_smul, V.r, msgId]; grind)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId]
        try simp only [Vt]
        grind)
      (reg_val hL hH F (by decide) (by decide) (l := [c RcptV3.Lv, k 0, k 0, k 0]) (by simp [loads]) (by simp) (by omega) _
        (fun k hk => by
          have V0 := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) F.fld.pos; simp only [Nat.add_zero] at V0
          rcases k with _ | _ | _ | _ | k <;> simp [u32r, V0.Lp, V0.Lv, V0.Ls, V0.kt, V0.hr] <;> first | rfl | omega)),
    fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]

theorem fb_V :
    (fieldRows tr tt (s + (8 + Lp)) Lv).Perm
      (((emitAt (msgId K_RC jN) (oN + (8 + Lp)) (colAt tr tt (s + (8 + Lp)) Lv b)).map Msg.toFp) ++ ((emitAt (msgId K_PEO rN) (32 + 32 * hN h) (colAt tr tt (s + (8 + Lp)) Lv b)).map Msg.toFp) ++ []) := by
  obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sV) (off := (8 + Lp)) (L := Lv) (by simp [plan])
  have hX : (sV, [(RC, at' [c o, k 8, c RcptV3.Lp], bE, k 1), (PEO, at' [k 32, smul 32 (c hr)], bE, k 1)]) ∈ emits := by simp [emits]
  refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
  rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (8 + Lp)) (colAt tr tt (s + (8 + Lp)) Lv b)
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId]
        try simp only [Vt]
        grind)
      (fun k hk => col_val _ _ _ _ hk),
    fld_chunk hL hH F hX (e := 1) (by decide) rfl (msgId K_PEO rN) (32 + 32 * hN h) (colAt tr tt (s + (8 + Lp)) Lv b)
      (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [PEO, eval_mid, eval_c, eval_k, eval_smul, V.r, msgId]; grind)
      (fun k hk => by
        have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
        simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId]
        try simp only [Vt]
        grind)
      (fun k hk => col_val _ _ _ _ hk),
    fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]

theorem fb_RID :
    (fieldRows tr tt (s + (8 + Lp + Lv)) 32).Perm
      (((emitAt (msgId K_RC jN) (oN + (8 + Lp + Lv)) (colAt tr tt (s + (8 + Lp + Lv)) 32 b)).map Msg.toFp) ++ ((emitAt (msgId K_LEAF rN) (4) (colAt tr tt (s + (8 + Lp + Lv)) 32 b)).map Msg.toFp) ++ (if h then (emitAt (msgId K_RID rN) (0) (colAt tr tt (s + (8 + Lp + Lv)) 32 b)).map Msg.toFp else [])) := by
  cases h
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sRID) (off := (8 + Lp + Lv)) (L := 32) (by simp [plan, hN])
    have hX : (sRID, [(RC, at' [c o, k 8, c RcptV3.Lp, c RcptV3.Lv], bE, k 1), (LEAF, at' [k 4], bE, k 1), (RIDm, ix, bE, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (8 + Lp + Lv)) (colAt tr tt (s + (8 + Lp + Lv)) 32 b)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk),
      fld_chunk hL hH F hX (e := 1) (by decide) rfl (msgId K_LEAF rN) (4) (colAt tr tt (s + (8 + Lp + Lv)) 32 b)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [LEAF, eval_mid, eval_c, eval_k, eval_smul, V.r, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk),
      fld_chunk_off hL hH F hX (e := 2) (by decide) rfl (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl)]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sRID) (off := (8 + Lp + Lv)) (L := 32) (by simp [plan, hN])
    have hX : (sRID, [(RC, at' [c o, k 8, c RcptV3.Lp, c RcptV3.Lv], bE, k 1), (LEAF, at' [k 4], bE, k 1), (RIDm, ix, bE, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (8 + Lp + Lv)) (colAt tr tt (s + (8 + Lp + Lv)) 32 b)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk),
      fld_chunk hL hH F hX (e := 1) (by decide) rfl (msgId K_LEAF rN) (4) (colAt tr tt (s + (8 + Lp + Lv)) 32 b)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [LEAF, eval_mid, eval_c, eval_k, eval_smul, V.r, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk),
      fld_chunk hL hH F hX (e := 2) (by decide) rfl (msgId K_RID rN) (0) (colAt tr tt (s + (8 + Lp + Lv)) 32 b)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RIDm, eval_mid, eval_c, eval_k, eval_smul, V.r, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk)]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]

theorem fb_T0 :
    (fieldRows tr tt (s + (40 + Lp + Lv)) 1).Perm
      (((emitAt (msgId K_RC jN) (oN + (40 + Lp + Lv)) ([0])).map Msg.toFp) ++ (if h then (emitAt (K_RF) (o2N + (46 + Ls)) ([0])).map Msg.toFp else []) ++ []) := by
  cases h
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sT0) (off := (40 + Lp + Lv)) (L := 1) (by simp [plan, hN])
    have hX : (sT0, [(RC, sum [c o, k 40, c RcptV3.Lp, c RcptV3.Lv], bE, k 1), (RF, sum [c o2, k 46, c RcptV3.Ls], bE, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (40 + Lp + Lv)) ([0])
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          obtain rfl : k = 0 := by omega
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (reg_val hL hH F (by decide) (by decide) (l := ks [0]) (by simp [loads, ks]) (by simp [ks, G_LE]) (by omega) _
          (fun k hk => ks_get _ k (by simp [G_LE]; omega) _)),
      fld_chunk_off hL hH F hX (e := 1) (by decide) rfl (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl),
      fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sT0) (off := (40 + Lp + Lv)) (L := 1) (by simp [plan, hN])
    have hX : (sT0, [(RC, sum [c o, k 40, c RcptV3.Lp, c RcptV3.Lv], bE, k 1), (RF, sum [c o2, k 46, c RcptV3.Ls], bE, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (40 + Lp + Lv)) ([0])
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          obtain rfl : k = 0 := by omega
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (reg_val hL hH F (by decide) (by decide) (l := ks [0]) (by simp [loads, ks]) (by simp [ks, G_LE]) (by omega) _
          (fun k hk => ks_get _ k (by simp [G_LE]; omega) _)),
      fld_chunk hL hH F hX (e := 1) (by decide) rfl (K_RF) (o2N + (46 + Ls)) ([0])
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl) (fun _ _ => rfl)
        (fun k hk => by
          obtain rfl : k = 0 := by omega
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (reg_val hL hH F (by decide) (by decide) (l := ks [0]) (by simp [loads, ks]) (by simp [ks, G_LE]) (by omega) _
          (fun k hk => ks_get _ k (by simp [G_LE]; omega) _)),
      fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]

theorem fb_SL :
    (fieldRows tr tt (s + (41 + Lp + Lv)) 4).Perm
      (((emitAt (msgId K_RC jN) (oN + (41 + Lp + Lv)) (u32r Ls)).map Msg.toFp) ++ (if h then (emitAt (K_RF) (o2N + 10) (u32r Ls)).map Msg.toFp else []) ++ (if h then (emitAt (K_RF) (o2N + (47 + Ls)) (u32r Ls)).map Msg.toFp else [])) := by
  cases h
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sSL) (off := (41 + Lp + Lv)) (L := 4) (by simp [plan, hN])
    have hX : (sSL, [(RC, at' [c o, k 41, c RcptV3.Lp, c RcptV3.Lv], bE, k 1), (RF, at' [c o2, k 10], bE, c hr), (RF, at' [c o2, k 47, c RcptV3.Ls], bE, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (41 + Lp + Lv)) (u32r Ls)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (reg_val hL hH F (by decide) (by decide) (l := [c RcptV3.Ls, k 0, k 0, k 0]) (by simp [loads]) (by simp) (by omega) _
          (fun k hk => by
            have V0 := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) F.fld.pos; simp only [Nat.add_zero] at V0
            rcases k with _ | _ | _ | _ | k <;> simp [u32r, V0.Lp, V0.Lv, V0.Ls, V0.kt, V0.hr, hN] <;> first | rfl | omega)),
      fld_chunk_off hL hH F hX (e := 1) (by decide) rfl (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl),
      fld_chunk_off hL hH F hX (e := 2) (by decide) rfl (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl)]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sSL) (off := (41 + Lp + Lv)) (L := 4) (by simp [plan, hN])
    have hX : (sSL, [(RC, at' [c o, k 41, c RcptV3.Lp, c RcptV3.Lv], bE, k 1), (RF, at' [c o2, k 10], bE, c hr), (RF, at' [c o2, k 47, c RcptV3.Ls], bE, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (41 + Lp + Lv)) (u32r Ls)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (reg_val hL hH F (by decide) (by decide) (l := [c RcptV3.Ls, k 0, k 0, k 0]) (by simp [loads]) (by simp) (by omega) _
          (fun k hk => by
            have V0 := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) F.fld.pos; simp only [Nat.add_zero] at V0
            rcases k with _ | _ | _ | _ | k <;> simp [u32r, V0.Lp, V0.Lv, V0.Ls, V0.kt, V0.hr, hN] <;> first | rfl | omega)),
      fld_chunk hL hH F hX (e := 1) (by decide) rfl (K_RF) (o2N + 10) (u32r Ls)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl) (fun _ _ => rfl)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (reg_val hL hH F (by decide) (by decide) (l := [c RcptV3.Ls, k 0, k 0, k 0]) (by simp [loads]) (by simp) (by omega) _
          (fun k hk => by
            have V0 := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) F.fld.pos; simp only [Nat.add_zero] at V0
            rcases k with _ | _ | _ | _ | k <;> simp [u32r, V0.Lp, V0.Lv, V0.Ls, V0.kt, V0.hr, hN] <;> first | rfl | omega)),
      fld_chunk hL hH F hX (e := 2) (by decide) rfl (K_RF) (o2N + (47 + Ls)) (u32r Ls)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl) (fun _ _ => rfl)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (reg_val hL hH F (by decide) (by decide) (l := [c RcptV3.Ls, k 0, k 0, k 0]) (by simp [loads]) (by simp) (by omega) _
          (fun k hk => by
            have V0 := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) F.fld.pos; simp only [Nat.add_zero] at V0
            rcases k with _ | _ | _ | _ | k <;> simp [u32r, V0.Lp, V0.Lv, V0.Ls, V0.kt, V0.hr, hN] <;> first | rfl | omega))]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]

theorem fb_S :
    (fieldRows tr tt (s + (45 + Lp + Lv)) Ls).Perm
      (((emitAt (msgId K_RC jN) (oN + (45 + Lp + Lv)) (colAt tr tt (s + (45 + Lp + Lv)) Ls b)).map Msg.toFp) ++ (if h then (emitAt (K_RF) (o2N + 14) (colAt tr tt (s + (45 + Lp + Lv)) Ls b)).map Msg.toFp else []) ++ (if h then (emitAt (K_RF) (o2N + (51 + Ls)) (colAt tr tt (s + (45 + Lp + Lv)) Ls b)).map Msg.toFp else [])) := by
  cases h
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sS) (off := (45 + Lp + Lv)) (L := Ls) (by simp [plan, hN])
    have hX : (sS, [(RC, at' [c o, k 45, c RcptV3.Lp, c RcptV3.Lv], bE, k 1), (RF, at' [c o2, k 14], bE, c hr), (RF, at' [c o2, k 51, c RcptV3.Ls], bE, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (45 + Lp + Lv)) (colAt tr tt (s + (45 + Lp + Lv)) Ls b)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk),
      fld_chunk_off hL hH F hX (e := 1) (by decide) rfl (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl),
      fld_chunk_off hL hH F hX (e := 2) (by decide) rfl (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl)]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sS) (off := (45 + Lp + Lv)) (L := Ls) (by simp [plan, hN])
    have hX : (sS, [(RC, at' [c o, k 45, c RcptV3.Lp, c RcptV3.Lv], bE, k 1), (RF, at' [c o2, k 14], bE, c hr), (RF, at' [c o2, k 51, c RcptV3.Ls], bE, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (45 + Lp + Lv)) (colAt tr tt (s + (45 + Lp + Lv)) Ls b)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk),
      fld_chunk hL hH F hX (e := 1) (by decide) rfl (K_RF) (o2N + 14) (colAt tr tt (s + (45 + Lp + Lv)) Ls b)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl) (fun _ _ => rfl)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk),
      fld_chunk hL hH F hX (e := 2) (by decide) rfl (K_RF) (o2N + (51 + Ls)) (colAt tr tt (s + (45 + Lp + Lv)) Ls b)
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl) (fun _ _ => rfl)
        (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (fun k hk => col_val _ _ _ _ hk)]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]

theorem fb_KT :
    (fieldRows tr tt (s + (45 + Lp + Lv + Ls)) 1).Perm
      (((emitAt (msgId K_RC jN) (oN + (45 + Lp + Lv + Ls)) ([kt])).map Msg.toFp) ++ (if h then (emitAt (K_RF) (o2N + (51 + 2 * Ls)) ([kt])).map Msg.toFp else []) ++ []) := by
  cases h
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sKT) (off := (45 + Lp + Lv + Ls)) (L := 1) (by simp [plan, hN])
    have hX : (sKT, [(RC, sum [c o, k 45, c RcptV3.Lp, c RcptV3.Lv, c RcptV3.Ls], bE, k 1), (RF, sum [c o2, k 51, smul 2 (c RcptV3.Ls)], bE, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (45 + Lp + Lv + Ls)) ([kt])
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          obtain rfl : k = 0 := by omega
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (reg_val hL hH F (by decide) (by decide) (l := [c RcptV3.kt]) (by simp [loads]) (by simp) (by omega) _
          (fun k hk => by
            have V0 := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) F.fld.pos; simp only [Nat.add_zero] at V0
            rcases k with _ | _ | _ | _ | k <;> simp [u32r, V0.Lp, V0.Lv, V0.Ls, V0.kt, V0.hr, hN] <;> first | rfl | omega)),
      fld_chunk_off hL hH F hX (e := 1) (by decide) rfl (fun k hk => by
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl),
      fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
  · obtain ⟨F, hH, hT⟩ := lay_fld hL lay (X := sKT) (off := (45 + Lp + Lv + Ls)) (L := 1) (by simp [plan, hN])
    have hX : (sKT, [(RC, sum [c o, k 45, c RcptV3.Lp, c RcptV3.Lv, c RcptV3.Ls], bE, k 1), (RF, sum [c o2, k 51, smul 2 (c RcptV3.Ls)], bE, c hr)]) ∈ emits := by simp [emits]
    refine (slots_perm tr _ _ _).trans (List.Perm.of_eq ?_)
    rw [fld_chunk hL hH F hX (e := 0) (by decide) rfl (msgId K_RC jN) (oN + (45 + Lp + Lv + Ls)) ([kt])
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun _ _ => rfl) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [RC, eval_mid, eval_c, eval_k, eval_smul, V.j, msgId]; grind)
        (fun k hk => by
          obtain rfl : k = 0 := by omega
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (reg_val hL hH F (by decide) (by decide) (l := [c RcptV3.kt]) (by simp [loads]) (by simp) (by omega) _
          (fun k hk => by
            have V0 := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) F.fld.pos; simp only [Nat.add_zero] at V0
            rcases k with _ | _ | _ | _ | k <;> simp [u32r, V0.Lp, V0.Lv, V0.Ls, V0.kt, V0.hr, hN] <;> first | rfl | omega)),
      fld_chunk hL hH F hX (e := 1) (by decide) rfl (K_RF) (o2N + (51 + 2 * Ls)) ([kt])
        (by simp [colAt_len, u32r, tailN, G_LEn, systemN, pubBytes]; try omega) (fun k hk => by have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk; simp only [eval_c, V.hr, hN]; rfl) (fun _ _ => rfl)
        (fun k hk => by
          obtain rfl : k = 0 := by omega
          have V := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) hk
          simp only [at', ix, RC, RF, PEO, LEAF, RIDm, varE, eval_sum_append, eval_sum_cons, eval_sum_nil, eval_c, eval_k, eval_smul, eval_mid, eval_add, V.j, V.o, V.o2, V.r, V.Lp, V.Lv, V.Ls, V.kt, V.hr, V.idx, msgId, hN]
          try simp only [Vt]
          grind)
        (reg_val hL hH F (by decide) (by decide) (l := [c RcptV3.kt]) (by simp [loads]) (by simp) (by omega) _
          (fun k hk => by
            have V0 := rowV hL lay ho ho2 hrN F (fun _ _ => hj _ (by omega) (by omega)) F.fld.pos; simp only [Nat.add_zero] at V0
            rcases k with _ | _ | _ | _ | k <;> simp [u32r, V0.Lp, V0.Lv, V0.Ls, V0.kt, V0.hr, hN] <;> first | rfl | omega)),
      fld_chunk_none hL hH F hX (e := 2) (by decide) rfl]
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]


end ZkFormal.NearV3.RcptV3Proof
