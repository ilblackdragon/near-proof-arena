import ZkFormal.NearV3.Candidates.ProcSound.Round

/-!
# ZkFormal.NearV3.Sched.View.ProcMsg — the messages of a round of `sprV3`

For a header `h` with round constants `τ, K, z, T, Lr` (`round_shape`):

* **`hdr_msgs`**: the shuffle header `SSHUF (lidOf τ T, L0 … L15, kq, Lr, kend)` received once,
  and the comparator `SCMP (Kq, K + 1, 1)` with multiplicity `1 − zk`;
* **`ent_msgs`**: on entry `j < Lr` (row `w = h + 1 + j`, time `T + j`): `SPUSH (τ, K, z, ts, ein)`
  received, `SSIN (lid, j, ein)` sent, `SSOUT (lid, j, eout)` received,
  `SINC (τ, eout, inc, rem, s, r, link)` received, the three GRANT ops on `SOP`
  (`addrOf τ 1 s`, `addrOf τ 2 r`, `addrOf τ 0 link`, time `T + j`, in / out values, `inc`, `ok`,
  condition), each once; `SPUSH (τ, alOut, [alOut = 0]·(z + 1), T + j, eout + 1)` sent with
  multiplicity `ok·(1 − last)`; the comparator `SCMP (next ts or T, ts + 1, 1)` once; and the
  entry-row facts (`ok = cS·cR·cL`, `last ↔ rem = 0`).

Message values are `Fp.ofNat` of naturals (so reduced modulo `P`).
-/

namespace ZkFormal.NearV3.Candidates.ProcSound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Proc

section
variable {tr : Trace Fp} {tp : Nat} {pub : List Fp}

theorem i1_def : interactions[1]! = Interaction.mk B_SSHUF [c kH]
    ([lidE] ++ keyMsg ++ [c kq, c Lr, c kend]) false := rfl
theorem i2_def : interactions[2]! = Interaction.mk B_SCMP [c cg] [c cx, c cy, k 1] true := rfl
theorem i3_def : interactions[3]! = Interaction.mk B_SPUSH [c kE]
    [c tau, c K, c z, c ts, c ein] false := rfl
theorem i4_def : interactions[4]! = Interaction.mk B_SSIN [c kE] [lidE, c x, c ein] true := rfl
theorem i5_def : interactions[5]! = Interaction.mk B_SSOUT [c kE] [lidE, c x, c eout] false := rfl
theorem i6_def : interactions[6]! = Interaction.mk B_SINC [c kE]
    [c tau, c eout, c inc, c rem, c s, c r, c link] false := rfl
theorem i7_def : interactions[7]! = Interaction.mk B_SOP [c kE]
    [aS, tE, k OP_GRANT, c sbIn, c sbOut, c inc, c ok, c cS] true := rfl
theorem i8_def : interactions[8]! = Interaction.mk B_SOP [c kE]
    [aR, tE, k OP_GRANT, c rbIn, c rbOut, c inc, c ok, c cR] true := rfl
theorem i9_def : interactions[9]! = Interaction.mk B_SOP [c kE]
    [aL, tE, k OP_GRANT, c alIn, c alOut, c inc, c ok, c cL] true := rfl
theorem i10_def : interactions[10]! = Interaction.mk B_SPUSH [c pm]
    [c tau, c alOut, c zn, tE, .add (c eout) (k 1)] true := rfl

theorem ev_lid (w : Nat) :
    lidE.eval tr tp w pub = Fp.ofNat (lidOf (cv tr tp w tau) (cv tr tp w T)) :=
  ev_of (by simp only [lidE, lidOf, zev_add, zev_smul, zev_c, cur_cv]; omega)
theorem ev_aS (w : Nat) :
    aS.eval tr tp w pub = Fp.ofNat (addrOf (cv tr tp w tau) 1 (cv tr tp w s)) :=
  ev_of (by simp only [aS, addrOf, zev_add, zev_smul, zev_c, zev_k, cur_cv]; omega)
theorem ev_aR (w : Nat) :
    aR.eval tr tp w pub = Fp.ofNat (addrOf (cv tr tp w tau) 2 (cv tr tp w r)) :=
  ev_of (by simp only [aR, addrOf, zev_add, zev_smul, zev_c, zev_k, cur_cv]; omega)
theorem ev_aL (w : Nat) :
    aL.eval tr tp w pub = Fp.ofNat (addrOf (cv tr tp w tau) 0 (cv tr tp w link)) :=
  ev_of (by simp only [aL, addrOf, zev_add, zev_smul, zev_c, cur_cv]; omega)
theorem ev_tE (w : Nat) : tE.eval tr tp w pub = Fp.ofNat (cv tr tp w T + cv tr tp w x) :=
  ev_of (by simp only [tE, zev_add, zev_c, cur_cv]; omega)
theorem ev_e1 (w : Nat) :
    (Expr.add (c eout) (k 1)).eval tr tp w pub = Fp.ofNat (cv tr tp w eout + 1) :=
  ev_of (by simp only [zev_add, zev_c, zev_k, cur_cv]; omega)

/-- **Header messages.** -/
theorem hdr_msgs (hL : PLocal tr tp pub) {h : Nat} (hh0 : h < tr.height tp)
    (hh : cv tr tp h kH = 1) :
    (interactions[1]!).multNat tr tp h pub = 1 ∧
    (interactions[1]!).msgVal tr tp h pub =
      ([lidOf (cv tr tp h tau) (cv tr tp h T)] ++ (List.range 16).map (fun i => cv tr tp h (colL i)) ++
        [cv tr tp h kq, cv tr tp h Lr, cv tr tp h kend]).map Fp.ofNat ∧
    (interactions[2]!).multNat tr tp h pub = 1 - cv tr tp h zk ∧
    (interactions[2]!).msgVal tr tp h pub = [cv tr tp h Kq, cv tr tp h K + 1, 1].map Fp.ofNat := by
  obtain ⟨hcg, hcx, hcy⟩ := cmp_hdr hL hh0 hh
  have hb := bool_of hL hh0 (x := cg) (by simp [boolCols])
  refine ⟨mult_of rfl (by simp only [zev_c, cur_cv, hh]; rfl), ?_, ?_, ?_⟩
  · rw [i1_def]
    simp only [Interaction.msgVal, keyMsg, List.map_append, List.map_cons, List.map_nil,
      List.map_map, Function.comp_def, ev_c, ev_lid]
  · rw [← hcg]; exact mult_bit rfl (by simp only [zev_c, cur_cv]) hb
  · rw [i2_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, ev_k, hcx, hcy, ofNat_mod]

/-- **Entry messages.** -/
theorem ent_msgs (hL : PLocal tr tp pub) (hH : tr.height tp ≤ 2 ^ 22) {h : Nat}
    (hh0 : h < tr.height tp) (hh : cv tr tp h kH = 1) {j : Nat} (hj : j < cv tr tp h Lr) :
    -- SPUSH receive
    (interactions[3]!).multNat tr tp (h + 1 + j) pub = 1 ∧
    (interactions[3]!).msgVal tr tp (h + 1 + j) pub =
      [cv tr tp h tau, cv tr tp h K, cv tr tp h z, cv tr tp (h + 1 + j) ts,
        cv tr tp (h + 1 + j) ein].map Fp.ofNat ∧
    -- SSIN send
    (interactions[4]!).multNat tr tp (h + 1 + j) pub = 1 ∧
    (interactions[4]!).msgVal tr tp (h + 1 + j) pub =
      [lidOf (cv tr tp h tau) (cv tr tp h T), j, cv tr tp (h + 1 + j) ein].map Fp.ofNat ∧
    -- SSOUT receive
    (interactions[5]!).multNat tr tp (h + 1 + j) pub = 1 ∧
    (interactions[5]!).msgVal tr tp (h + 1 + j) pub =
      [lidOf (cv tr tp h tau) (cv tr tp h T), j, cv tr tp (h + 1 + j) eout].map Fp.ofNat ∧
    -- SINC receive
    (interactions[6]!).multNat tr tp (h + 1 + j) pub = 1 ∧
    (interactions[6]!).msgVal tr tp (h + 1 + j) pub =
      [cv tr tp h tau, cv tr tp (h + 1 + j) eout, cv tr tp (h + 1 + j) inc,
        cv tr tp (h + 1 + j) rem, cv tr tp (h + 1 + j) s, cv tr tp (h + 1 + j) r,
        cv tr tp (h + 1 + j) link].map Fp.ofNat ∧
    -- SOP: sender, receiver, link GRANTs at time T + j
    (interactions[7]!).multNat tr tp (h + 1 + j) pub = 1 ∧
    (interactions[7]!).msgVal tr tp (h + 1 + j) pub =
      [addrOf (cv tr tp h tau) 1 (cv tr tp (h + 1 + j) s), cv tr tp h T + j, OP_GRANT,
        cv tr tp (h + 1 + j) sbIn, cv tr tp (h + 1 + j) sbOut, cv tr tp (h + 1 + j) inc,
        cv tr tp (h + 1 + j) ok, cv tr tp (h + 1 + j) cS].map Fp.ofNat ∧
    (interactions[8]!).multNat tr tp (h + 1 + j) pub = 1 ∧
    (interactions[8]!).msgVal tr tp (h + 1 + j) pub =
      [addrOf (cv tr tp h tau) 2 (cv tr tp (h + 1 + j) r), cv tr tp h T + j, OP_GRANT,
        cv tr tp (h + 1 + j) rbIn, cv tr tp (h + 1 + j) rbOut, cv tr tp (h + 1 + j) inc,
        cv tr tp (h + 1 + j) ok, cv tr tp (h + 1 + j) cR].map Fp.ofNat ∧
    (interactions[9]!).multNat tr tp (h + 1 + j) pub = 1 ∧
    (interactions[9]!).msgVal tr tp (h + 1 + j) pub =
      [addrOf (cv tr tp h tau) 0 (cv tr tp (h + 1 + j) link), cv tr tp h T + j, OP_GRANT,
        cv tr tp (h + 1 + j) alIn, cv tr tp (h + 1 + j) alOut, cv tr tp (h + 1 + j) inc,
        cv tr tp (h + 1 + j) ok, cv tr tp (h + 1 + j) cL].map Fp.ofNat ∧
    -- SPUSH send
    (interactions[10]!).multNat tr tp (h + 1 + j) pub =
      cv tr tp (h + 1 + j) ok * (1 - cv tr tp (h + 1 + j) lastf) ∧
    (interactions[10]!).msgVal tr tp (h + 1 + j) pub =
      [cv tr tp h tau, cv tr tp (h + 1 + j) alOut,
        (if cv tr tp (h + 1 + j) alOut = 0 then cv tr tp h z + 1 else 0), cv tr tp h T + j,
        cv tr tp (h + 1 + j) eout + 1].map Fp.ofNat ∧
    -- SCMP
    (interactions[2]!).multNat tr tp (h + 1 + j) pub = 1 ∧
    (interactions[2]!).msgVal tr tp (h + 1 + j) pub =
      [(if j + 1 = cv tr tp h Lr then cv tr tp h T else cv tr tp (h + 1 + j + 1) ts),
        cv tr tp (h + 1 + j) ts + 1, 1].map Fp.ofNat ∧
    -- entry row
    cv tr tp (h + 1 + j) ok =
      cv tr tp (h + 1 + j) cS * cv tr tp (h + 1 + j) cR * cv tr tp (h + 1 + j) cL ∧
    (cv tr tp (h + 1 + j) lastf = 1 ↔ cv tr tp (h + 1 + j) rem = 0) ∧
    cv tr tp (h + 1 + j) cS ≤ 1 ∧ cv tr tp (h + 1 + j) cR ≤ 1 ∧ cv tr tp (h + 1 + j) cL ≤ 1 := by
  obtain ⟨-, -, RS⟩ := round_shape hL hH hh0 hh
  obtain ⟨⟨hw, hE, hx, RC, -⟩, hle⟩ := RS j hj
  have hτ := RC tau (by simp [roundCols])
  have hT := RC T (by simp [roundCols])
  have hK := RC K (by simp [roundCols])
  have hz := RC z (by simp [roundCols])
  obtain ⟨hok, hlast, -, hpm, hS, hR, hLc, -⟩ := entry_row hL hw hE
  obtain ⟨hcg, hcy, hcxl, hcxn⟩ := cmp_ent hL hw hE
  have m1 : zev (tenv tr tp (h + 1 + j) pub) (c kE) = 1 := by simp only [zev_c, cur_cv, hE]; rfl
  have hzn : Fp.ofNat (cv tr tp (h + 1 + j) zn) =
      Fp.ofNat (if cv tr tp (h + 1 + j) alOut = 0 then cv tr tp h z + 1 else 0) := by
    rw [zn_def hL hw hE, hz]
    by_cases hc : cv tr tp (h + 1 + j) alOut = 0
    · simp only [hc, ↓reduceIte, ofNat_mod]
    · simp only [hc, ↓reduceIte]
  have hcx : Fp.ofNat (cv tr tp (h + 1 + j) cx) =
      Fp.ofNat (if j + 1 = cv tr tp h Lr then cv tr tp h T else cv tr tp (h + 1 + j + 1) ts) := by
    by_cases hc : j + 1 = cv tr tp h Lr
    · rw [if_pos hc] at hle ⊢; rw [hcxl hle, hT]
    · rw [if_neg hc] at hle ⊢; rw [hcxn hle]
  refine ⟨mult_of rfl m1, ?_, mult_of rfl m1, ?_, mult_of rfl m1, ?_, mult_of rfl m1, ?_,
    mult_of rfl m1, ?_, mult_of rfl m1, ?_, mult_of rfl m1, ?_, ?_, ?_,
    mult_of rfl (by simp only [zev_c, cur_cv, hcg]; rfl), ?_, hok, hlast, hS, hR, hLc⟩
  · rw [i3_def]; simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, hτ, hK, hz]
  · rw [i4_def]; simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, ev_lid, hτ, hT, hx]
  · rw [i5_def]; simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, ev_lid, hτ, hT, hx]
  · rw [i6_def]; simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, hτ]
  · rw [i7_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, ev_k, ev_aS, ev_tE, hτ, hT, hx]
  · rw [i8_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, ev_k, ev_aR, ev_tE, hτ, hT, hx]
  · rw [i9_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, ev_k, ev_aL, ev_tE, hτ, hT, hx]
  · rw [← hpm]
    exact mult_bit rfl (by simp only [zev_c, cur_cv]) (bool_of hL hw (x := pm) (by simp [boolCols]))
  · rw [i10_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, ev_tE, ev_e1, hτ, hT, hx, hzn]
  · rw [i2_def]
    simp only [Interaction.msgVal, List.map_cons, List.map_nil, ev_c, ev_k, hcx, hcy, ofNat_mod]

end

end ZkFormal.NearV3.Candidates.ProcSound
