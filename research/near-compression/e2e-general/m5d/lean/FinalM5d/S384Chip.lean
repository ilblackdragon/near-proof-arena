import FinalM5d.HbWhole
import StateM5a.WsDecode

/-!
# FinalM5d.S384Chip — an active `S384` row is a chip compression (lane B's contract)

`s384_comp`: in a trace satisfying `finalAirS` (the chip stub's `IF384` sends are the chip's),
under lane B's `Sha512IfContract compress` on those sends, every active `S384` row's 32 limb
triples (`S384.ifLimbs`: `hin ‖ block ‖ hout`) are the 21-bit limbs of `h ‖ blk ‖ compress h blk`
for 64-bit words `h` (8) and `blk` (16) — through lane B's `Sha512If.comp_sound`.
With `S384Rec.sha384_of_blocks`, what remains for the `S384` table is the row chain (`hin` =
IV384 / the previous `hout`) and the padding (the blocks are `pad` of the received bytes).
-/

namespace FinalM5d.S384Chip

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound FinalM5d FinalM5d.BusMem FinalM5d.Whole
open StateM5a.Bus StateM5a.Sha512If StateM5a.WsDecode

variable {tr : Trace Fp} {pub : List Fp}

/-- The row's 32 limb triples, as naturals. -/
def triples (tr : Trace Fp) (r : Nat) (pub : List Fp) : List (List Nat) :=
  (List.range 32).map fun k =>
    [ev tr 1 r pub (S384.ifLimbs.getD (3 * k) 0), ev tr 1 r pub (S384.ifLimbs.getD (3 * k + 1) 0),
     ev tr 1 r pub (S384.ifLimbs.getD (3 * k + 2) 0)]

/-- The row's `IF384` receive number `m`. -/
def ifRcv (m : Nat) : Interaction :=
  rcv B_IF384 S384.act ([S384.T.c "cid", K m] ++
    (List.range 6).map fun k => S384.ifLimbs.getD (6 * m + k) 0)

theorem ifRcv_mem {m : Nat} (hm : m < 16) : ifRcv m ∈ S384.interactions := by
  unfold S384.interactions
  exact List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.2 ⟨m, List.mem_range.2 hm, rfl⟩)))

theorem triples_get {r k : Nat} (hk : k < 32) :
    (triples tr r pub).getD k zeroL =
      [ev tr 1 r pub (S384.ifLimbs.getD (3 * k) 0), ev tr 1 r pub (S384.ifLimbs.getD (3 * k + 1) 0),
       ev tr 1 r pub (S384.ifLimbs.getD (3 * k + 2) 0)] := by
  simp [triples, List.getD_eq_getElem?_getD, hk]

/-- **An active `S384` row is a chip compression.** -/
theorem s384_comp (h : Holds finalAirS pub tr) {compress : List Nat → List Nat → List Nat}
    (hcok : CompressOK compress)
    (hC : Sha512IfContract compress ((busList finalAirS tr pub B_IF384 true).map decIf))
    {r : Nat} (hr : r < tr.height 1) (hact : ev tr 1 r pub S384.act = 1) :
    ∃ hh blk : List Nat, hh.length = 8 ∧ blk.length = 16 ∧ W64 hh ∧ W64 blk ∧
      triples tr r pub = (hh ++ blk ++ compress hh blk).map StateM5a.wlimbs := by
  apply comp_sound hcok hC (cid := ev tr 1 r pub (S384.T.c "cid")) (by simp [triples])
  intro x hx
  obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hx
  have hm' := List.mem_range.1 hm
  have hmem : ifRcv m ∈ (finalAirS.tables[1]'(by decide)).interactions := by
    rw [tab1]; exact ifRcv_mem hm'
  have ho := occ_of (by decide) hr hmem ((multNat_one rfl).2 (evalOne hact))
  have hin := (mem_iff_of_holds h B_IF384 _).2 (mem_busList.2 ho)
  refine List.mem_map.2 ⟨_, hin, ?_⟩
  rw [triples_get (by omega), triples_get (by omega)]
  simp only [decIf, Interaction.msgVal, ifRcv, rcv, List.map_cons, List.map_append, List.cons_append,
    List.getD_cons_zero, List.getD_cons_succ, IfMsg.mk.injEq]
  have e6 : List.range 6 = [0, 1, 2, 3, 4, 5] := rfl
  simp only [e6, List.map_cons, List.map_nil, List.nil_append, List.getD_cons_zero,
    List.getD_cons_succ]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · show ((Expr.const m).eval tr 1 r pub).toNat = m
    exact (ev_const (tr := tr) (t := 1) (r := r) (pub := pub) m).trans (Nat.mod_eq_of_lt (by omega))
  · simp only [tn, show 3 * (2 * m) = 6 * m + 0 by omega, show 3 * (2 * m) + 1 = 6 * m + 1 by omega,
      show 3 * (2 * m) + 2 = 6 * m + 2 by omega]; rfl
  · simp only [tn, show 3 * (2 * m + 1) = 6 * m + 3 by omega,
      show 3 * (2 * m + 1) + 1 = 6 * m + 4 by omega, show 3 * (2 * m + 1) + 2 = 6 * m + 5 by omega]; rfl

end FinalM5d.S384Chip
