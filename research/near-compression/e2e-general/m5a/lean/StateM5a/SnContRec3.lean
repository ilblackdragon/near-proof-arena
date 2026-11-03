import StateM5a.SnContRec1
import StateM5a.SnContRec2

/-!
# StateM5a.SnContRec3 — a continued head's record over its full key is `Hashed`

`contKeyB tr pub r M = hpDec (hp_0..hp_31 ++ M) odd`: the nibbles the hashed `hexPrefix`
encodes, where `M` are the `SNC` bytes of the message (`SnContRec2.cont_node`).  **`grecK_hashed`**:
when the message is `serC … M …` (every entry a byte, `hplen < 2^16`), the record
`gRecK (contKeyB M)` is `Hashed` to its SHA-256, and the key has `2·(hplen − 1) + odd`
nibbles, all `< 16`.
-/

namespace StateM5a.SnContRec3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.SnSer StateM5a.RowSnMsg StateM5a.SnRec StateM5a.SnHashed StateM5a.BrSer
open StateM5a.SnContRec1 StateM5a.SnContRec2 StateM5a.SnContSer2

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-- The full key of a continued head, decoded from its hashed `hexPrefix` (`M`: the `SNC` part). -/
def contKeyB (tr : Trace Fp) (pub : List Fp) (r : Nat) (M : List Nat) : List Nat :=
  hpDec ((List.range 32).map (fun m => ev tr 3 r pub (Sn.c "hp" m)) ++ M) (ev tr 3 r pub (Sn.c "odd"))

theorem m_hp0 : Sn.c "hp" 0 - (sm 32 (Sn.c "isL") + Sn.c "odd" * (16 + Sn.k 0)) ∈ Sn.constraints := by
  unfold Sn.constraints; simp

theorem hp0_arith (L O K0 V : Nat) (hL : L ≤ 1) (hO : O ≤ 1) (hK : K0 < 16)
    (h : V = (32 % P * L % P + O * ((16 % P + K0) % P) % P) % P) : V = 32 * L + O * (16 + K0) := by
  rcases (by omega : L = 0 ∨ L = 1) with rfl | rfl <;> rcases (by omega : O = 0 ∨ O = 1) with rfl | rfl <;>
    simp at h <;> omega

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem ev_hp0 (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0) (hk0 : ev tr 3 r pub (Sn.c "k" 0) < 16) :
    ev tr 3 r pub (Sn.c "hp" 0) =
      32 * ev tr 3 r pub (Sn.c "isL") + ev tr 3 r pub (Sn.c "odd") * (16 + ev tr 3 r pub (Sn.c "k" 0)) := by
  have e := eq_of_sub (FieldRows.hold rfl hc m_hp0)
  rw [FieldRows2.sn_k_lt 0 (by decide), ev_hadd, ev3_sm, ev_hmul, ev_hadd,
    show ev tr 3 r pub (16 : Expr) = 16 % P from ev_const 16] at e
  exact hp0_arith _ _ _ _ (FieldRows2.sn_bool hc "isL" (by simp)) (FieldRows2.sn_bool hc "odd" (by simp)) hk0 e

set_option maxHeartbeats 8000000 in
/-- **The record over the decoded full key is `Hashed`.** -/
theorem grecK_hashed (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hA : ev tr 3 r pub (Sn.c "act") = 1) (hk0 : ev tr 3 r pub (Sn.c "k" 0) < 16) {x mb : Nat → Expr} {xf : Expr} {M : List Nat}
    (hML : M.length = ev tr 3 r pub (Sn.c "hplen") - 32) (hMb : ∀ v ∈ M, v < 256)
    (hH32 : 32 ≤ ev tr 3 r pub (Sn.c "hplen")) (hH256 : ev tr 3 r pub (Sn.c "hplen") < 65536)
    (hby : ∀ k, k < 5 + ev tr 3 r pub (Sn.c "hplen") + payLen tr pub r + 8 →
      (k < 37 ∨ 5 + ev tr 3 r pub (Sn.c "hplen") ≤ k) →
      headF tr pub r (ev tr 3 r pub (Sn.c "hplen")) x mb k < 256)
    (hx3 : ev tr 3 r pub (Sn.c "isL") = 1 → ev tr 3 r pub (x 3) = 0)
    (hxf : ev tr 3 r pub (Sn.c "isL") ≠ 1 → ev tr 3 r pub xf = 0) :
    (contKeyB tr pub r M).length = 2 * (ev tr 3 r pub (Sn.c "hplen") - 1) + ev tr 3 r pub (Sn.c "odd") ∧
    nibblesOk (contKeyB tr pub r M) = true ∧
    Hashed (gRecK tr pub r (contKeyB tr pub r M) x xf mb)
      (sha256 ((serC (ev tr 3 r pub (sm 3 (Sn.c "isE"))) (ev tr 3 r pub (Sn.c "hplen"))
        (fun m => ev tr 3 r pub (Sn.c "hp" m)) M (payLen tr pub r) (fun t => ev tr 3 r pub (x t))
        (fun b => ev tr 3 r pub (mb b))).map UInt8.ofNat)) := by
  have hops := sn_ops hc
  have hL := FieldRows2.sn_bool hc "isL" (by simp)
  have hO := FieldRows2.sn_bool hc "odd" (by simp)
  generalize hHd : ev tr 3 r pub (Sn.c "hplen") = H at hML hH32 hH256 hby ⊢
  -- byte facts
  have hhp : ∀ m, m < 32 → ev tr 3 r pub (Sn.c "hp" m) < 256 := fun m hm => by
    have := hby (5 + m) (by unfold payLen; omega) (by omega); rwa [headF_hp hm] at this
  have hpay : ∀ t, t < payLen tr pub r → ev tr 3 r pub (x t) < 256 := fun t ht => by
    have := hby (5 + H + t) (by omega) (by omega); rwa [headF_x hH32 ht] at this
  have hmb : ∀ b, b < 8 → ev tr 3 r pub (mb b) < 256 := fun b hb => by
    have := hby (5 + H + payLen tr pub r + b) (by omega) (by omega); rwa [headF_mb hH32] at this
  -- the decoded key
  obtain ⟨B, hB⟩ : ∃ B, B = (List.range 32).map (fun m => ev tr 3 r pub (Sn.c "hp" m)) ++ M := ⟨_, rfl⟩
  have hBb : ∀ b ∈ B, b < 256 := by
    intro b hb
    rw [hB] at hb
    rcases List.mem_append.1 hb with h | h
    · simp only [List.mem_map, List.mem_range] at h
      obtain ⟨m, hm, rfl⟩ := h; exact hhp m hm
    · exact hMb b h
  have hB0 : B.headD 0 = 32 * (if decide (ev tr 3 r pub (Sn.c "isL") = 1) then 1 else 0) +
      ev tr 3 r pub (Sn.c "odd") * (16 + ev tr 3 r pub (Sn.c "k" 0)) := by
    rw [hB, show List.range 32 = 0 :: List.range' 1 31 from rfl]
    simp only [List.map_cons, List.cons_append, List.headD_cons]
    rw [ev_hp0 hc hk0]
    rcases (by omega : ev tr 3 r pub (Sn.c "isL") = 0 ∨ ev tr 3 r pub (Sn.c "isL") = 1) with h | h <;> simp [h]
  have hBl : B.length = H := by rw [hB]; simp [hML]; omega
  obtain ⟨hhpx, hnib, hKl⟩ := hexPrefix_hpDec B (decide (ev tr 3 r pub (Sn.c "isL") = 1))
    (ev tr 3 r pub (Sn.c "odd")) _ hO hk0 hBb (by intro h; rw [h] at hBl; simp at hBl; omega) hB0
  have hK : contKeyB tr pub r M = hpDec B (ev tr 3 r pub (Sn.c "odd")) := by rw [hB]; rfl
  rw [hK]
  refine ⟨by rw [hKl, hBl], hnib, ?_⟩
  have hlen : (hexPrefix (hpDec B (ev tr 3 r pub (Sn.c "odd"))) (decide (ev tr 3 r pub (Sn.c "isL") = 1))).length = H := by
    have := congrArg List.length hhpx; simp at this; omega
  have hhpE := map_toNat_eq hhpx
  -- the common head
  have hisE : ev tr 3 r pub (Sn.c "isE") = 1 - ev tr 3 r pub (Sn.c "isL") := by
    obtain ⟨hfl, h1, h2, h3, h4, h5, h6, -, -⟩ := hops
    have := hfl "isE" (by simp [RowSn.snNames]); omega
  have htag : ev tr 3 r pub (sm 3 (Sn.c "isE")) = 3 * (1 - ev tr 3 r pub (Sn.c "isL")) := by
    rw [ev3_sm, hisE]; omega
  have hhead : (serC (ev tr 3 r pub (sm 3 (Sn.c "isE"))) H (fun m => ev tr 3 r pub (Sn.c "hp" m)) M
        (payLen tr pub r) (fun t => ev tr 3 r pub (x t)) (fun b => ev tr 3 r pub (mb b))).map UInt8.ofNat =
      [UInt8.ofNat (3 * (1 - ev tr 3 r pub (Sn.c "isL")))] ++
        u32 (hexPrefix (hpDec B (ev tr 3 r pub (Sn.c "odd"))) (decide (ev tr 3 r pub (Sn.c "isL") = 1))).length ++
        hexPrefix (hpDec B (ev tr 3 r pub (Sn.c "odd"))) (decide (ev tr 3 r pub (Sn.c "isL") = 1)) ++
        (List.range (payLen tr pub r)).map (fun t => UInt8.ofNat (ev tr 3 r pub (x t))) ++
        u64 (memS tr pub r mb) := by
    rw [hlen, u32_mid hH256, hhpE, memS_u64 hmb, hB, htag]
    simp only [serC, List.map_append, List.map_cons, List.map_nil, List.map_map, List.cons_append,
      List.nil_append, List.append_assoc]
    rfl
  by_cases h1 : ev tr 3 r pub (Sn.c "isL") = 1
  · -- a leaf
    have hpl36 : payLen tr pub r = 4 + 32 := by unfold payLen; omega
    have x3 := hx3 h1
    have hx : ∀ t, t < 36 → ev tr 3 r pub (x t) < 256 := fun t ht => hpay t (by omega)
    have hvl : ev tr 3 r pub (Sn.vlenOf x) = ev tr 3 r pub (x 0) + 256 * ev tr 3 r pub (x 1) +
        65536 * (ev tr 3 r pub (x 2) + 256 * ev tr 3 r pub (x 3)) := by
      unfold Sn.vlenOf
      rw [ev_hadd, ev_hadd, ev3_sm, ev3_sm, x3]
      have := hx 0 (by omega); have := hx 1 (by omega); have := hx 2 (by omega)
      omega
    have hvlt : ev tr 3 r pub (Sn.vlenOf x) < 4294967296 := by
      rw [hvl, x3]; have := hx 0 (by omega); have := hx 1 (by omega); have := hx 2 (by omega); omega
    have hh : bytesOf ((pack2 fun b => x (4 + b)).map (nE tr pub r)) =
        (List.range 32).map fun j => UInt8.ofNat (ev tr 3 r pub (x (4 + j))) :=
      bytesOf_pack3 (fun b => x (4 + b)) (fun j hj => hx _ (by omega))
    have hhl : (bytesOf ((pack2 fun b => x (4 + b)).map (nE tr pub r))).length = 32 := by rw [hh]; simp
    simp only [gRecK, h1, ↓reduceIte]
    refine ⟨trivial, ?_, ⟨_, _, rfl⟩, ?_⟩
    · simp only [Rec.toP, PTrie.wf, hnib, slotOk, hvlt, hhl, memS_lt hmb, Bool.true_and, decide_true,
        beq_self_eq_true, Bool.and_true]
      simp only [h1, decide_true] at hlen
      rw [hlen]; (try simp) <;> omega
    · simp only [Rec.toP, PTrie.hashOf]
      congr 1
      rw [hhead, hpl36, range_split, Slot.valueRef, hvl]
      simp only [u32]
      rw [leN4 (fun b => ev tr 3 r pub (x b))
        (fun b hb => hx b (by omega)), hh]
      simp only [h1, decide_true, Nat.sub_self, Nat.mul_zero, List.append_assoc]
      rfl
  · -- an extension
    have h0 : ev tr 3 r pub (Sn.c "isL") = 0 := by omega
    have hpl32 : payLen tr pub r = 32 := by unfold payLen; omega
    have hx : ∀ t, t < 32 → ev tr 3 r pub (x t) < 256 := fun t ht => hpay t (by omega)
    have hch : refOf (nE tr pub r xf) ((pack2 x).map (nE tr pub r)) =
        .dig (bytesOf ((pack2 x).map (nE tr pub r))) :=
      refOf_dig' _ _ (by simp [pack2]) (hxf h1)
    have hh : bytesOf ((pack2 x).map (nE tr pub r)) = (List.range 32).map fun j => UInt8.ofNat (ev tr 3 r pub (x j)) :=
      bytesOf_pack3 x hx
    have hhl : (bytesOf ((pack2 x).map (nE tr pub r))).length = 32 := by rw [hh]; simp
    simp only [gRecK, h1, ↓reduceIte, hch]
    refine ⟨trivial, ?_, ⟨_, rfl⟩, ?_⟩
    · simp only [Rec.toP, Ref.toP, PTrie.wf, hnib, hhl, memS_lt hmb, Bool.true_and, decide_true,
        beq_self_eq_true, Bool.and_true]
      simp only [h1, decide_false] at hlen
      rw [hlen]; (try simp) <;> omega
    · simp only [Rec.toP, Ref.toP, PTrie.hashOf]
      congr 1
      rw [hhead, hpl32, hh]
      simp only [h1, decide_false, h0, Nat.sub_zero, Nat.mul_one, List.append_assoc]
      rfl

end

end StateM5a.SnContRec3
