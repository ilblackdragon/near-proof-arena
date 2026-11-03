import StateM5a.BrVl
import StateM5a.RowSnN

/-!
# StateM5a.SnSer — an `SN` row's SHA-256 byte sends spell its node's serialization

`Trie.Sn.serBytes id g x mb` sends a leaf / extension node to `SHA_BYTES`: the tag `3·isE`, the
`u32` hex-prefix length (`hplen, 0, 0, 0`), the hex-prefix bytes `hp_m` (`ha_m`), the payload
(`x_t`, 36 bytes for a leaf, 32 for an extension) and the memory bytes.  For a head whose key does
not continue (`cont = 0`) all of them come from the row (the `SNC` rows send the rest of a long
key), so:

* `snSerF`: the intended serialization as field elements, of length `serLen = 45 + hplen + 4·isL`;
* **`sn_ser_ok`**: every byte send that fires sits at a position `p < |snSerF|` and carries
  `snSerF[p]` (`ha_m = [m < hplen]`, `FieldRows2.sn_ha`/`sn_hplen`).

Generic in the payload / memory columns, so the old node (`x`, `mem`) and the new node (`nx`,
`nmem`) are both instances.
-/

namespace StateM5a.SnSer

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.KcChain

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable (tr : Trace Fp) (pub : List Fp) (r : Nat)

/-- Field values on `SN` row `r`. -/
abbrev nE (e : Expr) : Fp := e.eval tr 3 r pub

/-- The payload length: 36 (leaf) or 32 (extension). -/
def payLen : Nat := 32 + 4 * ev tr 3 r pub (Sn.c "isL")

/-- **The serialization** an `SN` head's byte sends spell (`cont = 0`). -/
def snSerF (x mb : Nat → Expr) : List Fp :=
  [nE tr pub r (sm 3 (Sn.c "isE")), nE tr pub r (Sn.c "hplen"), nE tr pub r 0, nE tr pub r 0, nE tr pub r 0] ++
    (List.range (ev tr 3 r pub (Sn.c "hplen"))).map (fun m => nE tr pub r (Sn.c "hp" m)) ++
    (List.range (payLen tr pub r)).map (fun t => nE tr pub r (x t)) ++
    (List.range 8).map (fun b => nE tr pub r (mb b))

end

section
variable {tr : Trace Fp} {pub : List Fp} {r : Nat}

theorem snSerF_length {x mb : Nat → Expr} :
    (snSerF tr pub r x mb).length = 45 + ev tr 3 r pub (Sn.c "hplen") + 4 * ev tr 3 r pub (Sn.c "isL") := by
  simp only [snSerF, payLen, List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range]
  omega

theorem ev3_K (n : Nat) : ev tr 3 r pub (K n) = n % P := ev_const n
theorem ev3_sm (v : Nat) (e : Expr) : ev tr 3 r pub (sm v e) = (v % P) * ev tr 3 r pub e % P := by
  show ev tr 3 r pub (Expr.mul (.const v) e) = _
  rw [ev_mul, ev_const]

theorem ev3_byte2 (a b : Expr) (ha : ev tr 3 r pub a < 256) (hb : ev tr 3 r pub b < 256) :
    ev tr 3 r pub (K 256 * a + b) = 256 * ev tr 3 r pub a + ev tr 3 r pub b := by
  rw [ev_hadd, ev_hmul, ev3_K, show 256 % P = 256 from rfl,
    Nat.mod_eq_of_lt (show 256 * ev tr 3 r pub a < P by omega),
    Nat.mod_eq_of_lt (show 256 * ev tr 3 r pub a + ev tr 3 r pub b < P by omega)]

/-- 32 bytes packed in 16-bit limbs and unpacked (`SN` rows). -/
theorem bytesOf_pack3 (v : Nat → Expr) (h : ∀ j, j < 32 → ev tr 3 r pub (v j) < 256) :
    bytesOf ((pack2 v).map (nE tr pub r)) = (List.range 32).map fun j => UInt8.ofNat (ev tr 3 r pub (v j)) := by
  unfold bytesOf pack2
  rw [List.map_map, List.map_map]
  have e : (List.range 16).map ((Fp.toNat ∘ nE tr pub r) ∘ fun i => K 256 * v (2 * i) + v (2 * i + 1)) =
      (List.range 16).map fun i => 256 * ev tr 3 r pub (v (2 * i)) + ev tr 3 r pub (v (2 * i + 1)) := by
    apply List.map_congr_left
    intro i hi
    have := List.mem_range.1 hi
    exact ev3_byte2 _ _ (h _ (by omega)) (h _ (by omega))
  rw [e, BrSer.limbBytes_pack (fun j => ev tr 3 r pub (v j)) 16 h]

theorem ev3_gate_one {g x : Expr} (hg : ev tr 3 r pub g = 1) (h : ev tr 3 r pub (g * x) = 1) :
    ev tr 3 r pub x = 1 := by
  rw [ev_hmul, hg, Nat.one_mul, Nat.mod_eq_of_lt (ev_lt _)] at h; exact h

theorem snSerF_hp {x mb : Nat → Expr} {m : Nat} (hm : m < ev tr 3 r pub (Sn.c "hplen")) :
    (snSerF tr pub r x mb)[5 + m]? = some (nE tr pub r (Sn.c "hp" m)) := by
  unfold snSerF
  rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by simp),
    List.getElem?_append_left (by simp; omega)]
  simp [hm]

theorem snSerF_x {x mb : Nat → Expr} {t : Nat} (ht : t < payLen tr pub r) :
    (snSerF tr pub r x mb)[5 + ev tr 3 r pub (Sn.c "hplen") + t]? = some (nE tr pub r (x t)) := by
  unfold snSerF
  rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp; omega)]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range,
    List.getElem?_map]
  rw [show 5 + ev tr 3 r pub (Sn.c "hplen") + t - (4 + 1) - ev tr 3 r pub (Sn.c "hplen") = t by omega]
  simp [ht]

theorem snSerF_mb {x mb : Nat → Expr} {b : Nat} (hb : b < 8) :
    (snSerF tr pub r x mb)[5 + ev tr 3 r pub (Sn.c "hplen") + payLen tr pub r + b]? =
      some (nE tr pub r (mb b)) := by
  unfold snSerF
  rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by simp; omega),
    List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range,
    List.getElem?_map]
  rw [show 5 + ev tr 3 r pub (Sn.c "hplen") + payLen tr pub r + b - (4 + 1) - ev tr 3 r pub (Sn.c "hplen") -
    payLen tr pub r = b by omega]
  simp [hb]

set_option maxHeartbeats 4000000 in
/-- **Every firing byte send of an `SN` head (`cont = 0`) carries its `snSerF` entry.** -/
theorem sn_ser_ok (hc : ∀ e ∈ Sn.table.constraints, e.eval tr 3 r pub = 0)
    (hA : ev tr 3 r pub (Sn.c "act") = 1) (hcont : ev tr 3 r pub (Sn.c "cont") = 0)
    {id g : Expr} {x mb : Nat → Expr} (hg : ev tr 3 r pub g = 1)
    {i : Interaction} (hi : i ∈ Sn.serBytes id g x mb) (hp : 0 < i.multNat tr 3 r pub) :
    ∃ pe ve, i.msg = [id, pe, ve] ∧ ev tr 3 r pub pe < (snSerF tr pub r x mb).length ∧
      (snSerF tr pub r x mb)[ev tr 3 r pub pe]? = some (nE tr pub r ve) := by
  have hlen := snSerF_length (tr := tr) (pub := pub) (r := r) (x := x) (mb := mb)
  have hL := FieldRows2.sn_bool hc "isL" (by simp)
  have hpl := FieldRows2.sn_hplen hc hA hcont
  have hkl := (FieldRows2.sn_flags hc hcont).1
  have hha := FieldRows2.sn_ha hc hA hcont
  have hpl33 : ev tr 3 r pub (Sn.c "hplen") ≤ 33 := by omega
  unfold Sn.serBytes at hi
  simp only [List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hi
  rcases hi with (((rfl | rfl | rfl | rfl | rfl) | ⟨m, hm, rfl⟩) | ⟨t, ht, rfl⟩) | ⟨b, hb, rfl⟩
  · exact ⟨_, _, rfl, by rw [show ev tr 3 r pub (0 : Expr) = 0 from ev_const 0]; omega,
      by rw [show ev tr 3 r pub (0 : Expr) = 0 from ev_const 0]; rfl⟩
  · exact ⟨_, _, rfl, by rw [show ev tr 3 r pub (1 : Expr) = 1 from ev_const 1]; omega,
      by rw [show ev tr 3 r pub (1 : Expr) = 1 from ev_const 1]; rfl⟩
  · exact ⟨_, _, rfl, by rw [show ev tr 3 r pub (2 : Expr) = 2 from ev_const 2]; omega,
      by rw [show ev tr 3 r pub (2 : Expr) = 2 from ev_const 2]; rfl⟩
  · exact ⟨_, _, rfl, by rw [show ev tr 3 r pub (3 : Expr) = 3 from ev_const 3]; omega,
      by rw [show ev tr 3 r pub (3 : Expr) = 3 from ev_const 3]; rfl⟩
  · exact ⟨_, _, rfl, by rw [show ev tr 3 r pub (4 : Expr) = 4 from ev_const 4]; omega,
      by rw [show ev tr 3 r pub (4 : Expr) = 4 from ev_const 4]; rfl⟩
  · have h1 := ev3_gate_one hg (eval_one_ev (multNat_one_bit rfl hp))
    have hm' : m < ev tr 3 r pub (Sn.c "hplen") := by
      have := hha m (by simp [HPMAX] at hm; omega)
      rw [h1] at this; split at this <;> omega
    refine ⟨_, _, rfl, ?_, ?_⟩
    · rw [ev3_K, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [ev3_K, Nat.mod_eq_of_lt (by omega)]; exact snSerF_hp hm'
  · have hpos : ev tr 3 r pub (5 + Sn.c "hplen" + K t) = 5 + ev tr 3 r pub (Sn.c "hplen") + t := by
      rw [ev_hadd, ev_hadd, show ev tr 3 r pub (5 : Expr) = 5 from ev_const 5, ev3_K]
      omega
    have htp : t < payLen tr pub r := by
      unfold payLen
      by_cases h32 : t < 32
      · omega
      · have h1 : ev tr 3 r pub (g * Sn.c "isL") = 1 := by
          have := eval_one_ev (multNat_one_bit (g := if t < 32 then g else g * Sn.c "isL") rfl hp)
          simpa [h32] using this
        rw [ev3_gate_one hg h1]; omega
    refine ⟨_, _, rfl, ?_, ?_⟩
    · rw [hpos]; unfold payLen at htp; omega
    · rw [hpos]; exact snSerF_x htp
  · have hpos : ev tr 3 r pub (37 + Sn.c "hplen" + sm 4 (Sn.c "isL") + K b) =
        5 + ev tr 3 r pub (Sn.c "hplen") + payLen tr pub r + b := by
      unfold payLen
      rw [ev_hadd, ev_hadd, ev_hadd, show ev tr 3 r pub (37 : Expr) = 37 from ev_const 37, ev3_sm, ev3_K]
      omega
    refine ⟨_, _, rfl, ?_, ?_⟩
    · rw [hpos]; unfold payLen; omega
    · rw [hpos]; exact snSerF_mb hb

end

end StateM5a.SnSer
