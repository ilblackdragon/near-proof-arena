import StateM5a.SnRec

/-!
# StateM5a.SnContRec1 — records of any key length, and decoding a `hexPrefix` (pure)

* `gRecK K x xf mb`: `SnRec.gRecS` with the key `K` given (`gRecS = gRecK snKey`, `gRecK_snKey`);
  a continued head's record is `gRecK` of its full key;
* `hpDec B odd`: the nibbles a `hexPrefix` byte list `B` encodes; **`hexPrefix_hpDec`**: when `B`
  is bytes and its first byte is `32·leaf + odd·(16 + n)` (`n < 16`), `hexPrefix (hpDec B odd)
  leaf` is `B`, the nibbles are `< 16`, and there are `2·(|B| − 1) + odd` of them;
* **`hashed_leaf`** / **`hashed_ext`**: a leaf / extension record over any key, with the widths in
  range, is `Hashed` to the SHA-256 of its serialization.
-/

namespace StateM5a.SnContRec1

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.Store StateM5a.BusWalk NearSpec StateM5a.RowDec
open StateM5a.FieldRows StateM5a.SnSer StateM5a.RowSnMsg StateM5a.SnRec

/-! ## Records over a given key -/

section
variable (tr : Trace Fp) (pub : List Fp) (r : Nat)

/-- **The record** an `SN` row's columns spell, over the key `K`. -/
def gRecK (K : List Nat) (x : Nat → Expr) (xf : Expr) (mb : Nat → Expr) : Rec :=
  if ev tr 3 r pub (Sn.c "isL") = 1 then
    .leaf K (.ref (ev tr 3 r pub (Sn.vlenOf x)) (bytesOf ((pack2 fun b => x (4 + b)).map (nE tr pub r))))
      (memS tr pub r mb)
  else .ext K (refOf (nE tr pub r xf) ((pack2 x).map (nE tr pub r))) (memS tr pub r mb)

theorem gRecK_snKey (x : Nat → Expr) (xf : Expr) (mb : Nat → Expr) :
    gRecK tr pub r (snKey tr pub r) x xf mb = gRecS tr pub r x xf mb := rfl

end

/-! ## Decoding a `hexPrefix` -/

/-- The nibbles a `hexPrefix` byte list encodes (`odd`: the key length's parity). -/
def hpDec (B : List Nat) (odd : Nat) : List Nat :=
  (if odd = 1 then [B.headD 0 % 16] else []) ++ B.tail.flatMap fun b => [b / 16, b % 16]

theorem pack_flat : ∀ (bs : List Nat), (∀ b ∈ bs, b < 256) →
    (packNibbles (bs.flatMap fun b => [b / 16, b % 16])).map UInt8.toNat = bs
  | [], _ => rfl
  | b :: bs, h => by
    have hb : b < 256 := h b (by simp)
    have ih := pack_flat bs (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, packNibbles, List.map_cons] at ih ⊢
    rw [ih]
    congr 1
    rw [UInt8.toNat_ofNat']
    omega

theorem flat_len : ∀ (bs : List Nat), (bs.flatMap fun b => [b / 16, b % 16]).length = 2 * bs.length
  | [] => rfl
  | b :: bs => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, flat_len bs]
    omega

theorem flat_nib : ∀ (bs : List Nat), (∀ b ∈ bs, b < 256) →
    ∀ x ∈ bs.flatMap (fun b => [b / 16, b % 16]), x < 16 := by
  intro bs h x hx
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨b, hb, rfl | rfl⟩ := hx
  · have := h b hb; omega
  · omega

/-- **`hexPrefix` of the decoded nibbles is `B`.** -/
theorem hexPrefix_hpDec (B : List Nat) (leaf : Bool) (odd n : Nat) (ho : odd ≤ 1) (hn : n < 16)
    (hB : ∀ b ∈ B, b < 256) (hne : B ≠ [])
    (h0 : B.headD 0 = 32 * (if leaf then 1 else 0) + odd * (16 + n)) :
    (hexPrefix (hpDec B odd) leaf).map UInt8.toNat = B ∧ nibblesOk (hpDec B odd) = true ∧
      (hpDec B odd).length = 2 * (B.length - 1) + odd := by
  obtain ⟨b0, bs, rfl⟩ : ∃ b0 bs, B = b0 :: bs := by
    cases B with
    | nil => exact absurd rfl hne
    | cons b0 bs => exact ⟨b0, bs, rfl⟩
  have hb0 : b0 < 256 := hB b0 (by simp)
  have hbs : ∀ b ∈ bs, b < 256 := fun b hb => hB b (by simp [hb])
  simp only [List.headD_cons] at h0
  have hfl := flat_len bs
  have hfn := flat_nib bs hbs
  have hpk := pack_flat bs hbs
  rcases (by omega : odd = 0 ∨ odd = 1) with rfl | rfl
  · simp only [hpDec, List.tail_cons, Nat.zero_ne_one, ↓reduceIte, List.nil_append]
    refine ⟨?_, ?_, by simp [hfl]⟩
    · have hev : (bs.flatMap fun b => [b / 16, b % 16]).length % 2 = 0 := by omega
      have hp : hexPrefix (bs.flatMap fun b => [b / 16, b % 16]) leaf =
          UInt8.ofNat (if leaf then 32 else 0) :: packNibbles (bs.flatMap fun b => [b / 16, b % 16]) := by
        generalize (bs.flatMap fun b => [b / 16, b % 16]) = k at hev
        cases k with
        | nil => rfl
        | cons n rest =>
          unfold hexPrefix
          rw [hev]
          rfl
      rw [hp, List.map_cons, hpk]
      congr 1
      cases leaf <;> simp at h0 ⊢ <;> omega
    · simp only [nibblesOk, List.all_eq_true, decide_eq_true_eq]
      exact hfn
  · simp only [hpDec, List.tail_cons, ↓reduceIte, List.headD_cons, List.singleton_append]
    refine ⟨?_, ?_, by simp [hfl]⟩
    · have hodd : (b0 % 16 :: bs.flatMap fun b => [b / 16, b % 16]).length % 2 = 1 := by
        simp only [List.length_cons]; omega
      have hp : hexPrefix (b0 % 16 :: bs.flatMap fun b => [b / 16, b % 16]) leaf =
          UInt8.ofNat (16 + b0 % 16 + (if leaf then 32 else 0)) ::
            packNibbles (bs.flatMap fun b => [b / 16, b % 16]) := by
        unfold hexPrefix
        rw [hodd]
        rfl
      rw [hp, List.map_cons, hpk]
      congr 1
      rw [UInt8.toNat_ofNat']
      cases leaf <;> simp at h0 ⊢ <;> omega
    · simp only [nibblesOk, List.all_cons, List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true]
      exact ⟨by omega, hfn⟩

/-! ## Hashed records over any key -/

theorem hashed_leaf (K : List Nat) (vlen : Nat) (vh : Bytes) (mem : Nat) (hK : nibblesOk K = true)
    (hv : vlen < 4294967296) (hh : vh.length = 32) (hm : mem < 18446744073709551616)
    (hl : (hexPrefix K true).length < 4294967296) :
    Hashed (.leaf K (.ref vlen vh) mem)
      (sha256 ([0] ++ u32 (hexPrefix K true).length ++ hexPrefix K true ++ (u32 vlen ++ vh) ++ u64 mem)) := by
  refine ⟨trivial, ?_, ⟨_, _, rfl⟩, rfl⟩
  simp [Rec.toP, PTrie.wf, slotOk, hK, hv, hh, hm, hl]

theorem hashed_ext (K : List Nat) (h : Bytes) (mem : Nat) (hK : nibblesOk K = true)
    (hh : h.length = 32) (hm : mem < 18446744073709551616)
    (hl : (hexPrefix K false).length < 4294967296) :
    Hashed (.ext K (.dig h) mem)
      (sha256 ([3] ++ u32 (hexPrefix K false).length ++ hexPrefix K false ++ h ++ u64 mem)) := by
  refine ⟨trivial, ?_, ⟨_, rfl⟩, rfl⟩
  simp [Rec.toP, Ref.toP, PTrie.wf, hK, hh, hm, hl]

end StateM5a.SnContRec1
