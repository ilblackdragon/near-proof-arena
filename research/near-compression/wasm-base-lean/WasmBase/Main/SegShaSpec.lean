import WasmBase.Main.SegSend
import StateM5a.Sha512If

/-!
# WasmBase.Main.SegShaSpec — SHA-384 as chained word-level compressions (E2E M4b)

The native chip computes FIPS 180-4's SHA-512 compression on a block of 16 64-bit words.  The
spec's compression `NearSpecV3.SHA512.compress h block` takes the block as 128 **byte values**, so
the chip's function is

  `compressW h ws = SHA512.compress h (wbv ws)`,  `wbv ws` = the big-endian bytes of the words,

and `compressW_ok : CompressOK compressW` (lane B's output shape: 8 words `< 2^64`).

* `sha384_blocks`: if the FIPS padding of a message is the bytes of the blocks `Bs` (16 words each),
  `sha384 m` is the bytes of the first 6 words of `Bs.foldl compressW IV384`.
* `pad_whole`: a message of whole 1024-bit blocks (`16·n` words) is padded by the one block
  `padBlk (64·#words)` = `0x8000…0 ‖ 0^13 ‖ len_hi ‖ len_lo` (length in bits).
* `pad_96`: a 96-byte message (two 48-byte digests) is padded by lane B's `padW = [2^63, 0, 0, 768]`.
* `sha384_node`, `nodeH_sha384`: lane B's node hash `nodeH compressW a b` is SHA-384 of
  `left48 ‖ right48` (the bytes of the two digests).
* `sha384_whole`: SHA-384 of `16·n` words is the chain of the `n` data blocks and `padBlk`.

Bytes are `ArenaCore.Bytes` (`List UInt8`); a word's bytes are `Bytes.beN 8` (big-endian), which is
how `SHA512.digestBytes` writes the hash words.
-/

namespace WasmBase
namespace SegSha

open NearSpecV3 ArenaCore StateM5a.Sha512If
set_option linter.unusedSimpArgs false

/-! ## Word bytes -/

/-- The big-endian bytes of a word list. -/
def wbytes (ws : List Nat) : Bytes := ws.flatMap (Bytes.beN 8)

/-- The same as byte values (the input of `SHA512.compress` / `SHA512.pad`). -/
def wbv (ws : List Nat) : List Nat := (wbytes ws).map UInt8.toNat

theorem wbytes_append (a b : List Nat) : wbytes (a ++ b) = wbytes a ++ wbytes b := by
  simp [wbytes]

theorem wbv_append (a b : List Nat) : wbv (a ++ b) = wbv a ++ wbv b := by
  simp [wbv, wbytes_append]

theorem wbytes_length (ws : List Nat) : (wbytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [wbytes, List.flatMap_cons, List.length_append, Bytes.beN_length] at ih ⊢
    rw [ih]; simp; omega

theorem wbv_length (ws : List Nat) : (wbv ws).length = 8 * ws.length := by
  simp [wbv, wbytes_length]

/-- **The chip's compression**: FIPS 180-4 SHA-512 compression of the block whose bytes are the
big-endian bytes of the 16 words. -/
def compressW (h ws : List Nat) : List Nat := SHA512.compress h (wbv ws)

theorem compressW_ok : CompressOK compressW := by
  intro h b
  refine ⟨rfl, ?_⟩
  intro w hw
  simp only [compressW, SHA512.compress, SHA512.add64, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Nat.mod_lt _ (by decide)

/-! ## Chained blocks -/

theorem blocks_wbv (h : List Nat) : ∀ (Bs : List (List Nat)), (∀ B ∈ Bs, B.length = 16) →
    SHA512.blocks Bs.length h (wbv Bs.flatten) = Bs.foldl compressW h := by
  intro Bs
  induction Bs generalizing h with
  | nil => intro _; rfl
  | cons B Bs ih =>
    intro hB
    have hl : (wbv B).length = 128 := by rw [wbv_length, hB B List.mem_cons_self]
    rw [List.flatten_cons, wbv_append, List.length_cons, List.foldl_cons]
    obtain ⟨x, xs, hx⟩ : ∃ x xs, wbv B = x :: xs := by
      cases e : wbv B with
      | nil => rw [e] at hl; simp at hl
      | cons x xs => exact ⟨x, xs, rfl⟩
    have step : SHA512.blocks (Bs.length + 1) h (wbv B ++ wbv Bs.flatten) =
        SHA512.blocks Bs.length (SHA512.compress h ((wbv B ++ wbv Bs.flatten).take 128))
          ((wbv B ++ wbv Bs.flatten).drop 128) := by
      rw [hx]; rfl
    rw [step, List.take_left' hl, List.drop_left' hl]
    exact ih _ (fun B' hB' => hB B' (List.mem_cons_of_mem _ hB'))

theorem take_wbytes : ∀ (k : Nat) (L : List Nat), (wbytes L).take (8 * k) = wbytes (L.take k)
  | 0, L => by simp [wbytes]
  | k + 1, [] => by simp [wbytes]
  | k + 1, w :: L => by
    have e : wbytes (w :: L) = Bytes.beN 8 w ++ wbytes L := rfl
    rw [e, show 8 * (k + 1) = 8 + 8 * k by omega, List.take_append, List.take_of_length_le
      (by rw [Bytes.beN_length]; omega), Bytes.beN_length, show 8 + 8 * k - 8 = 8 * k by omega,
      take_wbytes k L]
    rfl

/-- **SHA-384 as chained compressions.** -/
theorem sha384_blocks (m : Bytes) (Bs : List (List Nat)) (hB : ∀ B ∈ Bs, B.length = 16)
    (hp : SHA512.pad (m.map UInt8.toNat) = wbv Bs.flatten) :
    E2E.Bnd.sha384 m = wbytes ((Bs.foldl compressW E2E.Bnd.IV384).take 6) := by
  have hlen : (wbv Bs.flatten).length / 128 = Bs.length := by
    rw [wbv_length, List.length_flatten]
    have : (Bs.map List.length).sum = 16 * Bs.length := by
      clear hp
      induction Bs with
      | nil => rfl
      | cons B Bs ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [hB B List.mem_cons_self, ih (fun B' hB' => hB B' (List.mem_cons_of_mem _ hB'))]; omega
    rw [this]; omega
  simp only [E2E.Bnd.sha384, hp, hlen, blocks_wbv _ Bs hB]
  rw [show (48 : Nat) = 8 * 6 from rfl, ← take_wbytes]
  rfl

/-! ## Padding -/

theorem beN_mod : ∀ (w n : Nat), Bytes.beN w n = Bytes.beN w (n % 256 ^ w)
  | 0, _ => rfl
  | w + 1, n => by
    show Bytes.beN w (n / 256) ++ [UInt8.ofNat (n % 256)] =
      Bytes.beN w (n % 256 ^ (w + 1) / 256) ++ [UInt8.ofNat (n % 256 ^ (w + 1) % 256)]
    rw [beN_mod w (n / 256), beN_mod w (n % 256 ^ (w + 1) / 256)]
    have e1 : n / 256 % 256 ^ w = n % 256 ^ (w + 1) / 256 % 256 ^ w := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self, Nat.mod_mod]
    have e2 : n % 256 ^ (w + 1) % 256 = n % 256 := by
      rw [Nat.pow_succ, Nat.mod_mul_left_mod]
    rw [e1, e2]

theorem beN_add : ∀ (a b n : Nat), Bytes.beN (a + b) n = Bytes.beN a (n / 256 ^ b) ++ Bytes.beN b n
  | a, 0, n => by simp [Bytes.beN]
  | a, b + 1, n => by
    show Bytes.beN (a + b) (n / 256) ++ [UInt8.ofNat (n % 256)] =
      Bytes.beN a (n / 256 ^ (b + 1)) ++ (Bytes.beN b (n / 256) ++ [UInt8.ofNat (n % 256)])
    rw [beN_add a b (n / 256), Nat.div_div_eq_div_mul, ← Nat.pow_succ', List.append_assoc]

/-- The padding block of a message of whole blocks, `x` = its length in bits. -/
def padBlk (x : Nat) : List Nat := 2 ^ 63 :: List.replicate 13 0 ++ [x / 2 ^ 64 % 2 ^ 64, x % 2 ^ 64]

theorem padBlk_length (x : Nat) : (padBlk x).length = 16 := by simp [padBlk]

theorem padBlk_tail (x : Nat) :
    [0x80] ++ List.replicate 111 0 ++ (Bytes.beN 16 x).map UInt8.toNat = wbv (padBlk x) := by
  have e16 : Bytes.beN 16 x = Bytes.beN 8 (x / 2 ^ 64 % 2 ^ 64) ++ Bytes.beN 8 (x % 2 ^ 64) := by
    rw [show (16 : Nat) = 8 + 8 from rfl, beN_add, beN_mod 8 (x / 256 ^ 8), beN_mod 8 x]
  rw [e16]
  simp only [wbv, wbytes, padBlk, List.cons_append, List.flatMap_cons, List.flatMap_append,
    List.map_append, List.flatMap_nil, List.append_nil]
  have hz : (List.replicate 13 0).flatMap (Bytes.beN 8) = List.replicate 104 (0 : UInt8) := by decide
  rw [hz]
  have h63 : (Bytes.beN 8 (2 ^ 63)).map UInt8.toNat = [0x80, 0, 0, 0, 0, 0, 0, 0] := by decide
  simp only [List.map_append, h63, List.map_replicate]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  rfl

/-- **Padding of whole blocks** (FIPS 180-4 §5.1.2 with `len ≡ 0 mod 1024`). -/
theorem pad_whole (ws : List Nat) (hlen : ws.length % 16 = 0) :
    SHA512.pad (wbv ws) = wbv (ws ++ padBlk (64 * ws.length)) := by
  have hk : (239 - 8 * ws.length % 128) % 128 = 111 := by omega
  simp only [SHA512.pad, wbv_length, hk]
  rw [wbv_append, ← padBlk_tail, show 8 * (8 * ws.length) = 64 * ws.length by omega]
  simp only [List.append_assoc]

/-- **Padding of 96 bytes** (one node block: lane B's `padW`). -/
theorem pad_96 (ws : List Nat) (hlen : ws.length = 12) :
    SHA512.pad (wbv ws) = wbv (ws ++ padW) := by
  simp only [SHA512.pad, wbv_length, hlen]
  rw [wbv_append]
  simp only [List.append_assoc]
  congr 1

/-! ## SHA-384 of a node and of whole blocks -/

theorem iv_eq : StateM5a.IV384 = E2E.Bnd.IV384 := rfl

theorem iv_eq' : Chips.Seg.IV384 = E2E.Bnd.IV384 := rfl

/-- **The Merkle node hash is SHA-384 of `left48 ‖ right48`** (word level). -/
theorem sha384_node (l r : List Nat) (hl : l.length = 6) (hr : r.length = 6) :
    E2E.Bnd.sha384 (wbytes (l ++ r)) = wbytes ((compressW E2E.Bnd.IV384 (l ++ r ++ padW)).take 6) := by
  have := sha384_blocks (wbytes (l ++ r)) [l ++ r ++ padW] (by simp [hl, hr, padW])
    (by simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
        exact pad_96 (l ++ r) (by simp [hl, hr]))
  simpa using this

theorem take6_eq_digest6 {x : List Nat} (hx : x.length = 8) (hw : W64 x) :
    (digest6 x).1 = x.take 6 := by
  obtain ⟨o, ox, e, ho⟩ : ∃ o ox, x = o ++ ox ∧ o.length = 6 :=
    ⟨x.take 6, x.drop 6, (List.take_append_drop 6 x).symm, by simp [hx]⟩
  have hwo : W64 o := fun w hw' => hw w (by rw [e]; exact List.mem_append_left _ hw')
  rw [digest6_eq e ho hwo, e, List.take_left' ho]

/-- **Lane B's `nodeH` with the chip's compression is SHA-384 of the two children's bytes.** -/
theorem nodeH_sha384 (a b : Dig) :
    wbytes (nodeH compressW a b).1 = E2E.Bnd.sha384 (wbytes (a.1 ++ b.1)) := by
  rw [sha384_node a.1 b.1 a.2.1 b.2.1, nodeH, take6_eq_digest6 (compressW_ok _ _).1 (compressW_ok _ _).2]
  rfl

/-- Cut a word list into consecutive 16-word blocks. -/
def chunks16 : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | n + 1, ws => ws.take 16 :: chunks16 n (ws.drop 16)

theorem chunks16_spec : ∀ (n : Nat) (ws : List Nat), ws.length = 16 * n →
    (chunks16 n ws).flatten = ws ∧ ∀ B ∈ chunks16 n ws, B.length = 16
  | 0, ws, h => by simp [chunks16]; exact List.eq_nil_of_length_eq_zero (by omega)
  | n + 1, ws, h => by
    obtain ⟨ih1, ih2⟩ := chunks16_spec n (ws.drop 16) (by simp; omega)
    refine ⟨?_, ?_⟩
    · simp only [chunks16, List.flatten_cons, ih1, List.take_append_drop]
    · intro B hB
      simp only [chunks16, List.mem_cons] at hB
      rcases hB with rfl | hB
      · simp; omega
      · exact ih2 B hB

/-- **SHA-384 of whole blocks**: the message of `16·n` words is the chain of its `n` blocks and the
padding block. -/
theorem sha384_whole (n : Nat) (ws : List Nat) (hlen : ws.length = 16 * n) :
    E2E.Bnd.sha384 (wbytes ws) =
      wbytes ((compressW ((chunks16 n ws).foldl compressW E2E.Bnd.IV384) (padBlk (1024 * n))).take 6) := by
  obtain ⟨h1, h2⟩ := chunks16_spec n ws hlen
  have := sha384_blocks (wbytes ws) (chunks16 n ws ++ [padBlk (1024 * n)])
    (by
      intro B hB
      simp only [List.mem_append, List.mem_singleton] at hB
      rcases hB with hB | rfl
      · exact h2 B hB
      · exact padBlk_length _)
    (by
      rw [List.flatten_append, h1]
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
      have := pad_whole ws (by omega)
      rw [hlen] at this
      rw [show 1024 * n = 64 * (16 * n) by omega]
      exact this)
  rw [this, List.foldl_append]
  rfl

end SegSha
end WasmBase
