import NearSpecV3.E2E.Boundary

/-!
# FinalM5d.S384Rec — SHA-384 as a fold of compressions over the padded blocks (record level)

`sha384_of_blocks`: if the 128-byte blocks `bs` concatenate to the FIPS padding of `m`, then
lane E's `sha384 m` is the first 48 big-endian bytes of `foldl compress IV384 bs` — the `S384`
table's chain (`hin` = IV384 on a first block, the previous `hout` otherwise, `hout =
compress(hin, block)` from the chip) read off the last block. What is open at field level: the
`S384` rows' blocks are the padding of the received bytes (flag / marker / length constraints),
and each row's 16 `IF384` receives are a chip compression (lane B's `Sha512If.comp_sound`).
-/

namespace FinalM5d.S384Rec

open NearSpecV3 NearSpecV3.E2E.Bnd

theorem blocks_flatten : ∀ (bs : List (List Nat)) (h : List Nat),
    (∀ b ∈ bs, b.length = 128) →
    SHA512.blocks bs.length h bs.flatten = bs.foldl SHA512.compress h
  | [], h, _ => by simp [SHA512.blocks]
  | b :: bs, h, hb => by
    have hb0 := hb b List.mem_cons_self
    have ih := blocks_flatten bs (SHA512.compress h b) (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    simp only [List.length_cons, List.flatten_cons, List.foldl_cons]
    have hne : b ++ bs.flatten ≠ [] := by
      intro e; have := congrArg List.length e; simp [hb0] at this
    rw [SHA512.blocks]
    · rw [List.take_left' hb0, List.drop_left' hb0, ih]
    · exact hne

theorem flatten_length : ∀ (bs : List (List Nat)), (∀ b ∈ bs, b.length = 128) →
    bs.flatten.length = 128 * bs.length
  | [], _ => rfl
  | b :: bs, hb => by
    have := flatten_length bs (fun x hx => hb x (List.mem_cons_of_mem _ hx))
    simp only [List.flatten_cons, List.length_append, hb b List.mem_cons_self, this,
      List.length_cons]
    omega

/-- **SHA-384 from the block chain.** -/
theorem sha384_of_blocks (m : ArenaCore.Bytes) (bs : List (List Nat))
    (hb : ∀ b ∈ bs, b.length = 128) (hp : bs.flatten = SHA512.pad (m.map UInt8.toNat)) :
    sha384 m = (SHA512.digestBytes (bs.foldl SHA512.compress IV384)).take 48 := by
  unfold sha384
  simp only
  rw [← hp, flatten_length bs hb, Nat.mul_div_cancel_left _ (by decide), blocks_flatten bs _ hb]

end FinalM5d.S384Rec
