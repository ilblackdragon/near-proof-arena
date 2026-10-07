import ZkFormal.V2.IndexedPublic
import ZkFormal.V2.Verifier
import ZkFormal.Udr.Rbr
import NearSpec.ClaimCodec

/-! Byte-level prepared-statement lemmas for indexed public segments. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.Algebra ZkFormal.V2

abbrev byteF (b : UInt8) : Fp := Fp.ofNat b.toNat

theorem byteF_val (b : UInt8) : PubVal.val (byteF b) = b.toNat := by
  change (Fp.ofNat b.toNat).toNat = b.toNat
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (by have := b.toNat_lt; unfold ZkFormal.Algebra.P; omega)]

theorem pub_getD (bs : List UInt8) (i : Nat) :
    (ZkFormal.Udr.pubOf Fp bs).getD i 0 = byteF (bs.getD i 0) := by
  simp only [ZkFormal.Udr.pubOf,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases bs[i]? <;> rfl

theorem leNat_bytes (bs : List UInt8) : V2.leNat (bs.map UInt8.toNat) = NearSpec.leNat bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [V2.leNat,NearSpec.leNat,ih]

/-- Decode a checked u32 field without assuming the AIR message count. -/
theorem read4_u32 (read : Nat → Fp) (x : Nat) (hx : x < 256 ^ 4)
    (hread : ∀ k, k < 4 → read k = byteF ((NearSpec.u32 x).getD k 0)) :
    V2.leNat ((List.range 4).map (fun k => PubVal.val (read k))) = x := by
  have hm : (List.range 4).map (fun k => PubVal.val (read k)) =
      (NearSpec.u32 x).map UInt8.toNat := by
    apply List.ext_getElem (by simp [NearSpec.u32,NearSpec.leN_length])
    intro k hk hk'
    have hk4 : k < 4 := by simpa using hk
    simp only [List.getElem_map,List.getElem_range]
    rw [hread k hk4,byteF_val,List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa [NearSpec.u32,NearSpec.leN_length] using hk4),Option.getD_some]
  rw [hm,leNat_bytes]
  exact NearSpec.leNat_leN 4 x hx

theorem count_of_u32 (s : PubSeg) (pub : List Fp) (x : Nat) (hx : x < 256 ^ 4)
    (h : ∀ k, k < 4 → pub.getD (s.countAt+k) 0 = byteF ((NearSpec.u32 x).getD k 0)) :
    s.count pub = x := read4_u32 _ x hx h

theorem offset_of_u32 (s : PubSeg) (pub : List Fp) (offsetAt x : Nat)
    (ha : s.startAt = some offsetAt) (hx : x < 256 ^ 4)
    (h : ∀ k, k < 4 → pub.getD (offsetAt+k) 0 = byteF ((NearSpec.u32 x).getD k 0)) :
    s.startOffset pub = x := by
  simp only [PubSeg.startOffset,ha]
  exact read4_u32 _ x hx h

end ZkFormal.NearV3.Public
