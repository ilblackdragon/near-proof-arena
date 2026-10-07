import ZkFormal.NearV3.Public.HeaderBinding

namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra NearSpec NearSpecV3

theorem prep_tag_prefix_length : (borshBytes prepTag).length = 26 := by decide +kernel

theorem header_implicit_count (p : Prep) (witnessOverhead : Nat) {k : Nat} (hk : k < 4) :
    (headerBytes p witnessOverhead).getD (26+k) 0 = (u32 p.hdr.K).getD k 0 := by
  simp only [headerBytes,PrepHdr.encode,List.append_assoc]
  rw [show 26+k = (borshBytes prepTag).length+k by rw [prep_tag_prefix_length]]
  rw [getD_right]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa [u32,leN_length] using hk)]

theorem prepared_implicit_count (p : Prep) (witnessOverhead : Nat) (hr : RootsSized p)
    (hK : p.hdr.K < 256^4) :
    V2.leNat ((List.range 4).map (fun k => PubVal.val
      ((ZkFormal.Udr.pubOf Fp (preparedBytes p witnessOverhead)).getD (26+k) 0))) =
      p.hdr.K := by
  apply read4_u32 _ _ hK
  intro k hk
  rw [pub_getD,prepared_header p witnessOverhead hr (by omega),
    header_implicit_count p witnessOverhead hk]

end ZkFormal.NearV3.Public
