import ZkFormal.NearV3.Public.Source
import ZkFormal.NearV3.Rcpt.Tables.Size

/-! Candidate packed-statement header. The witness encoding overhead must be
supplied by the verified native preparation step; it is not a prover-chosen field. -/
namespace ZkFormal.NearV3.Public
open NearSpec NearSpecV3

private theorem byteArray_loop_length (bs : ByteArray) (i : Nat) (r : List UInt8) :
    (ByteArray.toList.loop bs i r).length = bs.size-i+r.length := by
  rw [ByteArray.toList.loop]
  split
  · rw [byteArray_loop_length bs (i+1) _]
    simp only [List.length_cons]
    omega
  · simp only [List.length_reverse]
    omega
termination_by bs.size-i

private theorem byteArray_toList_length (bs : ByteArray) : bs.toList.length = bs.size := by
  simpa only [ByteArray.toList,Nat.sub_zero,List.length_nil,Nat.add_zero] using
    byteArray_loop_length bs 0 []

/-- Preserve the existing static AIR offsets, and add body length and witness overhead. -/
def headerBytes (p : Prep) (witnessOverhead : Nat) : ByteString :=
  borshBytes prepTag ++ p.hdr.encode ++ u32 p.body.length ++ u32 witnessOverhead

def RootsSized (p : Prep) : Prop :=
  p.hdr.prevStateRoot.length = 32 ∧ p.hdr.postStateRoot.length = 32 ∧
    p.hdr.outcomeRoot.length = 32

theorem oldHeader_length (p : Prep) (hr : RootsSized p) :
    (borshBytes prepTag ++ p.hdr.encode).length = 194 := by
  obtain ⟨hpre,hpost,hout⟩ := hr
  simp [borshBytes,PrepHdr.encode,u32,u64,u128,leN_length,hpre,hpost,hout,prepTag]
  rw [byteArray_toList_length,String.size_toByteArray]
  decide

theorem headerBytes_length (p : Prep) (witnessOverhead : Nat) (hr : RootsSized p) :
    (headerBytes p witnessOverhead).length = 202 := by
  unfold headerBytes
  simp only [List.length_append,u32,leN_length]
  have h := oldHeader_length p hr
  simp only [List.length_append] at h
  omega

theorem header_body_length (p : Prep) (witnessOverhead : Nat) (hr : RootsSized p)
    {k : Nat} (hk : k < 4) :
    (headerBytes p witnessOverhead).getD (PH_BLEN+k) 0 = (u32 p.body.length).getD k 0 := by
  unfold headerBytes
  rw [show PH_BLEN+k = (borshBytes prepTag ++ p.hdr.encode).length+k by rw [oldHeader_length p hr]; rfl]
  exact getD_middle _ _ _ (by simpa [u32,leN_length] using hk)

theorem header_witness_overhead (p : Prep) (witnessOverhead : Nat) (hr : RootsSized p)
    (k : Nat) :
    (headerBytes p witnessOverhead).getD (SizeV3.PH_WOVH+k) 0 = (u32 witnessOverhead).getD k 0 := by
  unfold headerBytes
  rw [show SizeV3.PH_WOVH+k = (borshBytes prepTag ++ p.hdr.encode ++ u32 p.body.length).length+k by
    rw [List.length_append,oldHeader_length p hr]; simp [u32,leN_length,SizeV3.PH_WOVH]]
  exact getD_right _ _ k

end ZkFormal.NearV3.Public
