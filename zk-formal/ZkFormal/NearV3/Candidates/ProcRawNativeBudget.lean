import ZkFormal.NearV3.Candidates.ProcRawNativeLocal
import ZkFormal.NearV3.Assembly.ReadUnfoldBound
namespace ZkFormal.NearV3.Candidates.ProcRawNativeBudget
open NearSpec NearSpecV3 ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest
open ProcRawConcatGeometry

/-- Charge each parser to its own native prestate occurrence. Missing states
still consume their37-row framing block. No distinct-key assumption is used. -/
theorem block_bound (b : NativeBlock) (hb:b.Valid) :
    blockLength b≤unfoldedBytesT b.witness.pre+37 := by
  have hr:=hb.2.1
  have hd:=hb.2.2.2.1
  cases hp:b.prior with
  | none=>
    rw [hp] at hd
    have he:b.old=Bandwidth.State.initial := (Option.some.inj hd).symm
    simp [blockLength,ProcPriorRawSlots.length,he,Bandwidth.State.initial]
  | some bytes=>
    rw [hp] at hd hr
    have hl:=ProcPriorDecode.decode_length bytes b.old hd
    have hf:b.witness.pre.find keyBwState=some (some bytes) := by
      unfold readKey at hr
      split at hr <;> simp_all
    have hc:=find_value_unfolded hf
    unfold blockLength ProcPriorRawSlots.length
    omega

theorem total_bound (bs : List NativeBlock) (hb:∀b∈bs,b.Valid) :
    (rows bs).length≤preBytes (bs.map (fun b=>b.witness.pre))+37*bs.length := by
  induction bs with
  | nil=>simp [rows,preBytes]
  | cons b bs ih=>
    have hh:=block_bound b (hb b (by simp))
    have ht:=ih (fun b hm=>hb b (by simp [hm]))
    simp only [rows,List.flatMap_cons,List.length_append,block_length]
    simp only [preBytes,List.map_cons,List.sum_cons,List.length_cons] at ht ⊢
    change (bs.flatMap blockRows).length≤_ at ht
    omega

theorem capacity (bs : List NativeBlock) (hb:∀b∈bs,b.Valid)
    (hlen:bs.length≤32) (hbytes:preBytes (bs.map (fun b=>b.witness.pre))≤2000000) :
    (rows bs).length<2^22 := by
  have:=total_bound bs hb
  omega
end ZkFormal.NearV3.Candidates.ProcRawNativeBudget
