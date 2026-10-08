import ZkFormal.NearV3.Assembly.RcptFinalTokens

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/- Exact little-endian four-byte public read; the range prevents truncation. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem public_u32_eval (tr : Trace Fp) (pos off value : Nat) (pub : List Fp)
    (hv : value<256^4)
    (hp : ∀i,i<4→pub.getD (off+i) 0=Fp.ofNat (((u32 value).getD i 0).toNat)) :
    (sum ((List.range 4).map fun i=>smul (256^i) (.pub (off+i)))).eval tr 0 pos pub=Fp.ofNat value := by
  have h0 := hp 0 (by decide)
  have h1 := hp 1 (by decide)
  have h2 := hp 2 (by decide)
  have h3 := hp 3 (by decide)
  simp [u32,leN,UInt8.toNat_ofNat,Nat.div_div_eq_div_mul] at h0 h1 h2 h3
  have hval : value=value%256+256*((value/256)%256)+65536*((value/65536)%256)+16777216*((value/16777216)%256) := by omega
  have he := congrArg (fun n : Nat=>(n:Fp)) hval
  change (1:Fp)*pub.getD (off+0) 0+(256*pub.getD (off+1) 0+
    (65536*pub.getD (off+2) 0+(16777216*pub.getD (off+3) 0+0)))=Fp.ofNat value
  simp only [List.getD_eq_getElem?_getD,Nat.add_zero,h0,h1,h2,h3]
  change (1:Fp)*(value%256:Nat)+(256*((value/256)%256:Nat)+
    (65536*((value/65536)%256:Nat)+(16777216*((value/16777216)%256:Nat)+0)))=(value:Fp)
  grind only

end ZkFormal.NearV3.Assembly.RcptSkeleton
