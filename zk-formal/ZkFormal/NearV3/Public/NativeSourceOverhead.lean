import ZkFormal.NearV3.Public.HeaderBinding
import ZkFormal.NearV3.Rcpt.Extract.SizeProof
import ZkFormal.NearV3.Rcpt.Candidates.PreparedSourceCount

namespace ZkFormal.NearV3.Public
open ZkFormal.Algebra ZkFormal.Near NearSpecV3

/-- Exact non-SIZE portion of the constructed native source dictionary vector. -/
def sourceDictionaryOverhead (p : Prep) : Nat := 44*p.lists.length+4

theorem sourceDictionaryOverhead_bound {cb : NearSpec.Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint=.ok p) : sourceDictionaryOverhead p≤87300 := by
  have hh := Rcpt.Candidates.prepD0_source_count hp
  unfold sourceDictionaryOverhead
  omega

/-- The actual packed public overhead is interpreted naturally, not modulo the field. -/
theorem prepared_ovhNat (p : Prep) (overhead : Nat) (hr : RootsSized p)
    (ho : overhead<256^4) :
    ovhNat (ZkFormal.Udr.pubOf Fp (preparedBytes p overhead))=overhead := by
  have hh := prepared_overhead_count p overhead hr ho
  simp only [show List.range 4=[0,1,2,3] from rfl,List.map_cons,List.map_nil,V2.leNat] at hh
  unfold ovhNat pubNat
  change 256^0*Fp.toNat ((ZkFormal.Udr.pubOf Fp (preparedBytes p overhead)).getD (SizeV3.PH_WOVH+0) 0)+
    (256^1*Fp.toNat ((ZkFormal.Udr.pubOf Fp (preparedBytes p overhead)).getD (SizeV3.PH_WOVH+1) 0)+
    (256^2*Fp.toNat ((ZkFormal.Udr.pubOf Fp (preparedBytes p overhead)).getD (SizeV3.PH_WOVH+2) 0)+
    (256^3*Fp.toNat ((ZkFormal.Udr.pubOf Fp (preparedBytes p overhead)).getD (SizeV3.PH_WOVH+3) 0)+0)))=overhead
  dsimp only [V2.PubVal.val] at hh
  simp only [Nat.reducePow,Nat.one_mul] at *
  omega

/-- The source dictionary is fully paid by SIZE plus its deterministic overhead.
The remaining witness-overhead meaning and the no-wrap bound are explicit assembly
obligations; neither follows from merely serializing an arbitrary u32. -/
theorem source_dictionary_paid {p : Prep} {overhead remainder dictionarySize : Nat}
    (hr : RootsSized p) (ho : overhead<256^4)
    {v : SizeV} (hv : SizeWf (ZkFormal.Udr.pubOf Fp (preparedBytes p overhead)) v)
    (hwrap : overhead+v.x0+v.x1+v.x2+2^24≤ZkFormal.Algebra.P)
    (hsource : dictionarySize=v.x2+sourceDictionaryOverhead p)
    (hrest : sourceDictionaryOverhead p+remainder≤overhead) :
    v.x0+v.x1+dictionarySize+remainder≤8388608 := by
  have hh := hv.tot_le
  rw [prepared_ovhNat p overhead hr ho] at hh
  have hb := hh hwrap
  omega

end ZkFormal.NearV3.Public
