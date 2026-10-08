import ZkFormal.NearV3.Assembly.CompactDigestTargets

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Algebra ZkFormal.Air ZkFormal.Near Render.UpsGen

/-- A proven full native slice supplies every physical digest register;
field reduction is preserved rather than assumed injective. -/
theorem digest_window_slice {I : Render.UpsInst} {k pos job len : Nat} {hash : List Nat}
    (hs : ((part I k).q.drop pos).take 32=hash) (hh : hash.length=32) :
    (digestWindow I k pos job len).toFp=
      (digMsg (upsertJobId I.tau job) len hash).toFp := by
  have hv : (List.range 32).map (fun i=>(part I k).q.getD (pos+i) 0)=hash := by
    apply List.ext_getElem (by simp [hh])
    intro i hi hj
    have hib : i<32 := by simpa using hi
    have hsget:=congrArg (fun xs : List Nat=>xs.getD i 0) hs
    simp only [List.getD_eq_getElem?_getD,List.getElem?_take,hib,ite_true,
      List.getElem?_drop] at hsget
    simp only [List.getElem_map,List.getElem_range]
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some] using hsget
  simp only [digestWindow,digMsg,Msg.toFp,List.map_append,List.map_cons,List.map_nil,
    List.map_map,Function.comp_def,Fp.ofNat_toNat]
  have hf:=congrArg (List.map Fp.ofNat) hv
  simpa only [List.map_map,Function.comp_def,List.cons_append,List.nil_append] using congrArg
    (fun xs=>Fp.ofNat (upsertJobId I.tau job)::Fp.ofNat len::xs) hf

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
