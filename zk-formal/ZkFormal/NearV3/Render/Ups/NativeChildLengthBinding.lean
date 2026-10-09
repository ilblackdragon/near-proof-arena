import ZkFormal.NearV3.Render.Ups.NativeChildLengths
import ZkFormal.NearV3.Assembly.UpsertShaEncoding

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec Assembly

/-- The constructed clen is exactly the referenced final part's byte length.
This is the length carried by both MEMD and the child SHA digest lookup. -/
theorem nativeInstance_childLength (recordId : PTrie→Nat) (baseI : UpsInst)
    {root : PTrie} {value : Bytes} {run : TreeRun} (hr : traceUpsert root [0,15] value=some run)
    (base : Nat→UpsPartI) {Qs : List UpsPartI}
    (he : encodeNativeParts recordId root run (nativeSourceBase recordId run base)=some Qs)
    (k : Nat) (hbound : k<Qs.length) :
    let I := nativeInstance recordId baseI root run value Qs
    (part I k).jm-1<Qs.length ∧ (part I k).clen=(child I (part I k)).q.length := by
  let I := nativeInstance recordId baseI root run value Qs
  obtain ⟨c,hc,hclen⟩ := nativeInstance_nativeChildLength recordId baseI hr base he k hbound
  obtain ⟨Qc,hQc,_⟩ := encodeTreeParts_at (nativePartBase recordId root run (nativeSourceBase recordId run base))
    run.parts 0 Qs ((part I k).jm-1) c he hc
  have hj : (part I k).jm-1<Qs.length := List.getElem?_eq_some_iff.mp hQc |>.1
  obtain ⟨c',hc',hbytes,_⟩ := nativeInstance_part_digest recordId baseI hr
    (nativeSourceBase recordId run base) he ((part I k).jm-1) hj
  rw [hc] at hc'
  cases hc'
  have hlen := congrArg List.length hbytes
  simp only [List.length_map] at hlen
  exact ⟨hj,hclen.trans hlen.symm⟩
end ZkFormal.NearV3.Render.UpsGen
