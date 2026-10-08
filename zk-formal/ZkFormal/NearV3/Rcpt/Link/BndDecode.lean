import ZkFormal.NearV3.Rcpt.Link.BndPublic
import ZkFormal.NearV3.Rcpt.Link.NativeRouting

namespace ZkFormal.NearV3.RcptLink
open ZkFormal.Near NearSpec

private theorem boundary_pad (o : Option Bytes) (pos : Nat) :
    padB (boundaryNats o) pos=((o.getD []).getD pos 0).toNat := by
  simp only [padB,boundaryNats,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases (o.getD [])[pos]? <;> rfl

/-- Natural, canonical indexed boundary records identify the actual interval and
all three endpoint values. The old field-only packed-key equality is insufficient. -/
theorem boundary_record_decode (p : NearSpecV3.Prep) {q pos lo hi hn idx : Nat}
    (hp : pos<65) (hidx : idx<BND_STRIDE*p.bnds.length)
    (hrec : [65*q+pos,lo,hi,hn]=[idx]++(Public.boundaryRow p.bnds idx).map UInt8.toNat) :
    q<p.bnds.length ∧
    lo=padB (boundaryNats (p.bnds.getD q (none,none)).1) pos ∧
    hi=padB (boundaryNats (p.bnds.getD q (none,none)).2) pos ∧
    hn=(if (p.bnds.getD q (none,none)).2.isNone then 1 else 0) := by
  have hx : 65*q+pos=idx := by
    have hh := congrArg (fun xs => xs.getD 0 0) hrec
    simpa only [List.singleton_append,List.getD_cons_zero] using hh
  have hq : q<p.bnds.length := by unfold BND_STRIDE at hidx; omega
  have hd : idx/65=q ∧ idx%65=pos := by omega
  simp only [Public.boundaryRow,BND_STRIDE,hd.1,hd.2,List.map_cons,List.map_nil,
    List.singleton_append,List.cons.injEq] at hrec
  refine ⟨hq,?_,?_,?_⟩
  · rw [boundary_pad]
    exact hrec.2.1
  · rw [boundary_pad]
    exact hrec.2.2.1
  · have hh := hrec.2.2.2.1
    split at hh
    · rename_i h
      change hn=1 at hh
      simpa only [h,ite_true] using hh
    · rename_i h
      change hn=0 at hh
      simpa only [h,Bool.false_eq_true,ite_false] using hh

end ZkFormal.NearV3.RcptLink
