import ZkFormal.NearV3.Render.Ups.SourceLayout

namespace ZkFormal.NearV3.Render.UpsGen

 theorem SourceLayout.preserved_position {I : UpsInst} {Q : UpsPartI}
    (e : SourceLayout Q) (f : FieldsOk Q) {p : Nat} (hp : p < Q.q.length)
    (hk : Q.kind ∈ [0,1,2,3,11]) :
    sposV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p = (p : Int) := by
  by_cases hs : (fieldAt Q.shape p).1=8
  · have hm := f.mem_position hp hs
    have hl := e.length_preserve f hk
    simp [sposV,hs]; omega
  · simp [sposV,hs,hk]

theorem SourceLayout.value_position {I : UpsInst} {Q : UpsPartI}
    (e : SourceLayout Q) (f : FieldsOk Q) {p : Nat} (hp : p < Q.q.length)
    (hk : Q.kind=4) :
    sposV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p +
      36*aftV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.2.2 = (p : Int) := by
  by_cases hs : (fieldAt Q.shape p).1=8
  · have hm := f.mem_position hp hs
    have hl := e.length_value f hk
    simp [sposV,hs,aftV,AftB,hk,ind]; omega
  · simp [sposV,hs,hk] <;> omega

theorem SourceLayout.child_position {I : UpsInst} {Q : UpsPartI}
    (e : SourceLayout Q) (f : FieldsOk Q) {p : Nat} (hp : p < Q.q.length)
    (hk : Q.kind=5) :
    sposV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.1 (fieldAt Q.shape p).2.2.2 p +
      32*aftV I Q (fieldAt Q.shape p).1 (fieldAt Q.shape p).2.2.2 = (p : Int) := by
  by_cases hs : (fieldAt Q.shape p).1=8
  · have hm := f.mem_position hp hs
    have hl := e.length_child f hk
    simp [sposV,hs,aftV,AftB,hk,ind]; omega
  · simp [sposV,hs,hk] <;> omega

end ZkFormal.NearV3.Render.UpsGen
