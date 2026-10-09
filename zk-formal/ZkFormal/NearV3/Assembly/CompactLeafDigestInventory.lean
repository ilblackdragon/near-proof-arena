import ZkFormal.NearV3.Assembly.CompactDigestFieldStarts

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render.UpsRelay UpsRows UpsV3 Render.UpsGen

private theorem non_digest_field (I : Render.UpsInst) (k p s wi : Nat)
    (h5 : s≠5) (h7 : s≠7) : fieldDigestMsgs I k p s wi=[] := by
  simp [fieldDigestMsgs,WinFrB,h5,h7]

/-- A serialized leaf contributes precisely its value-hash field start, or no
lookup when copied. Its variable key/header bytes introduce no extra requests. -/
theorem leaf_digest_inventory (I : Render.UpsInst) (k : Nat)
    (hf : FieldsOk (part I k)) (ht : (part I k).ty=0) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=
      fieldDigestMsgs I k (9+(part I k).qhk) 5 0 := by
  have hw:=hf.leaf ht
  have hh:1≤(part I k).qhk:=hf.prefixLength (by omega)
  rw [node_digest_field_starts]
  · rw [hf.shape]
    simp only [ht,hw,nodeFields,List.replicate_zero,List.append_nil,
      show (0:Nat)≤1 by decide,show (0:Nat)=0∨0=3 by decide,show ¬(2:Nat)≤0 by decide,
      ite_true,ite_false,true_or]
    by_cases hk:1<(part I k).qhk
    · simp only [hk,ite_true,show ¬(0:Nat)=7 by decide,show ¬(1:Nat)=7 by decide,show ¬(2:Nat)=7 by decide,show ¬(3:Nat)=7 by decide,show ¬(4:Nat)=7 by decide,show ¬(5:Nat)=7 by decide,show ¬(8:Nat)=7 by decide,Nat.reduceAdd,Nat.add_zero,List.cons_append,List.nil_append,fieldStarts,
        show ¬(1:Nat)=0 by decide,show ¬(4:Nat)=0 by decide,show ¬(32:Nat)=0 by decide,
        show ¬(8:Nat)=0 by decide,show ¬(part I k).qhk-1=0 by omega,ite_false,
        non_digest_field I k _ 0 _ (by decide) (by decide),
        non_digest_field I k _ 1 _ (by decide) (by decide),
        non_digest_field I k _ 2 _ (by decide) (by decide),
        non_digest_field I k _ 3 _ (by decide) (by decide),
        non_digest_field I k _ 4 _ (by decide) (by decide),
        non_digest_field I k _ 8 _ (by decide) (by decide)]
      simp only [List.nil_append,List.append_nil]
      congr 1 <;> omega
    · have hk1:(part I k).qhk=1:=by omega
      simp [hk,hk1,fieldStarts,fieldDigestMsgs,WinFrB]
  · exact hf

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
