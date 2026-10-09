import ZkFormal.NearV3.Assembly.CompactDigestFieldStarts

namespace ZkFormal.NearV3.Assembly.CompactPhysicalDigests
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Render.UpsRelay UpsRows UpsV3 Render.UpsGen

private theorem non_digest_field (I : Render.UpsInst) (k p s wi : Nat)
    (h5 : s≠5) (h7 : s≠7) : fieldDigestMsgs I k p s wi=[] := by
  simp [fieldDigestMsgs,WinFrB,h5,h7]

/-- Child windows retain their complete bitmap order and ordinal, rather than
being replaced by a single lookup for the branch. -/
theorem child_window_starts (I : Render.UpsInst) (k n base wi : Nat) :
    fieldStarts (fieldDigestMsgs I k) (List.replicate n (7,32)++[(8,8)]) base wi=
      (List.range n).flatMap (fun j=>fieldDigestMsgs I k (base+32*j) 7 (wi+j)) := by
  induction n generalizing base wi with
  | zero=>simp [fieldStarts,fieldDigestMsgs,WinFrB]
  | succ n ih=>
    simp only [List.replicate_succ,List.cons_append,fieldStarts,show ¬(32:Nat)=0 by decide,
      ite_false,ite_true,Nat.reduceAdd,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
      Nat.mul_zero,Nat.add_zero]
    rw [ih]
    congr 1
    apply congrArg (fun f=>(List.range n).flatMap f)
    funext j
    congr 1 <;> omega

/-- A branch without a value contributes exactly its selected fresh child
windows at offsets 3+32*j. Copied children contribute no DIGEST demand. -/
theorem branch_digest_inventory (I : Render.UpsInst) (k : Nat)
    (hf : FieldsOk (part I k)) (ht : (part I k).ty=2) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=
      (List.range (nWin (part I k).shape)).flatMap
        (fun j=>fieldDigestMsgs I k (3+32*j) 7 j) := by
  rw [node_digest_field_starts I k hf]
  conv=>lhs;rw [hf.shape]
  simp only [ht,nodeFields,false_or,or_true,show ¬(2:Nat)=3 by decide,show ¬(2:Nat)≤1 by decide,show ¬((2:Nat)=0∨2=3) by decide,
    show (2:Nat)≤2 by decide,ite_false,ite_true,List.append_nil,List.cons_append,List.nil_append,
    fieldStarts,show ¬(1:Nat)=0 by decide,show ¬(2:Nat)=0 by decide,show ¬(0:Nat)=7 by decide,
    show ¬(6:Nat)=7 by decide,Nat.reduceAdd,Nat.add_zero,
    non_digest_field I k _ 0 _ (by decide) (by decide),
    non_digest_field I k _ 6 _ (by decide) (by decide),List.nil_append]
  rw [child_window_starts]
  simp only [Nat.zero_add]

/-- A value-bearing branch adds its one value window at offset5 and otherwise
retains all child windows in their physical order at offsets39+32*j. -/
theorem value_branch_digest_inventory (I : Render.UpsInst) (k : Nat)
    (hf : FieldsOk (part I k)) (ht : (part I k).ty=3) :
    (List.range (part I k).q.length).flatMap (nodeDigestMsgs I k)=
      fieldDigestMsgs I k 5 5 0 ++ (List.range (nWin (part I k).shape)).flatMap
        (fun j=>fieldDigestMsgs I k (39+32*j) 7 j) := by
  rw [node_digest_field_starts I k hf]
  conv=>lhs;rw [hf.shape]
  simp only [ht,nodeFields,false_or,or_true,show ¬(2:Nat)=3 by decide,show ¬(3:Nat)≤1 by decide,show ((3:Nat)=0∨3=3) by decide,
    show (2:Nat)≤3 by decide,ite_false,ite_true,List.append_nil,List.cons_append,List.nil_append,
    fieldStarts,show ¬(1:Nat)=0 by decide,show ¬(2:Nat)=0 by decide,
    show ¬(4:Nat)=0 by decide,show ¬(32:Nat)=0 by decide,
    show ¬(0:Nat)=7 by decide,show ¬(4:Nat)=7 by decide,show ¬(5:Nat)=7 by decide,
    show ¬(6:Nat)=7 by decide,Nat.reduceAdd,Nat.add_zero,
    non_digest_field I k _ 0 _ (by decide) (by decide),
    non_digest_field I k _ 4 _ (by decide) (by decide),
    non_digest_field I k _ 6 _ (by decide) (by decide),List.nil_append]
  rw [child_window_starts]
  simp only [Nat.zero_add]

end ZkFormal.NearV3.Assembly.CompactPhysicalDigests
