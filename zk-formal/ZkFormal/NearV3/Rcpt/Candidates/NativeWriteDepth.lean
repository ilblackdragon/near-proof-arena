import ZkFormal.NearV3.Rcpt.Candidates.NativeImplicitExactUpserts

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec

mutual
/-- Receipt replay changes no lookup path depth; native fuel bounds transport
without imposing a new bound on accepted transitions. -/
theorem write_lookup_depth : ∀{a b : PTrie},WriteTreePair a b→∀key,fdepth a key=fdepth b key
  | _,_,.hash _,_=>rfl
  | _,_,.leaf _ _ _,_=>rfl
  | _,_,.ext k m h,key=>by simp only [fdepth,write_lookup_depth h]
  | _,_,.branch _ _ _,[]=>rfl
  | _,_,.branch m h hs,n::key=>by simp only [fdepth,write_kid_lookup_depth hs]
theorem write_kid_lookup_depth : ∀{a b : Kids},WriteKidsPair a b→∀n key,kfdepth a n key=kfdepth b n key
  | _,_,.nil,_,_=>rfl
  | _,_,.none _,0,_=>rfl
  | _,_,.none h,n+1,key=>write_kid_lookup_depth h n key
  | _,_,.some h _,0,key=>write_lookup_depth h key
  | _,_,.some _ hs,n+1,key=>write_kid_lookup_depth hs n key
end

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
