import ZkFormal.NearV3.Assembly.SourceAddresses

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 Assembly Render.UpsGen

mutual
/-- The full source path counts every revealed edge, including empty extension
nodes retained for pass-through parts. -/
theorem source_address_depth : ∀n v d t key i a,
    (sourceAddresses n v d t key)[i]?=some a→a.depth=d+i
  | _,_,_,.hash _,_,0,_,h => by cases h;rfl
  | _,_,_,.hash _,_,_+1,_,h => by simp [sourceAddresses] at h
  | _,_,_,.leaf ..,_,0,_,h => by cases h;rfl
  | _,_,_,.leaf ..,_,_+1,_,h => by simp [sourceAddresses] at h
  | _,_,_,.ext ..,_,0,_,h => by cases h;rfl
  | n,v,d,.ext k c m,key,i+1,a,h => by
    simp only [sourceAddresses,List.getElem?_cons_succ] at h
    split at h
    · have hh:=source_address_depth (n+1) v (d+1) c (key.drop k.length) i a h
      omega
    · simp at h
  | _,_,_,.branch ..,[],0,_,h => by cases h;rfl
  | _,_,_,.branch ..,[],_+1,_,h => by simp [sourceAddresses] at h
  | _,_,_,.branch ..,_::_,0,_,h => by cases h;rfl
  | n,v,d,.branch sv cs m,j::key,i+1,a,h => by
    have hh:=kid_source_address_depth (n+1) (v+(optSlotVal sv).length) (d+1) cs j key i a h
    omega
theorem kid_source_address_depth : ∀n v d cs j key i a,
    (kidSourceAddresses n v d cs j key)[i]?=some a→a.depth=d+i
  | _,_,_,.nil,_,_,_,_,h => by simp [kidSourceAddresses] at h
  | _,_,_,.none _,0,_,_,_,h => by simp [kidSourceAddresses] at h
  | n,v,d,.some c _,0,key,i,a,h => source_address_depth n v d c key i a h
  | n,v,d,.none cs,j+1,key,i,a,h => kid_source_address_depth n v d cs j key i a h
  | n,v,d,.some c cs,j+1,key,i,a,h => kid_source_address_depth (n+tsize c) (v+(valsOf c).length) d cs j key i a h
end

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
