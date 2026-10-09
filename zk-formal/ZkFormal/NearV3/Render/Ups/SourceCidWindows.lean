import ZkFormal.NearV3.Render.Ups.SourceCidBytes

namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near ZkFormal.Near.Render
open NodeGen (F layout)

def fieldCid (f : F) : Nat := match f.chw with | some w => w.cid | none => 0

theorem cidLayout_fields (fs : List F) (hp : Nat) :
    (layout fs hp).map (fun fi=>fieldCid fi.1)=
      fs.flatMap (fun f=>List.replicate (f.len hp) (fieldCid f)) := by
  simp [layout,List.map_flatMap,List.map_map,Function.comp_def,List.map_const']

/-- Extension child IDs occupy exactly the serialized 32-byte child-digest window. -/
theorem sourceCidBytes_ext (key : List Nat) (kid : NKid) (mem : List Nat) :
    sourceCidBytes (.ext key kid mem)=
      List.replicate (6+key.length/2) 0 ++
      List.replicate 32 (fieldCid (.ch (NodeGen3.kidWin kid 0 true none))) ++ List.replicate 8 0 := by
  change (layout (NodeGen3.fieldsOf (.ext key kid mem)) (NodeGen3.hplenOf (.ext key kid mem))).map
    (fun fi=>fieldCid fi.1)=_
  rw [cidLayout_fields]
  simp only [NodeGen3.fieldsOf,NodeGen3.hplenOf,NodeGen3.isLE,ite_true,NodeGen3.keyOf,
    List.flatMap_cons,List.flatMap_nil,F.len,fieldCid,F.chw,List.append_nil]
  rw [show 1+key.length/2-1=key.length/2 by omega]
  simp only [←List.append_assoc,List.replicate_append_replicate]
  rw [show 1+(4+(1+key.length/2))=6+key.length/2 by omega]

/-- The native extension source's selected CH bytes name its immediate occurrence
child, even when its walk target skips further empty extensions. -/
theorem sourceCidBytes_ext_child (n vid : Nat) (key : List Nat) (child : PTrie) (mem i : Nat)
    (hn : isNode child=true) (hi : i<32) :
    (sourceCidBytes (viewNode n vid (.ext key child mem))).getD (6+key.length/2+i) 0=n+1 := by
  rw [show viewNode n vid (.ext key child mem)=
    NodeV3.ext key (viewKid (n+1) child) ((u64 mem).map UInt8.toNat) from rfl,sourceCidBytes_ext]
  simp only [viewKid,hn,ite_true,NodeGen3.kidWin,fieldCid,F.chw]
  rw [List.append_assoc,List.getD_eq_getElem?_getD,List.getElem?_append_right (by simp)]
  simp only [List.length_replicate]
  rw [show 6+key.length/2+i-(6+key.length/2)=i by omega]
  rw [List.getElem?_append_left (by simp; exact hi)]
  rw [List.getElem?_replicate_of_lt hi]
  rfl


private theorem cid_skip (s l p : Nat) (rest : List (Nat×Nat)) (hn : s≠7)
    (hh : ((fieldAt ((s,l)::rest) p).1,(fieldAt ((s,l)::rest) p).2.1)=(7,0)) :
    l≤p ∧ ((fieldAt rest (p-l)).1,(fieldAt rest (p-l)).2.1)=(7,0) := by
  by_cases hp : p<l
  · simp [fieldAt,hp] at hh
    exact (hn hh.1).elim
  · exact ⟨by omega,by simpa only [fieldAt,hp,ite_false] using hh⟩

private theorem cid_start (p : Nat)
    (hh : ((fieldAt [(7,32),(8,8)] p).1,(fieldAt [(7,32),(8,8)] p).2.1)=(7,0)) : p=0 := by
  by_cases hp : p<32
  · simpa [fieldAt,hp] using hh
  · by_cases hq : p-32<8 <;> simp [fieldAt,hp,hq] at hh

/-- The first extension CH byte follows tag, full u32 length and all HP bytes. -/
theorem ext_child_position (hk p : Nat) (hh : 1≤hk)
    (hs : (fieldAt (nodeFields 1 hk 1) p).1=7)
    (hi : (fieldAt (nodeFields 1 hk 1) p).2.1=0) : p=5+hk := by
  have hp : ((fieldAt (nodeFields 1 hk 1) p).1,(fieldAt (nodeFields 1 hk 1) p).2.1)=(7,0) :=
    Prod.ext hs hi
  by_cases hk1 : 1<hk
  · simp only [nodeFields] at hp
    simp only [show (1:Nat)≤1 from by decide,show ¬(1:Nat)=0 from by decide,
      show ¬(1:Nat)=3 from by decide,show ¬(2:Nat)≤1 from by decide,hk1,
      ite_true,ite_false,false_or,List.cons_append,List.nil_append,List.replicate_succ,List.replicate_zero] at hp
    obtain ⟨h1,hp⟩ := cid_skip 0 1 p _ (by decide) hp
    obtain ⟨h2,hp⟩ := cid_skip 1 4 (p-1) _ (by decide) hp
    obtain ⟨h3,hp⟩ := cid_skip 2 1 (p-1-4) _ (by decide) hp
    obtain ⟨h4,hp⟩ := cid_skip 3 (hk-1) (p-1-4-1) _ (by decide) hp
    have hz := cid_start _ hp
    omega
  · have hk0 : hk=1 := by omega
    subst hk
    simp only [nodeFields] at hp
    simp only [show (1:Nat)≤1 from by decide,show ¬(1:Nat)=0 from by decide,
      show ¬(1:Nat)=3 from by decide,show ¬(2:Nat)≤1 from by decide,show ¬(1:Nat)<1 from by decide,
      ite_true,ite_false,false_or,List.cons_append,List.nil_append,List.replicate_succ,List.replicate_zero] at hp
    obtain ⟨h1,hp⟩ := cid_skip 0 1 p _ (by decide) hp
    obtain ⟨h2,hp⟩ := cid_skip 1 4 (p-1) _ (by decide) hp
    obtain ⟨h3,hp⟩ := cid_skip 2 1 (p-1-4) _ (by decide) hp
    have hz := cid_start _ hp
    omega
end ZkFormal.NearV3.Render.UpsGen
