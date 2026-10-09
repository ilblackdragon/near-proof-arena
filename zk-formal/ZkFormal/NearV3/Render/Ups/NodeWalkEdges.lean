import ZkFormal.NearV3.Extract.NodeView

namespace ZkFormal.NearV3.Render.UpsGen
open ZkFormal.Near

/-- An ordinary leaf key position supplies its exact native key edge. -/
theorem leaf_key_edge (n i : Nat) (s : NodeS3) (key : List Nat) (slot : NSlot3)
    (mem : List Nat) (hs : s.v=.leaf key slot mem) (hi : i<key.length) :
    [n,i,key.getD i 0,n,i+1,EK_KEY]∈edgesOf3 n s := by
  simp only [edgesOf3,hs,List.mem_append]
  exact Or.inl (Or.inl (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩))

/-- The leaf-end edge is present even when its value is unrevealed. -/
theorem leaf_end_edge (n : Nat) (s : NodeS3) (key : List Nat) (slot : NSlot3)
    (mem : List Nat) (hs : s.v=.leaf key slot mem) :
    [n,key.length,SYM_END,n,key.length,EK_LEND]∈edgesOf3 n s := by
  simp [edgesOf3,hs]

/-- A revealed leaf value supplies its exact value-record target. -/
theorem leaf_value_edge (n : Nat) (s : NodeS3) (key lenB pre post mem : List Nat)
    (vid vlen : Nat) (written : Bool)
    (hs : s.v=.leaf key (.val lenB vid vlen pre post written) mem) :
    [n,key.length,SYM_END,vid,0,EK_VAL]∈edgesOf3 n s := by
  simp [edgesOf3,hs]

/-- Before an extension's final nibble, its key edge stays in the source record. -/
theorem ext_inner_edge (n i : Nat) (s : NodeS3) (key : List Nat) (kid : NKid)
    (mem : List Nat) (hs : s.v=.ext key kid mem) (hi : i+1<key.length) :
    [n,i,key.getD i 0,n,i+1,EK_KEY]∈edgesOf3 n s := by
  simp only [edgesOf3,hs,List.mem_append]
  left
  have hd : i<key.dropLast.length := by simp only [List.length_dropLast]; omega
  have he : key.dropLast.getD i 0=key.getD i 0 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_dropLast]
    rw [ite_eq_left (by omega)]
  exact List.mem_map.mpr ⟨i,List.mem_range.mpr hd,by rw [he]⟩

/-- An extension's final nibble enters the resolved revealed child. -/
theorem ext_last_revealed_edge (n cid clen cres : Nat) (s : NodeS3)
    (front pre post mem : List Nat) (x : Nat)
    (hs : s.v=.ext (front++[x]) (.node cid clen cres pre post) mem) :
    [n,front.length,x,cres,0,EK_KEY]∈edgesOf3 n s := by
  simp [edgesOf3,hs]

/-- An unrevealed child's final key edge remains at the extension's end position. -/
theorem ext_last_hash_edge (n : Nat) (s : NodeS3) (front hash mem : List Nat) (x : Nat)
    (hs : s.v=.ext (front++[x]) (.hash hash) mem) :
    [n,front.length,x,n,front.length+1,EK_KEY]∈edgesOf3 n s := by
  simp [edgesOf3,hs]

/-- The branch's revealed value supplies its exact value-record target. -/
theorem branch_value_edge (n : Nat) (s : NodeS3) (lenB pre post mem : List Nat)
    (vid vlen : Nat) (written : Bool) (kids : List NKid)
    (hs : s.v=.branch (some (.val lenB vid vlen pre post written)) kids mem) :
    [n,0,SYM_END,vid,0,EK_VAL]∈edgesOf3 n s := by
  simp [edgesOf3,hs]
end ZkFormal.NearV3.Render.UpsGen
