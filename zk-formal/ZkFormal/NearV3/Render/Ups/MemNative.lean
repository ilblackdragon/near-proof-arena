import ZkFormal.NearV3.Render.Ups.MemConstruct
import ZkFormal.NearV3.Render.Ups.TreeValueInput

/-! Interpret native u64 serializers and byte-list operands without imposing an
upper bound on the exact output memory total. -/
namespace ZkFormal.NearV3.Render.UpsGen
open NearSpec ZkFormal.Near

theorem u64_memory_decode (n : Nat) : le256 ((u64 n).map UInt8.toNat)=n%256^8 := by
  rw [UpsRows.toNats_u64]
  simp only [le256]
  omega

theorem pfx_byte_list (bs : List Nat) (hb : ∀ b∈bs,b<256) (hl : bs.length≤8) :
    pfx (fun i => (bs.getD i 0:Int)) 8=(le256 bs:Int) := by
  have hf : (fun i => (bs.getD i 0:Int))=(fun i => (le256 bs:Int)/256^i%256) := by
    funext i
    exact congrArg (fun n : Nat => (n:Int)) (UniqGen.byte_le256 bs i hb).symm
  rw [hf,pfx_bytes]
  have h := UniqGen.le256_lt bs hb
  have hp : 256^bs.length≤256^8 := Nat.pow_le_pow_right (by omega) hl
  omega

/-- A serialized eight-byte suffix is exactly the old-memory scalar read by MEM. -/
theorem memRb_suffix (Q : UpsPartI) (frontBytes bytes : List Nat)
    (he : Q.pb=frontBytes++bytes) (hl : bytes.length=8) (i : Nat) :
    memRb Q i=(bytes.getD i 0:Int) := by
  unfold memRb
  rw [he,List.length_append,hl]
  have hp : ((((frontBytes.length+8:Nat):Int)-8+i).toNat)=frontBytes.length+i := by omega
  rw [hp,List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega)]
  simp

theorem source_memory_scalar (Q : UpsPartI) (frontBytes : List Nat) (m : Nat)
    (he : Q.pb=frontBytes++(u64 m).map UInt8.toNat) :
    pfx (memRb Q) 8=(m%256^8:Int) := by
  have hl : ((u64 m).map UInt8.toNat).length=8 := by simp
  have hb : ∀ b∈(u64 m).map UInt8.toNat,b<256 := by
    intro b hb; obtain ⟨x,_,rfl⟩ := List.mem_map.mp hb; exact x.toNat_lt
  have hf := funext (memRb_suffix Q frontBytes _ he hl)
  rw [hf,pfx_byte_list _ hb (by omega),u64_memory_decode]
  omega
/-- Every revealed native node ends with its memory serializer. -/
theorem nodeEnc_memory_suffix (t : PTrie) (hn : isNode t=true) :
    ∃ frontBytes, (nodeEnc t).map UInt8.toNat=frontBytes++(u64 t.memD).map UInt8.toNat := by
  cases t with
  | hash => simp [isNode] at hn
  | leaf key value mem =>
    refine ⟨([0] ++ u32 (hexPrefix key true).length ++ hexPrefix key true ++ value.valueRef).map UInt8.toNat,?_⟩
    simp [nodeEnc,PTrie.memD,PTrie.mem?,List.map_append]
  | ext key child mem =>
    refine ⟨([3] ++ u32 (hexPrefix key false).length ++ hexPrefix key false ++ child.hashOf).map UInt8.toNat,?_⟩
    simp [nodeEnc,PTrie.memD,PTrie.mem?,List.map_append]
  | branch value kids mem =>
    cases value with
    | none =>
      refine ⟨([1] ++ u16 (kidsBitmap kids 0) ++ kids.hashes).map UInt8.toNat,?_⟩
      simp [nodeEnc,PTrie.memD,PTrie.mem?,List.map_append]
    | some value =>
      refine ⟨([2] ++ value.valueRef ++ u16 (kidsBitmap kids 0) ++ kids.hashes).map UInt8.toNat,?_⟩
      simp [nodeEnc,PTrie.memD,PTrie.mem?,List.map_append]

/-- The encoded actual source supplies its memory operand directly. -/
theorem encoded_source_memory {base Q : UpsPartI} {part : TreePart}
    (he : encodeTreePart base part=some Q) (hw : part.source.wf=true) :
    pfx (memRb Q) 8=(part.source.memD%256^8:Int) := by
  unfold encodeTreePart at he
  cases hs : treeNode part.source with
  | none => simp [hs] at he
  | some src =>
    cases hd : treeNode part.output with
    | none => simp [hs,hd] at he
    | some dst =>
      simp [hs,hd] at he
      subst Q
      have hn : isNode part.source=true := by
        cases h : part.source <;> simp_all [treeNode,isNode]
      obtain ⟨frontBytes,hfront⟩ := nodeEnc_memory_suffix part.source hn
      apply source_memory_scalar _ frontBytes
      exact (treeNode_ser hw hs true).trans hfront

theorem source_memory_bound (t : PTrie) (hw : t.wf=true) : t.memD<256^8 := by
  cases t <;> simp_all [PTrie.wf,PTrie.memD,PTrie.mem?]

/-- Only the original source needs the bound guaranteed by native well-formedness. -/
theorem encoded_source_memory_exact {base Q : UpsPartI} {part : TreePart}
    (he : encodeTreePart base part=some Q) (hw : part.source.wf=true) :
    pfx (memRb Q) 8=(part.source.memD:Int) := by
  rw [encoded_source_memory he hw]
  have hb := source_memory_bound part.source hw
  omega

end ZkFormal.NearV3.Render.UpsGen
