import ZkFormal.NearV3.Qv.Buffered

namespace ZkFormal.NearV3.Qv
open NearSpec NearSpecV3 ReexecV3D0

/-- A complete byte prefix decodes to its natural little-endian value. -/
theorem readLE_prefix (w : Nat) (bs : Bytes) (hb : w≤bs.length) :
    readLE w bs=some (leNat (bs.take w),bs.drop w) := by
  have ht : (bs.take w).length=w := by simp [List.length_take,Nat.min_eq_left hb]
  have hsize : leNat (bs.take w)<256^w := by simpa only [ht] using leNat_lt (bs.take w)
  have h := readLE_append w (leNat (bs.take w)) (bs.drop w) hsize
  have he : leN w (leNat (bs.take w))=bs.take w := by simpa only [ht] using leN_leNat (bs.take w)
  rw [he,List.take_append_drop] at h
  exact h

theorem pU64_prefix (label : String) (bs : Bytes) (hb : 8≤bs.length) :
    pU64 label bs=.ok (leNat (bs.take 8),bs.drop 8) := by
  unfold pU64 readU64 lift
  rw [readLE_prefix 8 bs hb]

theorem pU32_prefix (label : String) (bs : Bytes) (hb : 4≤bs.length) :
    pU32 label bs=.ok (leNat (bs.take 4),bs.drop 4) := by
  unfold pU32 readU32 lift
  rw [readLE_prefix 4 bs hb]

theorem bufferEntryParser_prefix (bs : Bytes) (hb : 24≤bs.length) :
    bufferEntryParser bs=.ok
      ((leNat (bs.take 8),leNat ((bs.drop 8).take 8),leNat ((bs.drop 16).take 8)),bs.drop 24) := by
  have h1 := pU64_prefix "shard" bs (by omega)
  have h2 := pU64_prefix "first" (bs.drop 8) (by simp only [List.length_drop]; omega)
  have h3 := pU64_prefix "next" (bs.drop 16) (by simp only [List.length_drop]; omega)
  simp only [bufferEntryParser,h1,bind,Except.bind,h2,List.drop_drop,show 8+8=16 from rfl,h3,
    show 16+8=24 from rfl,pure,Except.pure]

/-- Exact-length entries with equal index words decode successfully, including repeated shard IDs. -/
theorem bufferMany_bytes (k : Nat) (bs : Bytes) (hlen : bs.length=24*k)
    (heq : ∀ j, j<k → (bs.drop (24*j+8)).take 8=(bs.drop (24*j+16)).take 8) :
    ∃ es, pMany bufferEntryParser k bs=.ok (es,[]) ∧ EmptyBuffers es := by
  induction k generalizing bs with
  | zero =>
    have hb : bs=[] := by cases bs <;> simp_all
    subst bs
    exact ⟨[],rfl,by simp [EmptyBuffers]⟩
  | succ k ih =>
    have ht : (bs.drop 24).length=24*k := by simp only [List.length_drop]; omega
    have heqt : ∀ j, j<k → ((bs.drop 24).drop (24*j+8)).take 8=
        ((bs.drop 24).drop (24*j+16)).take 8 := by
      intro j hj
      have hh := heq (j+1) (by omega)
      simp only [List.drop_drop]
      have h1 : 24+(24*j+8)=24*(j+1)+8 := by omega
      have h2 : 24+(24*j+16)=24*(j+1)+16 := by omega
      simpa only [h1,h2] using hh
    obtain ⟨es,hparse,he⟩ := ih (bs.drop 24) ht heqt
    let e : BufferEntry := (leNat (bs.take 8),leNat ((bs.drop 8).take 8),leNat ((bs.drop 16).take 8))
    have hfirst : bufferEntryParser bs=.ok (e,bs.drop 24) := bufferEntryParser_prefix bs (by omega)
    refine ⟨e::es,?_,?_⟩
    · simp only [pMany,hfirst,bind,Except.bind,hparse,pure,Except.pure]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl|hx
      · change leNat ((bs.drop 8).take 8)=leNat ((bs.drop 16).take 8)
        have hh := heq 0 (by omega)
        simpa only [Nat.mul_zero,Nat.zero_add] using congrArg leNat hh
      · exact he x hx

/-- Structural bytes accepted by the AIR's buffered parser satisfy the native predicate. -/
theorem buffered_value_of_bytes (bs : Bytes) (k : Nat) (hlen : bs.length=4+24*k)
    (hcount : leNat (bs.take 4)=k)
    (heq : ∀ j, j<k → (bs.drop (4+24*j+8)).take 8=(bs.drop (4+24*j+16)).take 8) :
    ∃ shards, BufferedValue (some bs) shards := by
  have ht : (bs.drop 4).length=24*k := by simp only [List.length_drop]; omega
  have heqt : ∀ j, j<k → ((bs.drop 4).drop (24*j+8)).take 8=
      ((bs.drop 4).drop (24*j+16)).take 8 := by
    intro j hj
    simpa only [List.drop_drop,Nat.add_assoc] using heq j hj
  obtain ⟨es,hparse,he⟩ := bufferMany_bytes k (bs.drop 4) ht heqt
  have hhead := pU32_prefix ("shard_buffers" ++ " length") bs (by omega)
  rw [hcount] at hhead
  have hvec : pVec "shard_buffers" bufferEntryParser bs=.ok (es,[]) := by
    simp only [pVec,hhead,bind,Except.bind,hparse]
  refine ⟨es.map (·.1),(bufferedShards_iff _ _).mp ?_⟩
  unfold bufferedShards
  change (do
    let (rows,rest) ← pVec "shard_buffers" bufferEntryParser bs
    if !rest.isEmpty then throw "invalid: StorageInconsistentState (BufferedReceiptIndices)"
    if rows.any (fun e => e.2.1 != e.2.2) then throw "out of domain (e.queues_empty): outgoing buffer not empty"
    pure (rows.map (fun e : BufferEntry => e.1)))=.ok (es.map (·.1))
  simp only [hvec,bind,Except.bind,List.isEmpty_nil,Bool.not_true,Bool.false_eq_true,↓reduceIte,
    emptyBuffers_any es he,pure,Except.pure]

end ZkFormal.NearV3.Qv
