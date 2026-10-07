import ZkFormal.NearV3.Qv.Candidates.ValueTraffic

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec

def selectorValue (r : List Nat) : Nat :=
  ((List.range 8).map fun i => i * r.getD (ValueTable.sel i) 0).sum

theorem row_selectorValue (cfg : Config) (pos byte phase j entry : Nat) (regs : Bytes)
    (hj : j<8) (hp : phase≠4) :
    selectorValue (row cfg pos byte phase j entry regs) = j := by
  have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [selectorValue,row,ValueTable.sel,List.range_succ,hp]

@[simp] theorem row_shard (cfg : Config) (pos byte phase j entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase j entry regs).getD ValueTable.shard 0 = (decide (phase=1)).toNat := by
  simp [row,ValueTable.shard]

@[simp] theorem row_tau (cfg : Config) (pos byte phase j entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase j entry regs).getD ValueTable.tau 0 = cfg.tau := by
  simp [row,ValueTable.tau]

@[simp] theorem row_entry (cfg : Config) (pos byte phase j entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase j entry regs).getD ValueTable.entry 0 = entry := by
  simp [row,ValueTable.entry]

@[simp] theorem row_byte (cfg : Config) (pos byte phase j entry : Nat) (regs : Bytes) :
    (row cfg pos byte phase j entry regs).getD ValueTable.byte 0 = byte := by
  simp [row,ValueTable.byte]

def shardMessages (rows : List (List Nat)) : List (List Nat) :=
  (rows.filter fun r => r.getD ValueTable.shard 0 = 1).map
    (fun r => [r.getD ValueTable.tau 0,r.getD ValueTable.entry 0,selectorValue r,
      r.getD ValueTable.byte 0])

theorem shardMessages_append (a b : List (List Nat)) :
    shardMessages (a++b) = shardMessages a ++ shardMessages b := by simp [shardMessages]

theorem wordRows_no_shards (cfg : Config) (offset phase entry : Nat) (bytes regs : Bytes)
    (hp : phase≠1) : shardMessages (wordRows cfg offset phase entry bytes regs) = [] := by
  simp [shardMessages,wordRows,List.filter_map,row,ValueTable.shard,hp]

theorem wordRows_shards (cfg : Config) (offset entry : Nat) (bytes regs : Bytes)
    (hb : bytes.length=8) :
    shardMessages (wordRows cfg offset 1 entry bytes regs) =
      bytes.zipIdx.map (fun (b,i) => [cfg.tau,entry,i,b.toNat]) := by
  simp only [shardMessages,wordRows,List.filter_map,row_shard,decide_true,Bool.toNat_true,
    Function.comp_def]
  rw [List.filter_eq_self.mpr (by intros; rfl),List.map_map]
  apply List.map_congr_left
  rintro ⟨b,i⟩ hm
  have hi : i<8 := by
    have hget := List.mk_mem_zipIdx_iff_getElem?.mp hm
    obtain ⟨hlt,_⟩ := List.getElem?_eq_some_iff.mp hget
    omega
  simp only [Function.comp_def,row_tau,row_entry,row_byte,
    row_selectorValue cfg (offset+i) b.toNat 1 i entry regs hi (by decide)]

theorem shardMessages_flatMap {α : Type} (xs : List α) (f : α → List (List Nat)) :
    shardMessages (xs.flatMap f) = xs.flatMap (fun x => shardMessages (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,shardMessages_append,ih]

theorem bufferRows_shards (vid tau users : Nat) (es : List ByteBuffer)
    (hs : ∀ e ∈ es, e.Sized) :
    shardMessages (bufferRows vid tau users es) =
      es.zipIdx.flatMap (fun (e,i) => e.shard.zipIdx.map (fun (b,j) => [tau,i,j,b.toNat])) := by
  unfold bufferRows
  rw [shardMessages_append,wordRows_no_shards _ _ _ _ _ _ (by decide),List.nil_append,
    shardMessages_flatMap]
  rw [List.flatMap_def,List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  rintro ⟨e,i⟩ hm
  have he := hs e (List.fst_mem_of_mem_zipIdx hm)
  simp only [shardMessages_append,wordRows_no_shards _ _ 2 _ _ _ (by decide),
    wordRows_no_shards _ _ 3 _ _ _ (by decide),List.nil_append,List.append_nil,
    wordRows_shards _ _ _ _ _ he.1]

end ZkFormal.NearV3.Qv.Candidates.ValueGen
