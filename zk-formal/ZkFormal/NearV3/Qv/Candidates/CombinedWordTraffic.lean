import ZkFormal.NearV3.Qv.Candidates.CombinedShardTraffic

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ValueGen NearSpec

/-- One complete native key walk consumes exactly one authenticated result. -/
theorem Walk.final_word_messages (w : Walk) :
    w.kind.bytes.zipIdx.flatMap (fun bi => w.finalMessages bi.2) =
      [[W_QV+w.tau+64*w.slot,w.tau,(!w.value.isSome).toNat,
        if w.value.isSome then w.vid else 0]] := by
  cases hk : w.kind <;>
    simp [Walk.finalMessages,Kind.bytes,hk,u64,leN,List.range_succ,List.zipIdx]

/-- Present reads advance their provider counter exactly once per whole word. -/
theorem Walk.counter_word_messages (w : Walk) (sd : Bool) :
    w.kind.bytes.zipIdx.flatMap (fun bi => w.counterMessages bi.2 sd) =
      if w.value.isSome then [[w.vid,w.tau,w.mode,if sd then w.users+1 else w.users]] else [] := by
  cases hk : w.kind <;> cases hv : w.value.isSome <;>
    simp [Walk.counterMessages,Kind.bytes,hk,u64,leN,List.range_succ,List.zipIdx,hv]



def Walk.keyWordMessages (w : Walk) : List Msg :=
  let wid := W_QV+w.tau+64*w.slot
  [[wid,0,SYM_START,0]] ++
    (nibbles w.kind.bytes).zipIdx.map (fun ni => [wid,ni.2+1,ni.1,0]) ++
    [[wid,2*w.kind.bytes.length+1,SYM_END,1]]

theorem Walk.key_word_messages (w : Walk) :
    w.kind.bytes.zipIdx.flatMap (fun bi => w.keyMessages bi.2 bi.1) =
      w.keyWordMessages := by
  cases hk : w.kind <;>
    simp [Walk.keyMessages,Walk.keyWordMessages,Kind.bytes,hk,u64,leN,
      List.range_succ,List.zipIdx,nibbles]


def Walk.shardWordMessages (w : Walk) : List Msg :=
  match w.kind with
  | .group s => (u64 s).zipIdx.map (fun bi => [w.tau,w.slot-3,bi.2,bi.1.toNat])
  | .buffered => if w.value.isSome && (w.tau==0) then [[w.tau,0,8,w.count]] else []
  | _ => []

theorem Walk.shard_word_messages (w : Walk) :
    w.kind.bytes.zipIdx.flatMap (fun bi => w.shardMessages bi.2 bi.1) =
      w.shardWordMessages := by
  cases hk : w.kind <;> cases hv : w.value.isSome <;> by_cases ht : w.tau=0 <;>
    simp [Walk.shardMessages,Walk.shardWordMessages,Kind.bytes,Kind.code,hk,hv,ht,
      u64,leN,List.range_succ,List.zipIdx]

private theorem flatMap_congr_mem {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x ∈ xs, f x=g x) : xs.flatMap f=xs.flatMap g := by
  simp only [List.flatMap_def]
  exact congrArg List.flatten (List.map_congr_left h)

/-- Actual field traffic over the consecutive rows of a generated native word.
Only the trace cells are supplied; acceptance and global balance are not assumed. -/
theorem Walk.final_word_field (w : Walk) (tr : Trace Fp) (t start : Nat) (pub : List Fp)
    (hc : ∀ bi ∈ w.kind.bytes.zipIdx, ∀ c,
      tr.cell t (start+bi.2) c = Fp.ofNat ((w.row bi.2 bi.1).getD c 0)) :
    w.kind.bytes.zipIdx.flatMap (fun bi =>
      rowTraffic CombinedTable.interactions tr t (start+bi.2) pub B_FINAL false) =
    ([[W_QV+w.tau+64*w.slot,w.tau,(!w.value.isSome).toNat,
      if w.value.isSome then w.vid else 0]] : List Msg).map Msg.toFp := by
  calc
    _ = w.kind.bytes.zipIdx.flatMap (fun bi => (w.finalMessages bi.2).map Msg.toFp) :=
      flatMap_congr_mem _ _ _ (fun bi hi => w.final_field_messages bi.2 bi.1 tr t _ pub (hc bi hi))
    _ = _ := by rw [← List.map_flatMap,w.final_word_messages]

theorem Walk.counter_word_field (w : Walk) (tr : Trace Fp) (t start : Nat)
    (pub : List Fp) (sd : Bool)
    (hc : ∀ bi ∈ w.kind.bytes.zipIdx, ∀ c,
      tr.cell t (start+bi.2) c = Fp.ofNat ((w.row bi.2 bi.1).getD c 0)) :
    w.kind.bytes.zipIdx.flatMap (fun bi =>
      rowTraffic CombinedTable.interactions tr t (start+bi.2) pub ValueTable.B_QVC sd) =
    (if w.value.isSome then [[w.vid,w.tau,w.mode,if sd then w.users+1 else w.users]]
      else ([] : List Msg)).map Msg.toFp := by
  calc
    _ = w.kind.bytes.zipIdx.flatMap (fun bi => (w.counterMessages bi.2 sd).map Msg.toFp) :=
      flatMap_congr_mem _ _ _ (fun bi hi => w.counter_field_messages bi.2 bi.1 tr t _ pub (hc bi hi) sd)
    _ = _ := by rw [← List.map_flatMap,w.counter_word_messages]


theorem Walk.key_word_field (w : Walk) (tr : Trace Fp) (t start : Nat) (pub : List Fp)
    (hc : ∀ bi ∈ w.kind.bytes.zipIdx, ∀ c,
      tr.cell t (start+bi.2) c = Fp.ofNat ((w.row bi.2 bi.1).getD c 0)) :
    w.kind.bytes.zipIdx.flatMap (fun bi =>
      rowTraffic CombinedTable.interactions tr t (start+bi.2) pub B_KEYNIB true) =
      w.keyWordMessages.map Msg.toFp := by
  calc
    _ = w.kind.bytes.zipIdx.flatMap (fun bi => (w.keyMessages bi.2 bi.1).map Msg.toFp) :=
      flatMap_congr_mem _ _ _ (fun bi hi => w.key_field_messages bi.2 bi.1 tr t _ pub (hc bi hi))
    _ = _ := by rw [← List.map_flatMap,w.key_word_messages]


theorem Walk.shard_word_field (w : Walk) (tr : Trace Fp) (t start : Nat) (pub : List Fp)
    (hc : ∀ bi ∈ w.kind.bytes.zipIdx, ∀ c,
      tr.cell t (start+bi.2) c = Fp.ofNat ((w.row bi.2 bi.1).getD c 0))
    (hs : w.kind.code=3 → 3≤w.slot) :
    w.kind.bytes.zipIdx.flatMap (fun bi =>
      rowTraffic CombinedTable.interactions tr t (start+bi.2) pub B_QSH false) =
      w.shardWordMessages.map Msg.toFp := by
  calc
    _ = w.kind.bytes.zipIdx.flatMap (fun bi => (w.shardMessages bi.2 bi.1).map Msg.toFp) :=
      flatMap_congr_mem _ _ _ (fun bi hi => w.shard_field_messages bi.2 bi.1 tr t _ pub (hc bi hi) hs)
    _ = _ := by rw [← List.map_flatMap,w.shard_word_messages]

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen



