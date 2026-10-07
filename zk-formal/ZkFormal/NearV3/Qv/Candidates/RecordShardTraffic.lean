import ZkFormal.NearV3.Qv.Candidates.RecordProviders
import ZkFormal.NearV3.Qv.Candidates.ShardTraffic
import ZkFormal.Near.Render.Proof.Base

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.Air

theorem rowNatEval_sum (row : List Nat) (es : List Expr) :
    rowNatEval row (sum es)=(es.map (rowNatEval row)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [sum,rowNatEval,List.map_cons,List.sum_cons,ih]

theorem rowNatEval_subpos (row : List Nat) :
    rowNatEval row ValueTable.subpos=selectorValue row := by
  simp [ValueTable.subpos,rowNatEval_sum,selectorValue,List.map_map,Function.comp_def,smul,rowNatEval,c]

def countMessages (rows : List (List Nat)) : List Msg :=
  (rows.filter (fun r => r.getD ValueTable.header 0*r.getD (ValueTable.sel 3) 0=1)).map
    (fun r => [r.getD ValueTable.tau 0,0,8,r.getD ValueTable.count 0])

theorem natRowTraffic_shards (row : List Nat) :
    natRowTraffic ValueTable.interactions row B_QSH true =
      (if row.getD ValueTable.shard 0=1 then
        [[row.getD ValueTable.tau 0,row.getD ValueTable.entry 0,selectorValue row,
          row.getD ValueTable.byte 0]] else []) ++
      (if row.getD ValueTable.header 0*row.getD (ValueTable.sel 3) 0=1 then
        [[row.getD ValueTable.tau 0,0,8,row.getD ValueTable.count 0]] else []) := by
  by_cases hs : row.getD ValueTable.shard 0=1 <;>
    by_cases hc : row.getD ValueTable.header 0*row.getD (ValueTable.sel 3) 0=1
  all_goals simp_all [natRowTraffic,ValueTable.interactions,send,recv,natMultBits,
    rowNatEval_subpos,rowNatEval,c,k,ValueTable.headerEnd,B_QSH,B_VBYTES,ValueTable.B_QVC]

theorem qsh_shard_list (rows : List (List Nat)) :
    rows.flatMap (fun row => if row.getD ValueTable.shard 0=1 then
      [[row.getD ValueTable.tau 0,row.getD ValueTable.entry 0,selectorValue row,
        row.getD ValueTable.byte 0]] else [])=shardMessages rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rw [List.flatMap_cons,ih]
    clear ih
    by_cases h : row.getD ValueTable.shard 0=1
    all_goals simp_all [shardMessages]

theorem qsh_count_list (rows : List (List Nat)) :
    rows.flatMap (fun row => if row.getD ValueTable.header 0*row.getD (ValueTable.sel 3) 0=1 then
      [[row.getD ValueTable.tau 0,0,8,row.getD ValueTable.count 0]] else [])=countMessages rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rw [List.flatMap_cons,ih]
    clear ih
    by_cases h : row.getD ValueTable.header 0*row.getD (ValueTable.sel 3) 0=1
    all_goals simp_all [countMessages]

theorem qsh_natTraffic_perm (rows : List (List Nat)) :
    (rows.flatMap (fun r => natRowTraffic ValueTable.interactions r B_QSH true)).Perm
      (shardMessages rows++countMessages rows) := by
  simp only [natRowTraffic_shards]
  simpa only [qsh_shard_list,qsh_count_list] using
    ZkFormal.Near.Render.perm_flatMap_append rows
      (fun row => if row.getD ValueTable.shard 0=1 then
        [[row.getD ValueTable.tau 0,row.getD ValueTable.entry 0,selectorValue row,
          row.getD ValueTable.byte 0]] else [])
      (fun row => if row.getD ValueTable.header 0*row.getD (ValueTable.sel 3) 0=1 then
        [[row.getD ValueTable.tau 0,0,8,row.getD ValueTable.count 0]] else [])

theorem countMessages_append (xs ys : List (List Nat)) :
    countMessages (xs++ys)=countMessages xs++countMessages ys := by simp [countMessages]

theorem countMessages_flatMap {α : Type} (xs : List α) (f : α → List (List Nat)) :
    countMessages (xs.flatMap f)=xs.flatMap (fun x => countMessages (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,countMessages_append,ih]

theorem wordRows_no_counts (cfg : Config) (offset phase entry : Nat) (bytes regs : Bytes)
    (hp : phase≠0) : countMessages (wordRows cfg offset phase entry bytes regs)=[] := by
  simp [countMessages,wordRows,List.filter_map,Function.comp_def,row,
    ValueTable.header,ValueTable.sel,hp]

theorem headerRows_counts (cfg : Config) (n : Nat) :
    countMessages (wordRows cfg 0 0 0 (u32 n) (u32 n))=[[cfg.tau,0,8,cfg.count]] := by
  simp [countMessages,wordRows,u32,leN,row,ValueTable.header,ValueTable.sel,
    ValueTable.tau,ValueTable.count]

theorem bufferRows_counts (vid tau users : Nat) (es : List ByteBuffer) :
    countMessages (bufferRows vid tau users es)=[[tau,0,8,es.length]] := by
  unfold bufferRows
  rw [countMessages_append,headerRows_counts,countMessages_flatMap]
  have hz : ∀ p ∈ es.zipIdx,
      countMessages (wordRows ⟨vid,tau,users,1,4+24*es.length,es.length⟩ (4+24*p.2) 1 p.2 p.1.shard p.1.index ++
        wordRows ⟨vid,tau,users,1,4+24*es.length,es.length⟩ (12+24*p.2) 2 p.2 p.1.index p.1.index ++
        wordRows ⟨vid,tau,users,1,4+24*es.length,es.length⟩ (20+24*p.2) 3 p.2 p.1.index p.1.index)=[] := by
    intro p _
    simp only [countMessages_append,wordRows_no_counts _ _ _ _ _ _ (by decide : 1≠0),
      wordRows_no_counts _ _ _ _ _ _ (by decide : 2≠0),
      wordRows_no_counts _ _ _ _ _ _ (by decide : 3≠0),List.nil_append]
  rw [List.flatMap_eq_nil_iff.mpr hz]
  rfl

def Record.shardBytes (v : Record) : List Msg :=
  match v.payload with
  | .buffer es => es.zipIdx.flatMap (fun (e,i) =>
      e.shard.zipIdx.map (fun (b,j) => [v.tau,i,j,b.toNat]))
  | _ => []

def Record.shardCount (v : Record) : List Msg :=
  match v.payload with | .buffer es => [[v.tau,0,8,es.length]] | _ => []

theorem Record.shard_messages (v : Record) (hv : v.Valid) :
    shardMessages v.rows=v.shardBytes := by
  cases v with
  | mk vid tau users p =>
    cases p with
    | empty index =>
      simp only [Record.rows,Record.shardBytes,emptyRows,shardMessages_append,
        wordRows_no_shards _ _ _ _ _ _ (by decide : 2≠1),
        wordRows_no_shards _ _ _ _ _ _ (by decide : 3≠1),List.nil_append]
    | buffer es => exact bufferRows_shards vid tau users es hv.1
    | raw bytes =>
      simp only [Record.rows,Record.shardBytes]
      unfold rawRows
      split <;> simp [shardMessages,row,ValueTable.shard,List.filter_map,Function.comp_def]

theorem Record.count_messages (v : Record) : countMessages v.rows=v.shardCount := by
  cases v with
  | mk vid tau users p =>
    cases p with
    | empty index =>
      simp only [Record.rows,Record.shardCount,emptyRows,countMessages_append,
        wordRows_no_counts _ _ _ _ _ _ (by decide : 2≠0),
        wordRows_no_counts _ _ _ _ _ _ (by decide : 3≠0),List.nil_append]
    | buffer es => exact bufferRows_counts vid tau users es
    | raw bytes =>
      simp only [Record.rows,Record.shardCount]
      unfold rawRows
      split <;> simp [countMessages,row,ValueTable.header,List.filter_map,Function.comp_def]

theorem recordsTraffic_shards (vs : List Record) (hv : ∀ v ∈ vs, v.Valid) :
    ((recordsTraffic vs).sends B_QSH).Perm
      (vs.flatMap Record.shardBytes ++ vs.flatMap Record.shardCount) := by
  have hs : shardMessages (recordsRows vs)=vs.flatMap Record.shardBytes := by
    rw [recordsRows,shardMessages_flatMap]
    rw [List.flatMap_def,List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro v hm
    exact v.shard_messages (hv v hm)
  have hc : countMessages (recordsRows vs)=vs.flatMap Record.shardCount := by
    rw [recordsRows,countMessages_flatMap]
    rw [List.flatMap_def,List.flatMap_def]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro v _
    exact v.count_messages
  simpa only [hs,hc,recordsTraffic] using qsh_natTraffic_perm (recordsRows vs)

end ZkFormal.NearV3.Qv.Candidates.ValueGen
