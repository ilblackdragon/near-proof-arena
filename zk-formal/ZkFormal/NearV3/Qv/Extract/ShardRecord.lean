import ZkFormal.NearV3.Qv.Extract.ShardRows

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

theorem flatMap_range_blocks {α : Type} (s w k : Nat) (f : Nat → List α) :
    (List.range' s (w*k)).flatMap f=
      (List.range k).flatMap (fun j => (List.range' (s+w*j) w).flatMap f) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ,←List.range'_append_1,List.flatMap_append,ih,List.range_succ,List.flatMap_append]
    simp

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp} {s n : Nat}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (hfit : s+n≤tr.height tt)
variable (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
variable (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
variable (hm : tr.cell tt s mBuffer=1)
include hL hfit hw hs hm

theorem buffered_shard_byte_row (j : Nat) (hj : j<cv tr tt s count) (i : Nat) (hi : i<8) :
    rowTraffic Candidates.CombinedTable.interactions tr tt (s+4+24*j+i) pub B_QSH true=
      [[tr.cell tt s tau,(j:Fp),(i:Fp),tr.cell tt (s+4+24*j+i) byte]] := by
  have hstr := buffered_structure hL hfit hw hs hm
  have row := (hstr.2 j hj).2 i hi
  have hr : s+4+24*j+i<tr.height tt := by omega
  have hwalk := hw (s+4+24*j+i) (by omega) (by omega)
  rw [shard_selected_row hL hr hwalk row.1 hi row.2.1]
  have htau := metadata hL hfit hw hs (x:=tau) (by simp) (s+4+24*j+i) (by omega) (by omega)
  have start := (hstr.2 j hj).2 0 (by omega)
  simp only [Nat.add_zero] at start
  have he := buffered_entry_constant hL hfit hw hs hm (r:=s+4+24*j) (by omega) (by omega)
    start.1 start.2.1 (s+4+24*j+i) (by omega) (by omega)
  rw [htau,he,(hstr.2 j hj).1]

theorem buffered_shard_index_silent (j : Nat) (hj : j<cv tr tt s count)
    (i : Nat) (hi : i<16) :
    rowTraffic Candidates.CombinedTable.interactions tr tt (s+4+24*j+8+i) pub B_QSH true=[] := by
  have hstr := buffered_structure hL hfit hw hs hm
  have hr : s+4+24*j+8+i<tr.height tt := by omega
  have hwalk := hw (s+4+24*j+8+i) (by omega) (by omega)
  by_cases hf : i<8
  · exact shard_nonphase_row hL hr hwalk (x:=firstIndex) (by simp) ((hstr.2 j hj).2 i hf).2.2.1 true
  · have hn := ((hstr.2 j hj).2 (i-8) (by omega)).2.2.2.1
    have he : s+4+24*j+16+(i-8)=s+4+24*j+8+i := by omega
    rw [he] at hn
    exact shard_nonphase_row hL hr hwalk (x:=nextIndex) (by simp) hn true

/-- The four physical header rows emit exactly one count message. -/
theorem buffered_shard_header :
    (List.range' s 4).flatMap (fun r =>
      rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH true)=
      [[tr.cell tt s tau,0,8,tr.cell tt s count]] := by
  let f := fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH true
  have early : ∀ i, i<3 → f (s+i)=[] := by
    intro i hi
    obtain ⟨hb,hp,hsel⟩ := buffered_header_rows hL hfit hw hs hm i (by omega)
    exact shard_header_early hL (by omega) (hw (s+i) (by omega) (by omega)) hp hi hsel true
  obtain ⟨hb,hp,hsel⟩ := buffered_header_rows hL hfit hw hs hm 3 (by omega)
  have last : f (s+3)=[[tr.cell tt s tau,0,8,tr.cell tt s count]] := by
    dsimp only [f]
    rw [shard_header_row hL (by omega) (hw (s+3) (by omega) (by omega)) hp hsel,
      metadata hL hfit hw hs (x:=tau) (by simp) (s+3) (by omega) (by omega),
      metadata hL hfit hw hs (x:=count) (by simp) (s+3) (by omega) (by omega)]
  have h0 := early 0 (by omega)
  have h1 := early 1 (by omega)
  have h2 := early 2 (by omega)
  simp only [Nat.add_zero] at h0
  change (List.range' s 4).flatMap f=_
  simp [List.range'_succ,Nat.add_assoc,h0,h1,h2,last]

/-- Each physical entry emits precisely its ordered eight shard bytes. -/
theorem buffered_shard_entry (j : Nat) (hj : j<cv tr tt s count) :
    (List.range' (s+4+24*j) 24).flatMap (fun r =>
      rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH true)=
    (List.range 8).map (fun (i : Nat) => [tr.cell tt s tau,(j:Fp),(i:Fp),tr.cell tt (s+4+24*j+i) byte]) := by
  let f := fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH true
  have hsilent : (List.range' (s+4+24*j+8) 16).flatMap f=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    obtain ⟨i,hi,he⟩ := List.mem_range'.mp hr
    simp only [Nat.one_mul] at he
    rw [he]
    exact buffered_shard_index_silent hL hfit hw hs hm j hj i hi
  change (List.range' (s+4+24*j) (8+16)).flatMap f=_
  rw [←List.range'_append_1,List.flatMap_append,hsilent,List.append_nil,List.range'_eq_map_range,List.flatMap_map]
  have gen {α β : Type} (l : List α) (g : α → List β) (v : α → β)
      (h : ∀ x∈l,g x=[v x]) : l.flatMap g=l.map v := by
    induction l with
    | nil => rfl
    | cons x xs ih =>
      rw [List.flatMap_cons,h x (by simp),ih (fun y hy => h y (by simp [hy]))]
      rfl
  apply gen
  intro i hi
  exact buffered_shard_byte_row hL hfit hw hs hm j hj i (List.mem_range.mp hi)

/-- Exact ordered QSH sends of a complete buffered parser record. -/
theorem buffered_shard_segment :
    (List.range' s n).flatMap (fun r =>
      rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH true)=
    [[tr.cell tt s tau,0,8,tr.cell tt s count]] ++
      (List.range (cv tr tt s count)).flatMap (fun (j : Nat) =>
        (List.range 8).map (fun (i : Nat) =>
          [tr.cell tt s tau,(j:Fp),(i:Fp),tr.cell tt (s+4+24*j+i) byte])) := by
  have hlen := (buffered_structure hL hfit hw hs hm).1
  rw [hlen,←List.range'_append_1,List.flatMap_append,
    buffered_shard_header hL hfit hw hs hm,flatMap_range_blocks]
  apply congrArg (fun xs => [[tr.cell tt s tau,0,8,tr.cell tt s count]]++xs)
  rw [List.flatMap_def,List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  exact buffered_shard_entry hL hfit hw hs hm j (List.mem_range.mp hj)

end ZkFormal.NearV3.Qv.Extract.Parser
