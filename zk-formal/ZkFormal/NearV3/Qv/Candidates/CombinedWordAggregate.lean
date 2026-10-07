import ZkFormal.NearV3.Qv.Candidates.CombinedWordTraffic
import ZkFormal.NearV3.Qv.Candidates.CombinedParserTraffic

namespace ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ValueGen

theorem zipIdx_positions {α : Type} (xs : List α) : xs.zipIdx.map Prod.snd=List.range xs.length := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

theorem zipIdx_flatMap_positions {α β : Type} (xs : List α) (f : Nat → List β) :
    xs.zipIdx.flatMap (fun bi => f bi.2)=(List.range xs.length).flatMap f := by
  rw [← List.flatMap_map,zipIdx_positions]

/-- Aggregation at physical offsets preserves the complete ordered message list.
The per-word premise is discharged by checked word traffic equations. -/
theorem placed_words_traffic (tr : Trace Fp) (t : Nat) (pub : List Fp) (bus : Nat) (sd : Bool)
    (ws : List Walk) (start : Nat) (msgs : Walk → List (List Fp))
    (hc : ∀ r<(ws.flatMap Walk.rows).length, ∀ c,
      tr.cell t (start+r) c=Fp.ofNat (((ws.flatMap Walk.rows).getD r []).getD c 0))
    (hword : ∀ w ∈ ws, ∀ off,
      (∀ bi ∈ w.kind.bytes.zipIdx, ∀ c,
        tr.cell t (off+bi.2) c=Fp.ofNat ((w.row bi.2 bi.1).getD c 0)) →
      w.kind.bytes.zipIdx.flatMap (fun bi =>
        rowTraffic CombinedTable.interactions tr t (off+bi.2) pub bus sd)=msgs w) :
    (List.range (ws.flatMap Walk.rows).length).flatMap (fun r =>
      rowTraffic CombinedTable.interactions tr t (start+r) pub bus sd)=ws.flatMap msgs := by
  induction ws generalizing start with
  | nil => simp
  | cons w ws ih =>
    have hcw : ∀ bi ∈ w.kind.bytes.zipIdx, ∀ c,
        tr.cell t (start+bi.2) c=Fp.ofNat ((w.row bi.2 bi.1).getD c 0) := by
      intro bi hbi c
      have he := List.mem_zipIdx_iff_getElem?.mp hbi
      have hp : bi.2<w.kind.bytes.length := by
        have := List.getElem?_eq_some_iff.mp he
        exact this.1
      rw [hc bi.2 (by simp only [List.flatMap_cons,List.length_append,Walk.rows_length]; omega) c]
      simp only [List.flatMap_cons,append_getD_left w.rows (ws.flatMap Walk.rows) bi.2 [] (by simpa [Walk.rows_length] using hp),
        Walk.rows_at w bi.2 hp,List.getD_eq_getElem?_getD,he,Option.getD_some]
    have htail : ∀ r<(ws.flatMap Walk.rows).length, ∀ c,
        tr.cell t (start+w.kind.bytes.length+r) c=
          Fp.ofNat (((ws.flatMap Walk.rows).getD r []).getD c 0) := by
      intro r hr c
      rw [show start+w.kind.bytes.length+r=start+(w.rows.length+r) by rw [Walk.rows_length]; omega]
      rw [hc _ (by simp only [List.flatMap_cons,List.length_append]; omega) c]
      simp only [List.flatMap_cons,append_getD_offset]
    have ht := ih (start+w.kind.bytes.length) htail (fun v hv => hword v (by simp [hv]))
    have hh := hword w (by simp) start hcw
    rw [zipIdx_flatMap_positions w.kind.bytes (fun j => rowTraffic CombinedTable.interactions tr t (start+j) pub bus sd)] at hh
    simp only [List.flatMap_cons,List.length_append,Walk.rows_length,List.range_add,
      List.flatMap_append,List.flatMap_map]
    rw [hh]
    simpa only [Nat.add_assoc] using congrArg (fun xs => msgs w++xs) ht

theorem mixedTrace_prefix_word_messages (ws : List Walk) (vs : List Record) (log : Nat)
    (pub : List Fp) (bus : Nat) (sd : Bool) (msgs : Walk → List Msg)
    (hword : ∀ w ∈ ws, ∀ off,
      (∀ bi ∈ w.kind.bytes.zipIdx, ∀ c,
        (mixedTrace ws vs log).cell 0 (off+bi.2) c=Fp.ofNat ((w.row bi.2 bi.1).getD c 0)) →
      w.kind.bytes.zipIdx.flatMap (fun bi =>
        rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 (off+bi.2) pub bus sd)=
          (msgs w).map Msg.toFp) :
    (List.range (ws.flatMap Walk.rows).length).flatMap (fun r =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub bus sd)=
      (ws.flatMap msgs).map Msg.toFp := by
  have hc := mixedTrace_prefix (F:=Fp) ws vs log 0
  have h := placed_words_traffic (mixedTrace ws vs log) 0 pub bus sd ws 0
    (fun w => (msgs w).map Msg.toFp) (by simpa only [Nat.zero_add,PrefixCells,natCast_eq] using hc) hword
  simpa only [Nat.zero_add,List.map_flatMap] using h

def Walk.finalWordMessages (w : Walk) : List Msg :=
  [[W_QV+w.tau+64*w.slot,w.tau,(!w.value.isSome).toNat,if w.value.isSome then w.vid else 0]]

def Walk.counterWordMessages (w : Walk) (sd : Bool) : List Msg :=
  if w.value.isSome then [[w.vid,w.tau,w.mode,if sd then w.users+1 else w.users]] else []

theorem mixedTrace_prefix_key (ws : List Walk) (vs : List Record) (log : Nat) (pub : List Fp) :
    (List.range (ws.flatMap Walk.rows).length).flatMap (fun r =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub B_KEYNIB true)=
      (ws.flatMap Walk.keyWordMessages).map Msg.toFp := by
  apply mixedTrace_prefix_word_messages
  intro w _ off hc
  exact w.key_word_field _ 0 off pub hc

theorem mixedTrace_prefix_final (ws : List Walk) (vs : List Record) (log : Nat) (pub : List Fp) :
    (List.range (ws.flatMap Walk.rows).length).flatMap (fun r =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub B_FINAL false)=
      (ws.flatMap Walk.finalWordMessages).map Msg.toFp := by
  apply mixedTrace_prefix_word_messages
  intro w _ off hc
  exact w.final_word_field _ 0 off pub hc

theorem mixedTrace_prefix_counter (ws : List Walk) (vs : List Record) (log : Nat) (pub : List Fp)
    (sd : Bool) :
    (List.range (ws.flatMap Walk.rows).length).flatMap (fun r =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub ValueTable.B_QVC sd)=
      (ws.flatMap (fun w => w.counterWordMessages sd)).map Msg.toFp := by
  apply mixedTrace_prefix_word_messages
  intro w _ off hc
  exact w.counter_word_field _ 0 off pub sd hc

theorem mixedTrace_prefix_shard (ws : List Walk) (vs : List Record) (log : Nat) (pub : List Fp)
    (hs : ∀ w ∈ ws,w.kind.code=3 → 3≤w.slot) :
    (List.range (ws.flatMap Walk.rows).length).flatMap (fun r =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub B_QSH false)=
      (ws.flatMap Walk.shardWordMessages).map Msg.toFp := by
  apply mixedTrace_prefix_word_messages
  intro w hw off hc
  exact w.shard_word_field _ 0 off pub hc (hs w hw)

/-- Actual physical QVC traffic, ready for the allocator's rank-chain theorem. -/
theorem mixedTrace_counter_messages (ws : List Walk) (vs : List Record)
    (hv : ∀ v ∈ vs,v.Valid) (log : Nat) (pub : List Fp) (sd : Bool)
    (hfit : (ws.flatMap Walk.rows).length+recordsSize vs≤2^log) :
    ((List.range (2^log)).flatMap (fun r =>
      rowTraffic CombinedTable.interactions (mixedTrace ws vs log) 0 r pub ValueTable.B_QVC sd)).Perm
      ((ws.flatMap (fun w => w.counterWordMessages sd) ++
        (if sd then vs.map (fun v => [v.vid,v.tau,v.mode,0])
         else vs.map (fun v => [v.vid,v.tau,v.mode,v.users]))).map Msg.toFp) := by
  have h := mixedTrace_traffic_split ws vs hv log pub ValueTable.B_QVC sd hfit
  rw [mixedTrace_prefix_counter] at h
  simpa only [canonicalTraffic,show ValueTable.B_QVC≠B_VBYTES by decide,
    ite_false,ite_true,List.map_append] using h

end ZkFormal.NearV3.Qv.Candidates.CombinedWalkGen
