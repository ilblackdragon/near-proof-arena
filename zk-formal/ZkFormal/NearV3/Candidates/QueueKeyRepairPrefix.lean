import ZkFormal.NearV3.Candidates.QueueKeyRepairRows
namespace ZkFormal.NearV3.Candidates.QueueKeyRepair
open NearSpec ZkFormal.Near Qv Qv.Candidates Qv.Candidates.CombinedWalkGen
open ZkFormal.Air ZkFormal.Algebra ValueGen
theorem placed_words_traffic (tr : Trace Fp) (t : Nat) (pub : List Fp) (bus : Nat) (sd : Bool)
    (ws : List Walk) (start : Nat) (msgs : Walk → List (List Fp))
    (hc : ∀ r<(ws.flatMap Walk.rows).length, ∀ c,
      tr.cell t (start+r) c=Fp.ofNat (((ws.flatMap Walk.rows).getD r []).getD c 0))
    (hword : ∀ w ∈ ws, ∀ off,
      (∀ bi ∈ w.kind.bytes.zipIdx, ∀ c,
        tr.cell t (off+bi.2) c=Fp.ofNat ((w.row bi.2 bi.1).getD c 0)) →
      w.kind.bytes.zipIdx.flatMap (fun bi =>
        rowTraffic interactions tr t (off+bi.2) pub bus sd)=msgs w) :
    (List.range (ws.flatMap Walk.rows).length).flatMap (fun r =>
      rowTraffic interactions tr t (start+r) pub bus sd)=ws.flatMap msgs := by
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
    rw [zipIdx_flatMap_positions w.kind.bytes (fun j => rowTraffic interactions tr t (start+j) pub bus sd)] at hh
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
        rowTraffic interactions (mixedTrace ws vs log) 0 (off+bi.2) pub bus sd)=
          (msgs w).map Msg.toFp) :
    (List.range (ws.flatMap Walk.rows).length).flatMap (fun r =>
      rowTraffic interactions (mixedTrace ws vs log) 0 r pub bus sd)=
      (ws.flatMap msgs).map Msg.toFp := by
  have hc := mixedTrace_prefix (F:=Fp) ws vs log 0
  have h := placed_words_traffic (mixedTrace ws vs log) 0 pub bus sd ws 0
    (fun w => (msgs w).map Msg.toFp) (by simpa only [Nat.zero_add,PrefixCells,natCast_eq] using hc) hword
  simpa only [Nat.zero_add,List.map_flatMap] using h

theorem word_field (w : Walk) (tr : Trace Fp) (t off : Nat) (pub : List Fp)
    (hc : ∀bi∈w.kind.bytes.zipIdx,∀c,tr.cell t (off+bi.2) c=Fp.ofNat ((w.row bi.2 bi.1).getD c 0)) :
    w.kind.bytes.zipIdx.flatMap (fun bi=>rowTraffic interactions tr t (off+bi.2) pub B_KEYNIB true)=
      (keyMessages w).map Msg.toFp := by
  rw [←word_messages,List.map_flatMap]
  unfold List.flatMap
  congr 1
  apply List.map_congr_left
  intro bi hbi
  exact field_messages w bi.2 bi.1 tr t (off+bi.2) pub (hc bi hbi)

theorem prefix_keys (ws : List Walk) (vs : List Record) (log : Nat) (pub : List Fp) :
    (List.range (ws.flatMap Walk.rows).length).flatMap (fun r=>
      rowTraffic interactions (mixedTrace ws vs log) 0 r pub B_KEYNIB true)=
      (ws.flatMap keyMessages).map Msg.toFp := by
  apply mixedTrace_prefix_word_messages
  intro w _ off hc
  exact word_field w _ 0 off pub hc

end ZkFormal.NearV3.Candidates.QueueKeyRepair
