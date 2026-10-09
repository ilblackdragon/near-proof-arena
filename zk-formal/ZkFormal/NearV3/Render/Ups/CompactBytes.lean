import ZkFormal.NearV3.Render.Ups.CompactFields
import ZkFormal.NearV3.Render.Ups.GBytes
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Near.Render.EvI ZkFormal.Algebra ZkFormal.Air
  ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3 UpsGen

private theorem member_flatMap_length {α β : Type} (xs : List α) (f : α→List β)
    (a : α) (ha : a∈xs) : (f a).length≤(xs.flatMap f).length := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha
    simp only [List.flatMap_cons,List.length_append]
    rcases ha with rfl|ha
    · omega
    · have := ih ha; omega

theorem compact_part_length {insts : List UpsInst} {i k : Nat} (hi : i<insts.length)
    (hk : k<nQ (inst insts i)) : (part (inst insts i) k).q.length≤compactR insts := by
  have hp:=member_flatMap_length (List.range (nQ (inst insts i)))
    (fun k=>(List.range (part (inst insts i) k).q.length).map (RK.q k)) k (by simpa)
  have hr:=member_flatMap_length (List.range insts.length)
    (fun j=>(compactRecsI (inst insts j)).map ((j,·))) i (by simpa)
  simp only [List.length_map,List.length_range] at hp hr
  have hh : (compactRecsI (inst insts i)).length=4+
      ((List.range (nQ (inst insts i))).flatMap fun k=>
        (List.range (part (inst insts i) k).q.length).map (RK.q k)).length := by
    simp [compactRecsI]
  change (compactRecsI (inst insts i)).length≤(compactRecs insts).length at hr
  rw [compactRecs_length] at hr
  omega

theorem compact_cByteCopy {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (hc : ∀ I ∈ insts, ∀ k, k < nQ I → CopyFields I (part I k))
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    (hk : ∀ I ∈ insts, ∀ k, k < nQ I → (part I k).kind<12)
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cByteCopy := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteCopy.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi k p hk' hp q _ _ C D P hC _
    exact byte_copy_q (hc _ (inst_mem hi) k hk') (hf _ (inst_mem hi) k hk')
      (hk _ (inst_mem hi) k hk') hp hC

theorem compact_cByteEditPositions {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (he : ∀ I ∈ insts, ∀ k, k < nQ I → (part I k).kind ∈ [0,1,2,3,4,5,11] → SourceLayout (part I k))
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cByteEditPositions := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteEditPositions.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_edit_positions_q (he _ (inst_mem hi) k hk) (hf _ (inst_mem hi) k hk) hp hC

theorem compact_cByteFlags {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    (hk : ∀ I ∈ insts, ∀ k, k < nQ I → (part I k).kind < 12)
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cByteFlags := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_take he
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteFlags.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi k p hki hp q _ _ C D P hC _
    exact byte_flags_q (hk _ (inst_mem hi) k hki) ((hf _ (inst_mem hi) k hki).state hp) hC

theorem compact_cByteFreshPrefix {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (he : ∀ I ∈ insts, ∀ k, k < nQ I → NodeEncoding (part I k))
    (hpref : ∀ I (hI : I ∈ insts) k (hk : k < nQ I), FreshPrefix I (part I k) (he I hI k hk))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cByteFreshPrefix := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteFreshPrefix.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_fresh_prefix_q (he _ (inst_mem hi) k hk) (hpref _ (inst_mem hi) k hk) hp hC

theorem compact_cByteFreshValue {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (he : ∀ I ∈ insts, ∀ k, k < nQ I → NodeEncoding (part I k))
    (hv : ∀ I (hI : I ∈ insts) k (hk : k < nQ I), FreshValue I (part I k) (he I hI k hk))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cByteFreshValue := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteFreshValue.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_fresh_value_q (he _ (inst_mem hi) k hk) (hv _ (inst_mem hi) k hk) (hinst _ (inst_mem hi)).Lsmall hp hC

theorem compact_cByteHeaders {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (he : ∀ I ∈ insts, ∀ k, k < nQ I → NodeEncoding (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cByteHeaders := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteHeaders.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_headers_q (he _ (inst_mem hi) k hk) hp hC

theorem compact_cByteHpl {insts : List UpsInst} (hcap : compactR insts≤2^22) (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (he : ∀ I∈insts, ∀ k, k<nQ I → NodeEncoding (part I k))
    (hf : ∀ I∈insts, ∀ k, k<nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts+1≤H) : CompactGroupOk insts H cByteHpl := by
  apply compact_groupOk_by hpos hH (fun e h => by
    have hm : e∈UpsV3.cBytes := List.mem_of_mem_drop h
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc:=zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteHpl.all (vz zW (fun _ => false) false false false)=true by decide) ex hex)
  · intro i hi k p hk hpp q hq hr C D P hC hD
    have enc := he _ (inst_mem hi) k hk
    by_cases hn : p+1<(part (inst insts i) k).q.length
    · apply byte_hpl_qmid enc (hf _ (inst_mem hi) k hk) hpp hn
        (by have := compact_part_length hi hk; have := enc.hplen_le_length; omega)
        hC
      intro x hx
      rw [hD x hx,compact_nextRow hpos hinst hq hr (rk':=.q k (p+1)) (by simp [compactNext,nextRK,hn]),compactRowCell_q]
    · have hl : p+1=(part (inst insts i) k).q.length := by omega
      have hs := (((hinst _ (inst_mem hi)).memEnd k hk p hpp).1 hl).1
      exact byte_hpl_off (by omega) hC

theorem compact_cByteMovedPrefix {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (he : ∀ I ∈ insts, ∀ k, k < nQ I → NodeEncoding (part I k))
    (hm : ∀ I (hI : I ∈ insts) k (hk : k < nQ I),
      (part I k).kind=6 ∨ (part I k).kind=7 → MovedPrefix I (part I k) (he I hI k hk))
    (hb : ∀ I ∈ insts, ∀ k, k < nQ I → SourceBytes (part I k))
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cByteMovedPrefix := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteMovedPrefix.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_moved_prefix_q (he _ (inst_mem hi) k hk) (hm _ (inst_mem hi) k hk)
      (hb _ (inst_mem hi) k hk) (hf _ (inst_mem hi) k hk) hp hC

theorem compact_cByteOffsets {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cByteOffsets := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteOffsets.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_offsets_q ((hf _ (inst_mem hi) k hk).state hp) hC

theorem compact_cBytePositions {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cBytePositions := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := by
      rcases List.mem_append.1 he with h | h <;>
        exact List.mem_of_mem_drop (List.mem_of_mem_take h)
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cBytePositions.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_positions_q ((hf _ (inst_mem hi) k hk).state hp) hC

theorem compact_cByteReadBits {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (hb : ∀ I ∈ insts, ∀ k, k < nQ I → SourceBytes (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cByteReadBits := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := by
      rcases List.mem_append.1 he with h | h <;>
        exact List.mem_of_mem_drop (List.mem_of_mem_take h)
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteReadBits.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_read_bits_q (hb _ (inst_mem hi) k hk) hC

theorem compact_cByteSourceHeader {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (hi : ∀ I ∈ insts, ∀ k, k < nQ I → HeaderInput I (part I k))
    (hb : ∀ I ∈ insts, ∀ k, k < nQ I → SourceBytes (part I k))
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cByteSourceHeader := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := by
      rcases List.mem_append.1 he with h | h <;>
        exact List.mem_of_mem_drop (List.mem_of_mem_take h)
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteSourceHeader.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi' k p hk hp q _ _ C D P hC _
    exact byte_source_header_q (hi _ (inst_mem hi') k hk) (hb _ (inst_mem hi') k hk)
      (hf _ (inst_mem hi') k hk) hp hC

theorem compact_cByteSourceValue {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (he : ∀ I ∈ insts, ∀ k, k < nQ I → NodeEncoding (part I k))
    (hv : ∀ I (hI : I ∈ insts) k (hk : k < nQ I),
      ((part I k).ty=0 ∨ (part I k).ty=3) → VcpB I (part I k)=true ∨ (part I k).kind=3 → SourceValueLayout I (part I k) (he I hI k hk))
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cByteSourceValue := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteSourceValue.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_source_value_q (he _ (inst_mem hi) k hk) (hv _ (inst_mem hi) k hk)
      (hf _ (inst_mem hi) k hk) hp hC

theorem compact_cByteSplitBitmap {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (he : ∀ I ∈ insts, ∀ k, k < nQ I → NodeEncoding (part I k))
    (hb : ∀ I (hI : I ∈ insts) k (hk : k < nQ I), SplitBitmap I (part I k) (he I hI k hk))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cByteSplitBitmap := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteSplitBitmap.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact byte_split_bitmap_q (he _ (inst_mem hi) k hk) (hb _ (inst_mem hi) k hk) hp hC

theorem compact_cFreshByte {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cFreshByte := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cFreshByte.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi k p hk hp q _ _ C D P hC _
    exact fresh_byte_q (hf _ (inst_mem hi) k hk) hp hC

theorem compact_cByteShifts {insts : List UpsInst} (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (hf : ∀ I ∈ insts, ∀ k, k < nQ I → FieldsOk (part I k))
    {H : Nat} (hH : compactR insts + 1 ≤ H) : CompactGroupOk insts H cByteShifts := by
  apply compact_groupOk_by hpos hH (fun e he => by
    have hm : e ∈ UpsV3.cBytes := List.mem_of_mem_drop (List.mem_of_mem_take he)
    simp [compactConstraints,hm])
  · intro i hi t ht q _ _ C D P hC _ ex hex
    exact vzC (zc := zW) (fun x hx => by
      rw [hC x (by simp [zW] at hx; omega)]; exact zW_cell _ _ _ hx)
      (List.all_eq_true.1 (show cByteShifts.all (vz zW (fun _ => false) false false false) = true by decide) ex hex)
  · intro i hi k p hk hp q hq hr C D P hC hD
    by_cases hp1 : p+1 < (part (inst insts i) k).q.length
    · apply byte_shifts_qmid (hf _ (inst_mem hi) k hk) hp hC
      intro x hx
      rw [hD x hx,compact_nextRow hpos hinst hq hr (rk' := .q k (p+1)) (by simp [compactNext,nextRK,hp1]),compactRowCell_q]
    · have he : p+1 = (part (inst insts i) k).q.length := by omega
      have hs := (((hinst _ (inst_mem hi)).memEnd k hk p hp).1 he).1
      apply byte_shifts_off
      rw [ev_fresh hC]
      simp [winFrV,WinFrB,ind,hs]

theorem compact_cBytes {insts : List UpsInst} (hcap : compactR insts≤2^22) (hpos : 0<insts.length) (hinst : ∀I∈insts,InstOk I)
    (hi : ∀ I ∈ insts, ∀ k, k<nQ I → ByteInput I (part I k))
    {H : Nat} (hH : compactR insts+1≤H) : CompactGroupOk insts H UpsV3.cBytes := by
  let he := fun I hI k hk => (hi I hI k hk).output
  have hf := fun I hI k hk => (hi I hI k hk).fieldsOk
  have hk := fun I hI k hk => (hi I hI k hk).kind
  have hb := fun I hI k hk => (hi I hI k hk).sourceBytes
  have hall : CompactGroupOk insts H byteGroups := by
    unfold byteGroups
    exact (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_groupOk_append (compact_cByteFlags hpos hinst hf hk hH)
      (compact_cByteCopy hpos hinst (fun I hI k hk => (hi I hI k hk).copyFields) hf hk hH))
      (compact_cByteHeaders hpos hinst he hH))
      (compact_cByteMovedPrefix hpos hinst he (fun I hI k hk => (hi I hI k hk).movedPrefix) hb hf hH))
      (compact_cByteFreshPrefix hpos hinst he (fun I hI k hk => (hi I hI k hk).freshPrefix) hH))
      (compact_cByteFreshValue hpos hinst he (fun I hI k hk => (hi I hI k hk).freshValue) hH))
      (compact_cFreshByte hpos hinst hf hH))
      (compact_cByteShifts hpos hinst hf hH))
      (compact_cByteSplitBitmap hpos hinst he (fun I hI k hk => (hi I hI k hk).splitBitmap) hH))
      (compact_cByteReadBits hpos hinst hb hH))
      (compact_cByteSourceHeader hpos hinst (fun I hI k hk => (hi I hI k hk).sourceHeader) hb hf hH))
      (compact_cByteSourceValue hpos hinst he (fun I hI k hk => (hi I hI k hk).sourceValue) hf hH))
      (compact_cBytePositions hpos hinst hf hH))
      (compact_cByteEditPositions hpos hinst (fun I hI k hk => (hi I hI k hk).sourceLayout) hf hH))
      (compact_cByteOffsets hpos hinst hf hH))
      (compact_cByteHpl hcap hpos hinst he hf hH))
  intro q hq C D P hC hD e he
  exact hall q hq C D P hC hD e (byteGroups_cover he)

end ZkFormal.NearV3.Render.UpsRelay
