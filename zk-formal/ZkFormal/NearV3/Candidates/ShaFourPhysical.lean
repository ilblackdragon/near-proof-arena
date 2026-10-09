import ZkFormal.NearV3.Candidates.ShaHeight.Packed
import ZkFormal.NearV3.Candidates.HorizontalPack
import ZkFormal.NearV3.Rcpt.Candidates.ShaAllocationTraffic

namespace ZkFormal.NearV3.Candidates.ShaFourPhysical
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Sha
open ZkFormal.NearV3.Rcpt.Candidates ZkFormal.NearV3.Assembly

/-- Physical SHA components, with actual packed cells at the common fusion clock. -/
def components (bins : List (List Gen.Msg)) : List HorizontalPack.Component :=
  bins.map (fun bin=>(ShaCarryKinds.table B_BYTES B_DIGEST,ShaHeight.packedTrace bin))

/-- Byte and length validity survive allocation because whole jobs are retained. -/
theorem bins_ok (bins : List (List Gen.Msg)) (ms : List Gen.Msg)
    (hp : bins.flatten.Perm ms) (hr : ∀bin∈bins,(Gen.honestRows bin).length≤2^22)
    (hb : ∀M∈ms,∀x∈M.bytes,x<256) :
    ∀bin∈bins,MsgsOk bin := by
  intro bin hbin
  have hm : ∀M∈bin,M∈ms := by
    intro M hM
    exact hp.mem_iff.mp (List.mem_flatten.mpr ⟨bin,hbin,hM⟩)
  exact ⟨fun M hM=>hb M (hm M hM),fun M hM=>sha_message_len_of_rows (hr bin hbin) hM,hr bin hbin⟩

theorem components_local (bins : List (List Gen.Msg)) (pub : List Fp)
    (h : ∀bin∈bins,MsgsOk bin) :
    ∀x∈components bins,TableLocal x.1 x.2 0 pub ∧ x.2.log 0=22 := by
  intro x hx
  obtain ⟨bin,hbin,rfl⟩ := List.mem_map.mp hx
  exact ⟨ShaHeight.packed_local bin (h bin hbin) 0 B_BYTES B_DIGEST pub,rfl⟩

private theorem count_flat {α β : Type} [BEq β] (xs : List α) (f : α→List β) (m : β) :
    (xs.map (fun x=>(f x).count m)).sum=(xs.flatMap f).count m := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih,List.count_append]

/-- All concrete allocated bytes are received exactly once per occurrence. -/
theorem components_bytes (bins : List (List Gen.Msg)) (ms : List Gen.Msg) (pub : List Fp)
    (hp : bins.flatten.Perm ms) (h : ∀bin∈bins,MsgsOk bin) (m : List Fp) :
    HorizontalFamily.count (components bins) pub B_BYTES false m=
      ((Gen.expectedBytes ms).map Msg.toFp).count m := by
  unfold HorizontalFamily.count components
  simp only [List.map_map,Function.comp_def]
  have he : bins.map (fun bin=>tableBusCount (ShaCarryKinds.table B_BYTES B_DIGEST).interactions
      (ShaHeight.packedTrace bin) 0 pub B_BYTES false m)=
      bins.map (fun bin=>((Gen.expectedBytes bin).map Msg.toFp).count m) := by
    apply List.map_congr_left
    intro bin hbin
    have ht := (ShaHeight.packed_traffic bin (h bin hbin) 0 pub) B_BYTES m
    simpa [shaBinTraffic] using ht.2
  rw [he,count_flat]
  have hp' := ((allocated_bytes hp).map Msg.toFp).count_eq m
  simpa only [List.map_flatMap] using hp'

/-- DIGEST supply retains each complete job's original multiplicity flag. -/
theorem components_digests (bins : List (List Gen.Msg)) (ms : List Gen.Msg) (pub : List Fp)
    (hp : bins.flatten.Perm ms) (h : ∀bin∈bins,MsgsOk bin) (m : List Fp) :
    HorizontalFamily.count (components bins) pub B_DIGEST true m=
      ((Gen.expectedDigests ms).map Msg.toFp).count m := by
  unfold HorizontalFamily.count components
  simp only [List.map_map,Function.comp_def]
  have he : bins.map (fun bin=>tableBusCount (ShaCarryKinds.table B_BYTES B_DIGEST).interactions
      (ShaHeight.packedTrace bin) 0 pub B_DIGEST true m)=
      bins.map (fun bin=>((Gen.expectedDigests bin).map Msg.toFp).count m) := by
    apply List.map_congr_left
    intro bin hbin
    have ht := (ShaHeight.packed_traffic bin (h bin hbin) 0 pub) B_DIGEST m
    simpa [shaBinTraffic] using ht.1
  rw [he,count_flat]
  have hp' := ((allocated_digests hp).map Msg.toFp).count_eq m
  simpa only [List.map_flatMap] using hp'

theorem components_tables (bins : List (List Gen.Msg)) :
    (components bins).map Prod.fst=List.replicate bins.length (ShaCarryKinds.table B_BYTES B_DIGEST) := by
  induction bins with
  | nil => rfl
  | cons bin bins ih => simp [components,List.map_map,Function.comp_def] at ih ⊢; rw [ih]; rfl

/-- The checked four-bin allocator now produces actual packed physical traces,
not only a weight partition. Native payload byte validity remains explicit. -/
theorem allocated_components (scheduler native receipt source : List Gen.Msg) (pub : List Fp)
    (hs : (Gen.honestRows scheduler).length≤1663260)
    (hv : (Gen.honestRows native).length≤2925275)
    (hr : (Gen.honestRows receipt).length≤1373299)
    (hp : (Gen.honestRows source).length≤8932712)
    (hm : ∀M∈source,(Gen.msgRows M).length≤35)
    (hb : ∀M∈scheduler++native++receipt++source,∀x∈M.bytes,x<256) :
    let bins := fourShaJobBins (fun M : Gen.Msg=>(Gen.msgRows M).length) scheduler native receipt source
    let xs := components bins
    xs.map Prod.fst=List.replicate 4 (ShaCarryKinds.table B_BYTES B_DIGEST) ∧
    (∀x∈xs,TableLocal x.1 x.2 0 pub ∧ x.2.log 0=22) ∧
    (∀m,HorizontalFamily.count xs pub B_BYTES false m=
      ((Gen.expectedBytes (scheduler++native++receipt++source)).map Msg.toFp).count m) ∧
    (∀m,HorizontalFamily.count xs pub B_DIGEST true m=
      ((Gen.expectedDigests (scheduler++native++receipt++source)).map Msg.toFp).count m) := by
  obtain ⟨hn,hrows,hperm⟩ := fourSha_physical_fit scheduler native receipt source hs hv hr hp hm
  have hok := bins_ok _ _ hperm hrows hb
  exact ⟨by rw [components_tables,hn],components_local _ pub hok,
    components_bytes _ _ pub hperm hok,components_digests _ _ pub hperm hok⟩

/-- The allocated physical SHA family has no traffic on any other channel. -/
theorem components_isolated (bins : List (List Gen.Msg)) (pub : List Fp)
    (h : ∀bin∈bins,MsgsOk bin) (bs br : Nat) (hs : bs≠B_DIGEST) (hr : br≠B_BYTES) (m : List Fp) :
    HorizontalFamily.count (components bins) pub bs true m=0 ∧
    HorizontalFamily.count (components bins) pub br false m=0 := by
  induction bins with
  | nil => exact ⟨rfl,rfl⟩
  | cons bin bins ih =>
    have hk := h bin (by simp)
    have hbs := (ShaHeight.packed_traffic bin hk 0 pub) bs m
    have hbr := (ShaHeight.packed_traffic bin hk 0 pub) br m
    have hz1 : tableBusCount (ShaCarryKinds.table B_BYTES B_DIGEST).interactions
        (ShaHeight.packedTrace bin) 0 pub bs true m=0 := by
      simpa [shaBinTraffic,hs] using hbs.1
    have hz2 : tableBusCount (ShaCarryKinds.table B_BYTES B_DIGEST).interactions
        (ShaHeight.packedTrace bin) 0 pub br false m=0 := by
      simpa [shaBinTraffic,hr] using hbr.2
    have hi := ih (fun bin hbin=>h bin (by simp [hbin]))
    change _+HorizontalFamily.count (components bins) pub bs true m=0 ∧
      _+HorizontalFamily.count (components bins) pub br false m=0
    dsimp only
    rw [hz1,hz2,hi.1,hi.2]
    exact ⟨rfl,rfl⟩

end ZkFormal.NearV3.Candidates.ShaFourPhysical
