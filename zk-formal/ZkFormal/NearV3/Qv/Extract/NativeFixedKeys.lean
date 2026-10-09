import ZkFormal.NearV3.Qv.Extract.NativeGroupKey

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

/-- A non-group walk consists exactly of its authenticated header byte. -/
theorem singleton_walk_key {tr : Trace Fp} {tt s n : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (hfit : s+n≤tr.height tt)
    (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s n)
    (hz : tr.cell tt s lo=0 ∨ tr.cell tt s hi=0) (b : UInt8)
    (hb : tr.cell tt s wb=(b.toNat:Fp)) : physicalWalkBytes tr tt (s,n)=[b] := by
  have hn := (walk_kind_length hL hfit hs).2 hz
  simp only [physicalWalkBytes,hn,List.range_succ,List.range_zero,
    List.map_cons,List.map_nil,List.nil_append,Nat.add_zero,List.cons.injEq,and_true]
  unfold cv
  rw [hb]
  change UInt8.ofNat (Fp.ofNat b.toNat).toNat=b
  have hbyte := UInt8.toNat_lt b
  have hp : 256<P := by decide
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (show b.toNat<P by omega),UInt8.ofNat_toNat]

/-- The three leading main walks have exactly the native delayed/buffered/yield keys. -/
theorem main_fixed_key {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
    (j : Nat) (hj : j<q.segs.length) (hm : tr.cell tt q.segs[j].1 main=1) (hsmall : j<3) :
    NearSpec.nibbles (physicalWalkBytes tr tt q.segs[j])=
      if j=0 then NearSpecV3.keyDelayedIdx else
      if j=1 then NearSpecV3.keyBufferedIdx else NearSpecV3.keyYieldIdx := by
  have hp : q.segs[j]∈q.segs := List.getElem_mem hj
  have hend := seg_le_end q.segs 0 q.consecutive _ hp
  have hfit := Nat.le_trans hend.2 q.fits
  have hs := q.valid _ hp
  have hk := WalkChain.main_kind hL q j hj hm
  have hh := walk_header hL hfit hs
  have hc : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases hc with rfl|rfl|rfl
  · simp at hk
    rw [hk.1,hk.2] at hh
    have hb : tr.cell tt q.segs[0].1 wb=((7:UInt8).toNat:Fp) := by change _=(7:Fp); grind
    rw [singleton_walk_key hL hfit hs (Or.inl hk.1) 7 hb]
    rfl
  · simp at hk
    rw [hk.1,hk.2] at hh
    have hb : tr.cell tt q.segs[1].1 wb=((13:UInt8).toNat:Fp) := by change _=(13:Fp); grind
    rw [singleton_walk_key hL hfit hs (Or.inr hk.2) 13 hb]
    rfl
  · simp at hk
    rw [hk.1,hk.2] at hh
    have hb : tr.cell tt q.segs[2].1 wb=((10:UInt8).toNat:Fp) := by change _=(10:Fp); grind
    rw [singleton_walk_key hL hfit hs (Or.inl hk.1) 10 hb]
    rfl

/-- Every post-main implicit walk reads the native delayed-index key. -/
theorem implicit_fixed_key {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
    (p : Nat × Nat) (hp : p∈q.segs) (hm : tr.cell tt p.1 main=0) :
    NearSpec.nibbles (physicalWalkBytes tr tt p)=NearSpecV3.keyDelayedIdx := by
  have hend := seg_le_end q.segs 0 q.consecutive p hp
  have hfit := Nat.le_trans hend.2 q.fits
  have hs := q.valid p hp
  have hn := hs.1
  have hr : p.1<tr.height tt := by omega
  have hw : tr.cell tt p.1 walk=1 := by
    simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 p.1 (by omega) (by omega)
  obtain ⟨hl,hh,hslot⟩ := order_implicit_shape hL hr hw hm
  have hhead := walk_header hL hfit hs
  rw [hl,hh] at hhead
  have hb : tr.cell tt p.1 wb=((7:UInt8).toNat:Fp) := by change _=(7:Fp); grind
  rw [singleton_walk_key hL hfit hs (Or.inl hl) 7 hb]
  rfl

end ZkFormal.NearV3.Qv.Extract
