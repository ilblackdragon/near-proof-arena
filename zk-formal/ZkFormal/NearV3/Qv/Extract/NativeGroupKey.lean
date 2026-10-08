import ZkFormal.NearV3.Qv.Extract.WalkGroupRequests

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

def physicalWalkBytes (tr : Trace Fp) (tt : Nat) (p : Nat × Nat) : NearSpec.Bytes :=
  (List.range p.2).map (fun i => UInt8.ofNat (cv tr tt (p.1+i) wb))

private theorem native_byte_field {x : Fp} {b : UInt8} (h : x=(b.toNat:Fp)) :
    UInt8.ofNat x.toNat=b := by
  have hb := UInt8.toNat_lt b
  have hp : 256<P := by decide
  rw [h]
  change UInt8.ofNat (Fp.ofNat b.toNat).toNat=b
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (show b.toNat<P by omega),UInt8.ofNat_toNat]

/-- The complete physical group key is the native prefix16 followed by the
same shard occurrence's little-endian u64 bytes. -/
theorem native_group_key_bytes {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
    (ss : List Nat) (htau : Fp) (hlen : ss.length<P)
    (hrequests : ∀ m∈(List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic interactions tr tt r pub B_QSH false),
      m∈Parser.nativeShardMessages htau ss)
    (j : Nat) (hj : j<q.segs.length) (hm : tr.cell tt q.segs[j].1 main=1)
    (hgroup : 3≤j) :
    physicalWalkBytes tr tt q.segs[j]=[16]++NearSpec.u64 (ss.getD (j-3) 0) := by
  have hp : q.segs[j]∈q.segs := List.getElem_mem hj
  have hend := seg_le_end q.segs 0 q.consecutive _ hp
  have hfit := Nat.le_trans hend.2 q.fits
  have hs := q.valid _ hp
  have hk := WalkChain.main_kind hL q j hj hm
  have hn0 : ¬(j=0 ∨ j=2) := by omega
  have hn2 : ¬j<2 := by omega
  simp only [hn0,hn2,ite_false] at hk
  have hn := (walk_kind_length hL hfit hs).1 hk
  have hhead := walk_header hL hfit hs
  rw [hk.1,hk.2] at hhead
  have h16 : tr.cell tt q.segs[j].1 wb=16 := by grind
  have hb : ∀ i, i<8 → UInt8.ofNat (cv tr tt (q.segs[j].1+1+i) wb)=
      (NearSpec.u64 (ss.getD (j-3) 0)).getD i 0 := by
    intro i hi
    exact native_byte_field (group_native_byte hL q ss htau hlen hrequests j hj hm hgroup i hi).2.2
  unfold physicalWalkBytes
  rw [hn]
  have hr : List.range 9=0::List.range' 1 8 := by decide
  rw [hr,List.map_cons]
  have hh : UInt8.ofNat (cv tr tt (q.segs[j].1+0) wb)=16 := by
    simp only [Nat.add_zero,cv,h16]
    decide
  rw [hh]
  simp only [List.singleton_append,List.cons.injEq,true_and]
  rw [List.range'_eq_map_range,List.map_map]
  apply List.ext_getElem
  · simp [NearSpec.u64,NearSpec.leN]
  · intro i hi hi'
    have hib : i<8 := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,Function.comp_apply]
    have hv := hb i hib
    rw [←List.getElem_eq_getD (h:=hi') 0] at hv
    simpa only [Nat.add_assoc] using hv

/-- The recovered key is exactly the native runtime group-data key. -/
theorem native_group_key {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
    (ss : List Nat) (htau : Fp) (hlen : ss.length<P)
    (hrequests : ∀ m∈(List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic interactions tr tt r pub B_QSH false),
      m∈Parser.nativeShardMessages htau ss)
    (j : Nat) (hj : j<q.segs.length) (hm : tr.cell tt q.segs[j].1 main=1)
    (hgroup : 3≤j) :
    NearSpec.nibbles (physicalWalkBytes tr tt q.segs[j])=NearSpecV3.keyGroupsData (ss.getD (j-3) 0) := by
  rw [native_group_key_bytes hL q ss htau hlen hrequests j hj hm hgroup]
  rfl

end ZkFormal.NearV3.Qv.Extract
