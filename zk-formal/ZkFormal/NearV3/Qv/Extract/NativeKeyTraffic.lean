import ZkFormal.NearV3.Qv.Extract.NativeKeySymbols

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

def nativeKeyRow (id : Fp) (bs : NearSpec.Bytes) (i : Nat) : List (List Fp) :=
  (if i=0 then [[id,0,(SYM_START:Nat),0]] else []) ++
  [[id,2*(i:Fp)+1,(((bs.getD i 0).toNat/16:Nat):Fp),0],
   [id,2*(i:Fp)+2,(((bs.getD i 0).toNat%16:Nat):Fp),0]] ++
  (if i+1=bs.length then [[id,2*(i:Fp)+3,(SYM_END:Nat),1]] else [])

def nativeKeyTraffic (id : Fp) (bs : NearSpec.Bytes) : List (List Fp) :=
  (List.range bs.length).flatMap (nativeKeyRow id bs)

/-- Each physical KEYNIB row has the native byte's two symbols, with exact
start/end markers, positions and the segment's constant walk identifier. -/
theorem native_key_row {tr : Trace Fp} {tt s n : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (hfit : s+n≤tr.height tt)
    (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s n)
    (i : Nat) (hi : i<n) :
    rowTraffic interactions tr tt (s+i) pub B_KEYNIB true=
      nativeKeyRow (wid.eval tr tt s pub) (physicalWalkBytes tr tt (s,n)) i := by
  have hw : tr.cell tt (s+i) walk=1 := by
    simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 (s+i) (by omega) (by omega)
  obtain ⟨hb,hl,hh⟩ := walk_nibbles_byte hL (by omega) hw
  have hget : (physicalWalkBytes tr tt (s,n)).getD i 0=UInt8.ofNat (cv tr tt (s+i) wb) := by
    simp [physicalWalkBytes,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem (show i<(List.range n).length by simpa using hi)]
  have hnat : ((physicalWalkBytes tr tt (s,n)).getD i 0).toNat=cv tr tt (s+i) wb := by
    rw [hget,Link.toNat_ofNat_byte hb]
  rw [key_segment_row hL hfit hs (s+i) (by omega) (by omega),hl,hh]
  have hfirst : s+i=s ↔ i=0 := by omega
  have hlast : s+i+1=s+n ↔ i+1=n := by omega
  have hlen : (physicalWalkBytes tr tt (s,n)).length=n := by
    simp [physicalWalkBytes]
  simp only [nativeKeyRow,hnat,hlen,hfirst,hlast,Nat.add_sub_cancel_left]

/-- The complete physical KEYNIB stream equals the native key traffic exactly,
including identifiers, positions, markers, order and multiplicities. -/
theorem native_key_segment {tr : Trace Fp} {tt s n : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (hfit : s+n≤tr.height tt)
    (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s n) :
    (List.range' s n).flatMap (fun r => rowTraffic interactions tr tt r pub B_KEYNIB true)=
      nativeKeyTraffic (wid.eval tr tt s pub) (physicalWalkBytes tr tt (s,n)) := by
  rw [List.range'_eq_map_range,List.flatMap_map]
  simp only [nativeKeyTraffic,physicalWalkBytes,List.length_map,List.length_range,List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i hi
  exact native_key_row hL hfit hs i (List.mem_range.mp hi)

/-- All table sends are native key messages of the extracted walks; parser and
padding rows contribute no additional messages. -/
theorem native_key_physical {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt) :
    (List.range (tr.height tt)).flatMap
      (fun r => rowTraffic interactions tr tt r pub B_KEYNIB true)=
    q.segs.flatMap (fun p => nativeKeyTraffic (wid.eval tr tt p.1 pub)
      (physicalWalkBytes tr tt p)) := by
  rw [key_physical hL q]
  simp only [List.flatMap_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro p hp
  have he := native_key_segment hL
    (Nat.le_trans (seg_le_end q.segs 0 q.consecutive p hp).2 q.fits) (q.valid p hp)
  simpa only [key_row,List.flatMap_def] using he

end ZkFormal.NearV3.Qv.Extract
