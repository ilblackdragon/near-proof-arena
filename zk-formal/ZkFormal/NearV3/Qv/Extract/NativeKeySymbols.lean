import ZkFormal.NearV3.Qv.Extract.WalkNibbleBytes

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.CombinedTable

private theorem nibbles_flatMap (bs : NearSpec.Bytes) :
    NearSpec.nibbles bs=bs.flatMap (fun b => [b.toNat/16,b.toNat%16]) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [NearSpec.nibbles,ih]

/-- All physical walk nibble expressions encode exactly the recovered native
key, in high-then-low byte order and with repeated nibbles preserved. -/
theorem walk_native_key_symbols {tr : Trace Fp} {tt s n : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (hfit : s+n≤tr.height tt)
    (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s n) :
    (List.range n).flatMap (fun i =>
      [((nibble 4).eval tr tt (s+i) pub).toNat,((nibble 0).eval tr tt (s+i) pub).toNat])=
    NearSpec.nibbles (physicalWalkBytes tr tt (s,n)) := by
  rw [nibbles_flatMap]
  simp only [physicalWalkBytes,List.flatMap_def,List.map_map,Function.comp_def]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro i hi
  have hn := List.mem_range.mp hi
  have hw : tr.cell tt (s+i) walk=1 := by
    simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 (s+i) (by omega) (by omega)
  obtain ⟨hb,hl,hh⟩ := walk_nibbles_byte hL (by omega) hw
  rw [hl,hh]
  have hp : 256<P := by decide
  have hlow : cv tr tt (s+i) wb%16<P := by omega
  have hhigh : cv tr tt (s+i) wb/16<P := by omega
  change [(Fp.ofNat (cv tr tt (s+i) wb/16)).toNat,(Fp.ofNat (cv tr tt (s+i) wb%16)).toNat]=_
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt hhigh,Nat.mod_eq_of_lt hlow]
  rw [Link.toNat_ofNat_byte hb]

end ZkFormal.NearV3.Qv.Extract
