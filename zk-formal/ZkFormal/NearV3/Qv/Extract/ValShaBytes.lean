import ZkFormal.NearV3.Assembly.ShaUnionBytes
import ZkFormal.NearV3.Qv.Extract.NativeRecord

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Canonical value fields are bytes because each physical BYTES send reaches
one of the locally checked SHA tables. No digest export or byte-range premise
is required for the value record. -/
theorem value_bytes_of_sha {tr : Trace Fp} {pub : List Fp} {tv : Nat}
    (ts : List Nat) (hsha : ∀ t∈ts, Sha.ShaLocal tr t pub)
    (vals : List ValE) (hv : ValWf vals)
    (ht : TableTraffic ValV3.interactions tr tv pub (valTraffic vals))
    (hbalance : ∀ m, tableBusCount ValV3.interactions tr tv pub B_BYTES true m≤
      Assembly.shaUnionCount tr pub ts false B_BYTES m) :
    ∀ e∈vals, Bytes8 e.bytes := by
  intro e he x hx
  have hcanon := (hv.canon e he).2.2.2 x hx
  have hz : e.vz=false := by
    cases h : e.vz with
    | false => rfl
    | true => have hb := (hv.shape e he).1 h; rw [hb.2] at hx; simp at hx
  obtain ⟨i,hi,hxi⟩ := List.mem_iff_getElem.mp hx
  have hget : e.bytes.getD i 0=x := by
    rw [List.getElem_eq_getD (h:=hi) 0] at hxi
    exact hxi
  have hmem : [eidV e,i,x]∈valSends vals B_BYTES := by
    simp only [valSends,ite_true,List.mem_flatMap]
    refine ⟨e,he,?_⟩
    simp only [hz,Bool.false_eq_true,ite_false,emitAt,List.mem_map]
    exact ⟨i,List.mem_range.mpr hi,by simp only [Nat.zero_add,hget]⟩
  have hpos := Link.cnt_pos_of_mem hmem
  have hle := hbalance (Msg.toFp [eidV e,i,x])
  have hvcount := (ht B_BYTES (Msg.toFp [eidV e,i,x])).1
  simp only [valTraffic] at hvcount
  rw [hvcount] at hle
  have hrecv : 0<Assembly.shaUnionCount tr pub ts false B_BYTES [Fp.ofNat (eidV e),Fp.ofNat i,Fp.ofNat x] := by
    change 0<Assembly.shaUnionCount tr pub ts false B_BYTES (Msg.toFp [eidV e,i,x])
    exact Nat.lt_of_lt_of_le hpos hle
  have hb := Assembly.shaUnion_byte_range ts hsha hrecv
  simpa only [Fp.toNat_ofNat,Nat.mod_eq_of_lt hcanon] using hb

end ZkFormal.NearV3.Qv.Extract
