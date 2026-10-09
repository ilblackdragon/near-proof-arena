import ZkFormal.NearV3.Candidates.ProcPriorForestByteIdentity
namespace ZkFormal.NearV3.Candidates.ProcPriorForestPreimage
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Byte position bounds prevent even a whole-field length wrap: if a SHA
preimage were longer than the target, its target-length position would be
an authenticated out-of-range byte. -/
theorem exact_bytes {bs:NearSpec.Bytes} {data:List Nat} (hd:data.length<P)
    (hlen:(Fp.ofNat bs.length).toNat=data.length)
    (hb:∀j,j<bs.length→(Fp.ofNat j).toNat<data.length ∧
      (Fp.ofNat (bs.getD j 0).toNat).toNat=data.getD (Fp.ofNat j).toNat 0) :
    bs.map UInt8.toNat=data := by
  have hle:bs.length≤data.length:=by
    by_cases h:bs.length≤data.length
    · exact h
    · have hx:= (hb data.length (by omega)).1
      rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hd] at hx
      omega
  have hbs:bs.length<P:=by omega
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hbs] at hlen
  apply List.ext_getElem
  · simpa using hlen
  · intro j hj hj'
    have hjbs:j<bs.length:=by simpa using hj
    have h:= (hb j hjbs).2
    have hpj:j<P:=by omega
    have hpbyte:(bs.getD j 0).toNat<P:=by
      have hh:=UInt8.toNat_lt (bs.getD j 0)
      unfold P;omega
    rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hpbyte,Fp.toNat_ofNat,Nat.mod_eq_of_lt hpj] at h
    simp only [List.getElem_map]
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hjbs,
      List.getElem?_eq_getElem hj',Option.getD_some] using h

theorem node_pre {vs:List NodeS3} {es:List ValE} (hw:NodeWf3 vs) (hv:ValWf es)
    {n:Nat} (hn:n<vs.length) {bs:NearSpec.Bytes}
    (hlen:(Fp.ofNat bs.length).toNat=(vs[n].v.ser false).length)
    (hb:∀j,j<bs.length→ProcPriorForestByteIdentity.Provider (vs:=vs) (es:=es)
      [Fp.ofNat (msgId K_NPRE n),Fp.ofNat j,Fp.ofNat (bs.getD j 0).toNat]) :
    bs.map UInt8.toNat=vs[n].v.ser false := by
  apply exact_bytes (by have:=Link3.ser_len_lt hw hn;unfold P;omega) hlen
  intro j hj
  exact ProcPriorForestByteIdentity.node_pre_byte hw hv hn (hb j hj)

theorem value_pre {vs:List NodeS3} {es:List ValE} (hw:NodeWf3 vs) (hv:ValWf es)
    {n:Nat} (hn:n<es.length) {bs:NearSpec.Bytes}
    (hlen:(Fp.ofNat bs.length).toNat=es[n].bytes.length)
    (hb:∀j,j<bs.length→ProcPriorForestByteIdentity.Provider (vs:=vs) (es:=es)
      [Fp.ofNat (msgId K_VPRE n),Fp.ofNat j,Fp.ofNat (bs.getD j 0).toNat]) :
    bs.map UInt8.toNat=es[n].bytes := by
  have hc:=hv.canon es[n] (List.getElem_mem hn)
  have hd:es[n].bytes.length<P:=by
    have hs:=hv.shape es[n] (List.getElem_mem hn)
    cases hz:es[n].vz with
    | true=>have:=hs.1 hz;simp_all
    | false=>have:=(hs.2 hz).1;omega
  apply exact_bytes hd hlen
  intro j hj
  exact ProcPriorForestByteIdentity.value_pre_byte hw hv hn (hb j hj)
end ZkFormal.NearV3.Candidates.ProcPriorForestPreimage
