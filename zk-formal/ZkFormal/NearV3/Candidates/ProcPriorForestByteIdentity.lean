import ZkFormal.NearV3.Candidates.ProcPriorRoutedForestStructure
import ZkFormal.NearV3.Link.Sha3
namespace ZkFormal.NearV3.Candidates.ProcPriorForestByteIdentity
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

/-- Only the actual extracted Node and Value inventories, with their physical
IDs; this predicate does not classify unrelated BYTES suppliers. -/
def Provider {vs:List NodeS3} {es:List ValE} (msg:List Fp):Prop:=
  msg∈((nodeSends3 vs B_BYTES++valSends es B_BYTES).map Msg.toFp)

theorem node_id {vs:List NodeS3} (hw:NodeWf3 vs) {n:Nat} (hn:n<vs.length)
    {k:Nat} (hk:k<16) :
    (Fp.ofNat (msgId k n)).toNat=msgId k n ∧
      (Fp.ofNat (msgId k n)).toNat%16=k := by
  have h:=Link3.nid_lt hw hn k hk
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt h]
  constructor
  · rfl
  · simp [msgId,Nat.add_mod,Nat.mod_eq_of_lt hk]

theorem value_id {es:List ValE} (hw:ValWf es) {n:Nat} (hn:n<es.length) :
    es[n].vid=n ∧ (Fp.ofNat (msgId K_VPRE n)).toNat=msgId K_VPRE n ∧
      (Fp.ofNat (msgId K_VPRE n)).toNat%16=K_VPRE := by
  have hc:=ProcPriorRoutedValueBytes.value_count hw
  have hid:msgId K_VPRE n<P:=by unfold msgId K_VPRE;unfold P;omega
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hid]
  exact ⟨Link3.vid_small hw hn,rfl,by simp [msgId,K_VPRE,Nat.add_mod]⟩

theorem node_pre_byte {vs:List NodeS3} {es:List ValE}
    (hw:NodeWf3 vs) (hv:ValWf es) {n:Nat} (hn:n<vs.length) {pos byte:Fp}
    (hm:Provider (vs:=vs) (es:=es) [Fp.ofNat (msgId K_NPRE n),pos,byte]) :
    pos.toNat<(vs[n].v.ser false).length ∧
      byte.toNat=(vs[n].v.ser false).getD pos.toNat 0 := by
  obtain ⟨m,hm,he⟩:=List.mem_map.mp hm
  cases m with
  | nil=>simp [Msg.toFp] at he
  | cons a tail=>
    have ha:Fp.ofNat a=Fp.ofNat (msgId K_NPRE n):=by
      have h:=congrArg (fun xs:List Fp=>xs[0]!) he
      exact h
    have hm':(a::tail)∈nodeSends3 vs B_BYTES++valSends es B_BYTES++[]:=by simpa using hm
    obtain ⟨j,hj,hmsg⟩:=Link3.npre_sends hw hv (others:=[])
      (by intro m hm;cases hm) hn _ hm' a rfl ha
    rw [hmsg] at he
    have ep:=congrArg (fun xs:List Fp=>xs[1]!.toNat) he
    have eb:=congrArg (fun xs:List Fp=>xs[2]!.toNat) he
    have hjP:j<P:=by have:=Link3.ser_len_lt hw hn;unfold P;omega
    have hbyte:(vs[n].v.ser false).getD j 0<P:=by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]
      exact Link3.ser_lt_P hw hn _ (List.getElem_mem hj)
    change (Fp.ofNat j).toNat=pos.toNat at ep
    change (Fp.ofNat ((vs[n].v.ser false).getD j 0)).toNat=byte.toNat at eb
    rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hjP] at ep
    rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hbyte] at eb
    exact ⟨by omega,by rw [←ep];exact eb.symm⟩

theorem value_pre_byte {vs:List NodeS3} {es:List ValE}
    (hw:NodeWf3 vs) (hv:ValWf es) {n:Nat} (hn:n<es.length) {pos byte:Fp}
    (hm:Provider (vs:=vs) (es:=es) [Fp.ofNat (msgId K_VPRE n),pos,byte]) :
    pos.toNat<es[n].bytes.length ∧ byte.toNat=es[n].bytes.getD pos.toNat 0 := by
  obtain ⟨m,hm,he⟩:=List.mem_map.mp hm
  cases m with
  | nil=>simp [Msg.toFp] at he
  | cons a tail=>
    have ha:Fp.ofNat a=Fp.ofNat (msgId K_VPRE n):=by
      have h:=congrArg (fun xs:List Fp=>xs[0]!) he
      exact h
    have hm':(a::tail)∈nodeSends3 vs B_BYTES++valSends es B_BYTES++[]:=by simpa using hm
    obtain ⟨j,hj,hmsg⟩:=Link3.vpre_sends hw hv (others:=[])
      (by intro m hm;cases hm) hn _ hm' a rfl ha
    rw [hmsg] at he
    have ep:=congrArg (fun xs:List Fp=>xs[1]!.toNat) he
    have eb:=congrArg (fun xs:List Fp=>xs[2]!.toNat) he
    have hcanon:=hv.canon es[n] (List.getElem_mem hn)
    have hlen:es[n].bytes.length<P:=by
      have hs:=hv.shape es[n] (List.getElem_mem hn)
      cases hz:es[n].vz with
      | true=>have:=hs.1 hz;simp_all
      | false=>have:=(hs.2 hz).1;omega
    have hbyte:es[n].bytes.getD j 0<P:=by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some]
      exact hcanon.2.2.2 _ (List.getElem_mem hj)
    change (Fp.ofNat j).toNat=pos.toNat at ep
    change (Fp.ofNat (es[n].bytes.getD j 0)).toNat=byte.toNat at eb
    rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (show j<P by omega)] at ep
    rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hbyte] at eb
    exact ⟨by omega,by rw [←ep];exact eb.symm⟩
end ZkFormal.NearV3.Candidates.ProcPriorForestByteIdentity
