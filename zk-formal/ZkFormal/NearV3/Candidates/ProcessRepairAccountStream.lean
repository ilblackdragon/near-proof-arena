import ZkFormal.NearV3.Candidates.ProcessRepairQueueComplete
import ZkFormal.NearV3.Candidates.ProcessRepairAccountView
namespace ZkFormal.NearV3.Candidates.ProcessRepairAccountStream
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
open Qv.Extract

def stream (a:AcctV):List (List Fp):=(emitAt a.k 0 a.pre).map Msg.toFp

theorem start (a:AcctV) (hn:0<a.pre.length):
    ∃m∈stream a,byteKey m=(Fp.ofNat a.k,0):=by
  refine ⟨Msg.toFp [a.k,0,a.pre.getD 0 0],?_,rfl⟩
  unfold stream
  rw [emitAt_zero,List.map_map]
  exact List.mem_map.mpr ⟨0,List.mem_range.mpr hn,rfl⟩

theorem id (a:AcctV):∀m∈stream a,(byteKey m).1=Fp.ofNat a.k:=by
  intro m hm
  unfold stream at hm
  rw [emitAt_zero,List.map_map] at hm
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hm
  rfl

theorem isolate {es:List ValE} (hv:ValWf es) (a:AcctV) (hn:0<a.pre.length)
    (others:List (List Fp)) (ho:StartClosed others)
    (hb:(stream a++others).Perm ((valRecvs es B_VBYTES).map Msg.toFp)):
    (stream a).Perm (((valRecvs es B_VBYTES).map Msg.toFp).filter
      (fun m=>decide ((byteKey m).1=Fp.ofNat a.k))):=by
  exact stream_isolate byteKey (Fp.ofNat a.k) _ _ _ hb (value_byte_keys_unique hv)
    (start a hn) (id a) ho

theorem exact_value {es:List ValE} (hv:ValWf es) (a:AcctV)
    (hn:0<a.pre.length) (hk:a.k<P) (hlen:a.pre.length<P)
    (hc:∀x∈a.pre,x<P)
    (hb:(stream a).Perm (((valRecvs es B_VBYTES).map Msg.toFp).filter
      (fun m=>decide ((byteKey m).1=Fp.ofNat a.k)))):
    ∃e∈es,e.vz=false ∧ e.vid=a.k ∧ e.bytes=a.pre:=by
  have hm:Msg.toFp [a.k,0,a.pre.getD 0 0]∈stream a:=by
    unfold stream
    rw [emitAt_zero,List.map_map]
    exact List.mem_map.mpr ⟨0,List.mem_range.mpr hn,rfl⟩
  have hmem:=(List.mem_filter.mp (hb.mem_iff.mp hm)).1
  obtain ⟨e,he,j,hj,hz,hid,_,_⟩:=value_byte_member hv hmem
  have heid:e.vid=a.k:=by
    have h0:(Fp.ofNat a.k).toNat=a.k:=by rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt hk]
    exact hid.symm.trans h0
  have hb':(stream a).Perm (valueRecordStream e):=by
    have hf:=value_stream_filter hv e he
    simpa only [byteKey,←heid,hf] using hb
  have heqlen:e.bytes.length=a.pre.length:=by
    have h:=hb'.length_eq
    simpa [stream,emitAt_zero,valueRecordStream,hz] using h.symm
  refine ⟨e,he,hz,heid,?_⟩
  apply List.ext_getElem
  · exact heqlen
  intro i hi hi'
  have hm:Msg.toFp [a.k,i,a.pre.getD i 0]∈stream a:=by
    unfold stream
    rw [emitAt_zero,List.map_map]
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi',rfl⟩
  have hmem:=hb'.mem_iff.mp hm
  simp only [valueRecordStream,hz,Bool.false_eq_true,ite_false] at hmem
  obtain ⟨j,hj,heq⟩:=List.mem_map.mp hmem
  have hj':=List.mem_range.mp hj
  simp only [Msg.toFp,List.map_cons,List.map_nil,List.cons.injEq] at heq
  have hji:j=i:=Link.ofNat_inj (by omega) (by omega) heq.2.1
  subst j
  have hb1:e.bytes.getD i 0<P:=by simpa [List.getD_eq_getElem?_getD,hi] using (hv.canon e he).2.2.2 _ (List.getElem_mem hi)
  have hb2:a.pre.getD i 0<P:=by simpa [List.getD_eq_getElem?_getD,hi'] using hc _ (List.getElem_mem hi')
  have heq:=Link.ofNat_inj hb1 hb2 heq.2.2.1
  simpa [List.getD_eq_getElem?_getD,hi,hi'] using heq
end ZkFormal.NearV3.Candidates.ProcessRepairAccountStream
