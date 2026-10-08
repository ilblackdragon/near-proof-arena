import ZkFormal.NearV3.Qv.Extract.QueueRootRead

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable

def queueMainValues (vs : List NodeS3) (es : List ValE) (tr : Trace Fp) (tt : Nat)
    (q : WalkChain tr tt) (ss : List Nat) : MainValues :=
  ⟨queueValue vs es tr tt (q.segs.getD 0 (0,0)).1,
   queueValue vs es tr tt (q.segs.getD 1 (0,0)).1,ss,
   queueValue vs es tr tt (q.segs.getD 2 (0,0)).1⟩

theorem main_tau_zero {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (hr : r<tr.height tt) (hm : tr.cell tt r main=1) :
    cv tr tt r Candidates.ValueTable.tau=0 := by
  have ht := con hL hr (e:=.mul (c main) (c Candidates.ValueTable.tau)) (by simp [constraints])
  simp only [eval_mul,eval_c,hm] at ht
  have hz : tr.cell tt r Candidates.ValueTable.tau=0 := by grind
  simp only [cv,hz]
  decide

/-- All physically ordered main requests assemble into the native read
interface, including every occurrence of a shard in the authenticated vector. -/
theorem main_queue_reads {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
    (vs : List NodeS3) (es : List ValE) (hs : List HeadE)
    (ss : List Nat) (htau : Fp) (hlen : ss.length<P)
    (hj : 1<q.segs.length) (hc : cv tr tt (q.segs[1]'hj).1 Candidates.ValueTable.count=ss.length)
    (hrequests : ∀ m∈(List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic interactions tr tt r pub B_QSH false), m∈Parser.nativeShardMessages htau ss)
    (hread : ∀ i (hi : i<q.segs.length),
      (queueTree vs es hs (cv tr tt (q.segs[i]'hi).1 Candidates.ValueTable.tau)).find
        (NearSpec.nibbles (physicalWalkBytes tr tt (q.segs[i]'hi)))=
        some (queueValue vs es tr tt (q.segs[i]'hi).1)) :
    (queueMainValues vs es tr tt q ss).Reads
      (queueTree vs es hs 0) (queueTree vs es hs 0) (queueTree vs es hs 0) := by
  obtain ⟨hfit,hmain⟩ := native_main_read_prefix hL q ss hj hc
  have h0 : 0<q.segs.length := by omega
  have h2 : 2<q.segs.length := by omega
  have hr0 := main_fixed_root_read hL q 0 h0 ((hmain 0 h0).mpr (by omega)) (by omega) (hread 0 h0)
  have hr1 := main_fixed_root_read hL q 1 hj ((hmain 1 hj).mpr (by omega)) (by omega) (hread 1 hj)
  have hr2 := main_fixed_root_read hL q 2 h2 ((hmain 2 h2).mpr (by omega)) (by omega) (hread 2 h2)
  have he0 : q.segs.getD 0 (0,0)=q.segs[0] := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h0]
  have he1 : q.segs.getD 1 (0,0)=q.segs[1] := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]
  have he2 : q.segs.getD 2 (0,0)=q.segs[2] := by simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h2]
  simp only [MainValues.Reads,queueMainValues,he0,he1,he2]
  refine ⟨by simpa using hr0,by simpa using hr1,?_,by simpa using hr2⟩
  intro s hs'
  obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem hs'
  have hidx : k+3<q.segs.length := by omega
  have hm := (hmain (k+3) hidx).mpr (by omega)
  have hr := hread (k+3) hidx
  rw [main_tau_zero hL (q.start_lt (k+3) hidx) hm,
    native_group_key hL q ss htau hlen hrequests (k+3) hidx hm (by omega)] at hr
  have hget : ss.getD (k+3-3) 0=ss[k] := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk]
  rw [hget] at hr
  exact ⟨_,hr⟩

/-- Physical parser evidence certifies all three recovered fixed main values. -/
theorem main_queue_valid (vs : List NodeS3) {es : List ValE} (hv : ValWf es)
    (tr : Trace Fp) (tt : Nat) (q : WalkChain tr tt) (ss : List Nat)
    (he : ∀ j∈[0,2], cv tr tt (q.segs.getD j (0,0)).1 absent=0 →
      ∃ e∈es, e.vid=cv tr tt (q.segs.getD j (0,0)).1 Candidates.ValueTable.vid ∧
        EmptyQueue (some (toBytes e.bytes)))
    (hb : cv tr tt (q.segs.getD 1 (0,0)).1 absent=0 →
      ∃ e∈es, e.vid=cv tr tt (q.segs.getD 1 (0,0)).1 Candidates.ValueTable.vid ∧
        BufferedValue (some (toBytes e.bytes)) ss)
    (ha : cv tr tt (q.segs.getD 1 (0,0)).1 absent≠0 → ss=[]) :
    (queueMainValues vs es tr tt q ss).Valid := by
  exact ⟨queue_value_empty vs hv tr tt _ (he 0 (by simp)),
    queue_value_buffered vs hv tr tt _ ss hb ha,
    queue_value_empty vs hv tr tt _ (he 2 (by simp))⟩

end ZkFormal.NearV3.Qv.Extract
