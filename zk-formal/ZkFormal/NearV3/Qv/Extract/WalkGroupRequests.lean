import ZkFormal.NearV3.Qv.Extract.PhysicalBufferedRead
import ZkFormal.NearV3.Qv.Extract.WalkMain

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable
open Candidates.ValueTable (tau)

/-- Main walk ordinal j≥3 requests the eight bytes of shard occurrence j−3. -/
theorem group_request_mem {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
    (j : Nat) (hj : j<q.segs.length) (hm : tr.cell tt q.segs[j].1 main=1)
    (hgroup : 3≤j) (i : Nat) (hi : i<8) :
    [tr.cell tt q.segs[j].1 tau,((j-3:Nat):Fp),(i:Fp),tr.cell tt (q.segs[j].1+1+i) wb]∈
      (List.range (segEnd 0 q.segs)).flatMap (fun r => rowTraffic interactions tr tt r pub B_QSH false) := by
  have hp : q.segs[j]∈q.segs := List.getElem_mem hj
  have hend := seg_le_end q.segs 0 q.consecutive _ hp
  have hfit : q.segs[j].1+q.segs[j].2≤tr.height tt := Nat.le_trans hend.2 q.fits
  have hs := q.valid _ hp
  have hk := WalkChain.main_kind hL q j hj hm
  have hn0 : ¬(j=0 ∨ j=2) := by omega
  have hn2 : ¬j<2 := by omega
  simp only [hn0,hn2,ite_false] at hk
  have hn := (walk_kind_length hL hfit hs).1 hk
  let r := q.segs[j].1+1+i
  have hr : q.segs[j].1≤r := by dsimp [r]; omega
  have hb : r<q.segs[j].1+q.segs[j].2 := by dsimp [r]; omega
  have hrow : r<tr.height tt := by omega
  have hw : tr.cell tt r walk=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 r hr hb
  have hf := zero_of_false hL hrow (x:=wf) (by simp [walkBools])
    (hs.2.2.2.2.1 r (by dsimp [r]; omega) hb)
  have hl := walk_metadata hL hfit hs (x:=lo) (by simp) r hr hb
  have hh := walk_metadata hL hfit hs (x:=Candidates.CombinedTable.hi) (by simp) r hr hb
  have hg := con hL hrow (e:=sub (c groupByte) (mul3 (c walk) group (Dsl.not (c wf))))
    (by simp [constraints])
  simp only [eval_sub,eval_c,eval_mul3,group,eval_mul,eval_not,hw,hf,hl,hh,hk.1,hk.2] at hg
  have hgate : tr.cell tt r groupByte=1 := by grind
  have htau := walk_metadata hL hfit hs (x:=tau) (by simp) r hr hb
  have hslot := walk_metadata hL hfit hs (x:=slot) (by simp) r hr hb
  rw [WalkChain.main_slot hL q j hj hm] at hslot
  have hj3 : j=(j-3)+3 := by omega
  have h3 : ((3:Nat):Fp)=3 := by decide
  have hentry : tr.cell tt r slot-3=((j-3:Nat):Fp) := by
    rw [hslot]
    have hc := congrArg (fun n : Nat => (n:Fp)) hj3
    simp only [natCast_add,h3] at hc
    grind
  have hpos := walk_position hL hfit hs r hr hb
  have hri : r-q.segs[j].1=i+1 := by dsimp [r]; omega
  rw [hri,natCast_add,Lean.Grind.Semiring.natCast_one] at hpos
  have hbyte : tr.cell tt r wp-1=(i:Fp) := by grind
  have hpre : r<segEnd 0 q.segs := by omega
  have hreq := shard_byte_request_mem tr tt r (segEnd 0 q.segs) pub hpre hgate
  simpa only [htau,hentry,hbyte] using hreq

/-- The physical group-key byte is the exact byte of the requested native shard
occurrence. The entry bound comes from the actual walk index. -/
theorem group_native_byte {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal table tr tt pub) (q : WalkChain tr tt)
    (ss : List Nat) (htau : Fp) (hlen : ss.length<P)
    (hrequests : ∀ m∈(List.range (segEnd 0 q.segs)).flatMap
      (fun r => rowTraffic interactions tr tt r pub B_QSH false),
      m∈Parser.nativeShardMessages htau ss)
    (j : Nat) (hj : j<q.segs.length) (hm : tr.cell tt q.segs[j].1 main=1)
    (hgroup : 3≤j) (i : Nat) (hi : i<8) :
    tr.cell tt q.segs[j].1 tau=htau ∧ j-3<ss.length ∧
      tr.cell tt (q.segs[j].1+1+i) wb=
        (((NearSpec.u64 (ss.getD (j-3) 0)).getD i 0).toNat:Fp) := by
  have hidx := WalkChain.index_lt_modulus hL q j hj
  have hreq := group_request_mem hL q j hj hm hgroup i hi
  exact Parser.native_shard_byte_index hlen (by omega) hi (hrequests _ hreq)

end ZkFormal.NearV3.Qv.Extract
