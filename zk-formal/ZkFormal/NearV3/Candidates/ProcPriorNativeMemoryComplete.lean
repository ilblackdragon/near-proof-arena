import ZkFormal.NearV3.Candidates.ProcPriorNativeMemoryLocal
import ZkFormal.NearV3.Candidates.ProcPriorNativeMemoryBalance
namespace ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Assembly.CodecDigest

theorem ordered_distinct (bs : List NativeBlock)
    (ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i) :
    bs.Pairwise (fun a b=>a.run.tau≠b.run.tau) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hti:=ho i bs[i] (List.getElem?_eq_getElem hi)
  have htj:=ho j bs[j] (List.getElem?_eq_getElem hj)
  omega

theorem native_query (bs : List NativeBlock) (a : Tagged) (ha:a∈allRows bs)
    (hq:a.row.event.query=true) : a.row.before=ProcPriorValues.value a.row.event := by
  obtain ⟨b,_,hab⟩:=List.mem_flatMap.mp ha
  exact ProcPriorRows.query_row b.pub.ids b.old.links a.row (tagged_member b a hab).2 hq

theorem native_address (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (hlen:bs.length≤32) (ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i)
    (a : Tagged) (ha:a∈allRows bs) : address a<P := by
  obtain ⟨b,hb,hab⟩:=List.mem_flatMap.mp ha
  obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hb
  have hir: i<bs.length :=(List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨ht,hr⟩:=tagged_member b a hab
  have hlink:=ProcPriorIndexed.row_bound _ _ (hn b hb) a.row hr
  have hτ:=ho i b hi
  have hp:P>131072:=by decide +kernel
  unfold address
  omega

/-- Actual sorted native rows remain locally legal when concatenated in
prepared timestamp order. Packed-address boundaries reset incoming memory;
no adjacent-row or read-value equations are supplied as hypotheses. -/
theorem native_local (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (hlen:bs.length≤32) (ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i)
    (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184)
    (tt wb rb cb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorMemoryTable.table wb rb cb) (trace (allRows bs)) tt pub := by
  have hc:=capacity bs hn hlen hraw
  have hchain:=all_chain bs hn (ordered_distinct bs ho)
  refine ⟨by change 1≤22;decide,by change 22≤22;decide,?_,?_⟩
  · intro j hj e he
    exact constraints (allRows bs) hc hchain (all_first bs) (native_query bs)
      (native_address bs hn hlen ho) tt j hj pub e he
  · intro j hj i hi e he
    exact bits (allRows bs) hc tt j hj pub wb rb cb i hi e he

theorem native_gated_local (bs : List NativeBlock) (hn:∀b∈bs,b.pub.ids.length≤64)
    (hlen:bs.length≤32) (ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i)
    (hraw:(ProcRawConcatGeometry.rows bs).length≤2001184)
    (tt wb rb cb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorMemoryGated.table wb rb cb)
      (ProcPriorMemoryGated.liftTrace (trace (allRows bs)) tt pub) tt pub := by
  exact ProcPriorMemoryGated.lift_local wb rb cb _ tt pub
    (native_local bs hn hlen ho hraw tt wb rb cb pub)
end ZkFormal.NearV3.Candidates.ProcPriorNativeMemory
