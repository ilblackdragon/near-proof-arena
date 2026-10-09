import ZkFormal.NearV3.Candidates.ProcCodecAppendLocal
import ZkFormal.NearV3.Assembly.SchedulerCodecNativeBlocks
namespace ZkFormal.NearV3.Candidates.ProcCodecNativeConcatLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecAppendLocal

theorem cons_rows (b : NativeBlock) (bs : List NativeBlock) :
    nativeBlockRows (b::bs)=b.output.rows++nativeBlockRows bs := by
  simp [nativeBlockRows]

theorem first_cell (b : NativeBlock) (bs : List NativeBlock) (hb:b.Valid) :
    (nativeBlockRows (b::bs))[0]! =b.output.rows[0]! := by
  rw [cons_rows]
  apply left_cell
  rw [generated_length _ _ _ _ _ _ _ hb.2.2.2.2]
  omega

theorem rows_ok (bs : List NativeBlock)
    (hb:∀b∈bs,b.Valid ∧ b.run.n≤64 ∧ b.run.tau<P ∧
      ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace b.output.rows codecPad) 0 []) :
    RowsOk (nativeBlockRows bs) := by
  induction bs with
  | nil => intro r hr; simp [nativeBlockRows] at hr
  | cons b bs ih =>
    have hB:=hb b (by simp)
    have hgen:=hB.1.2.2.2.2
    have hl:=generated_length _ _ _ _ _ _ _ hgen
    have hcap: b.output.rows.size<2^22 := (ProcCodecGeneratedBits.capacity _ _ _ _ _ _ _ hgen hB.2.1).2
    have hlocal:=ProcCodecGeneratedBoundary.active_of_local b.output.rows hcap hB.2.2.2
    cases bs with
    | nil => simpa [nativeBlockRows,RowsOk] using hlocal
    | cons d ds =>
      have hD:=hb d (by simp)
      have hlen:=generated_length _ _ _ _ _ _ _ hD.1.2.2.2.2
      have htail:0<(nativeBlockRows (d::ds)).size := by rw [cons_rows,Array.size_append];omega
      rw [cons_rows]
      apply append_rows _ _ (by omega) htail hlocal (ih (fun x hx=>hb x (by simp [hx])))
      rw [first_cell d ds hD.1]
      exact ProcCodecGeneratedBoundary.pair _ _ _ _ _ _ _ hgen _ _ _ _ _ _ _ hD.1.2.2.2.2 hB.2.2.1

theorem empty_local (t : Nat) (pub : List Fp) :
    ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace #[] codecPad) t pub := by
  have hz:∀r,ProcCodecPhysicalPadding.cells #[] r=(fun _=>0) := by
    intro r
    exact ProcCodecPhysicalPadding.padding_cells #[] r (by simp)
  have hc : ∀a b c:Bool,∀e∈ProcPriorCodecActual.constraints,
      e.evalWith (ProcPriorCells.env (fun _=>0) (fun _=>0)
        (if a then 1 else 0) (if b then 1 else 0) (if c then 1 else 0))=0 := by decide +kernel
  have hm : ∀a b c:Bool,∀i∈ProcPriorCodecActual.interactions,∀e∈i.mult,
      e.evalWith (ProcPriorCells.env (fun _=>0) (fun _=>0)
        (if a then 1 else 0) (if b then 1 else 0) (if c then 1 else 0))=0 := by decide +kernel
  refine ⟨by change 1≤22;decide,by change 22≤22;decide,?_,?_⟩
  · intro r hr e he
    have hp:e.pubBound=0 := (by decide +kernel : ∀e∈ProcPriorCodecActual.constraints,e.pubBound=0) e he
    rw [ProcCodecPhysicalPadding.physical_eval #[] t r hr pub e hp,hz,hz]
    simpa only [decide_eq_true_eq] using hc (decide (r=0)) (decide (r+1=2^22)) (decide (r+1<2^22)) e he
  · intro r hr i hi e he
    left
    have hp:e.pubBound=0 := (by decide +kernel : ∀i∈ProcPriorCodecActual.interactions,∀e∈i.mult,e.pubBound=0) i hi e he
    rw [ProcCodecPhysicalPadding.physical_eval #[] t r hr pub e hp,hz,hz]
    simpa only [decide_eq_true_eq] using hm (decide (r=0)) (decide (r+1=2^22)) (decide (r+1<2^22)) i hi e he

/-- Any prepared-size list of honest locally valid Codec blocks is locally
valid after actual concatenation. All inter-block edges and selector changes
are proved, including the empty list and final cyclic padding row. -/
theorem table (bs : List NativeBlock) (hlen:bs.length≤33)
    (hb:∀b∈bs,b.Valid ∧ b.run.n≤64 ∧ b.run.tau<P ∧
      ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace b.output.rows codecPad) 0 [])
    (t : Nat) (pub : List Fp) :
    ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace (nativeBlockRows bs) codecPad) t pub := by
  cases bs with
  | nil => exact empty_local t pub
  | cons b bs =>
    have hv:∀x∈b::bs,x.Valid ∧ x.run.n≤64 := fun x hx=>⟨(hb x hx).1,(hb x hx).2.1⟩
    have hbound:=native_block_rows_bound (b::bs) hv
    have hcap:(nativeBlockRows (b::bs)).size<2^22 := by omega
    have hlenb:=generated_length _ _ _ _ _ _ _ (hb b (by simp)).1.2.2.2.2
    have hne:0<(nativeBlockRows (b::bs)).size := by rw [cons_rows,Array.size_append];omega
    apply ProcCodecPhysicalRows.table_of_rows _ hne hcap t pub (rows_ok (b::bs) hb)
    intro r hr i hi e he
    have hm:(nativeBlockRows (b::bs))[r]!∈(nativeBlockRows (b::bs)).toList := by simp [hr]
    simp only [nativeBlockRows,List.toList_toArray,List.mem_flatMap] at hm
    obtain ⟨x,hx,hrow⟩:=hm
    exact ProcCodecGeneratedBits.generated_good _ _ _ _ _ _ _ (hb x hx).1.2.2.2.2 _ _ _ _
      (nativeBlockRows (b::bs))[r]! hrow i hi e he
/-- Ordered prepared-size instances supply their own field timestamp bounds. -/
theorem indexed_table (bs : List NativeBlock) (hlen:bs.length≤33)
    (hb:∀b∈bs,b.Valid ∧ b.run.n≤64 ∧
      ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace b.output.rows codecPad) 0 [])
    (ho:∀(i:Nat)(b:NativeBlock),bs[i]?=some b→b.run.tau=i) (t : Nat) (pub : List Fp) :
    ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace (nativeBlockRows bs) codecPad) t pub := by
  apply table bs hlen
  intro b hmem
  obtain ⟨i,hi⟩:=List.mem_iff_getElem?.mp hmem
  have hir:=(List.getElem?_eq_some_iff.mp hi).1
  have ht:b.run.tau<P := by
    rw [ho i b hi]
    have hP:33<P := by decide +kernel
    omega
  exact ⟨(hb b hmem).1,(hb b hmem).2.1,ht,(hb b hmem).2.2⟩
end ZkFormal.NearV3.Candidates.ProcCodecNativeConcatLocal
