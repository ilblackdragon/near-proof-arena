import ZkFormal.NearV3.Candidates.ProcCodecGeneratedBoundary
namespace ZkFormal.NearV3.Candidates.ProcCodecAppendLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def RowsOk (rows : Array (Array Nat)) : Prop :=
  ∀r,r<rows.size→∀e∈ProcPriorCodecActual.constraints,
    e.evalWith (ProcCodecPhysicalRows.rowEnvAt rows r)=0

theorem left_cell (a b : Array (Array Nat)) (i : Nat) (hi:i<a.size) :
    (a++b)[i]! =a[i]! := by
  rw [getElem!_pos _ i (by simp;omega),getElem!_pos a i hi,Array.getElem_append_left hi]

theorem right_cell (a b : Array (Array Nat)) (i : Nat) (hi:i<b.size) :
    (a++b)[a.size+i]! =b[i]! := by
  rw [getElem!_pos _ _ (by simp;omega),getElem!_pos b i hi,Array.getElem_append_right (by omega)]
  simp

/-- Append locally valid Codec blocks, checking their actual boundary pair.
Every interior row is retained; relocated first selectors are cleared. -/
theorem append_rows (a b : Array (Array Nat)) (ha:1<a.size) (hb:0<b.size)
    (hA:RowsOk a) (hB:RowsOk b)
    (hpair:∀e∈ProcPriorCodecActual.constraints,e.evalWith (ProcPriorCells.env
      (fun c:Nat=>Fp.ofNat a[a.size-1]![c]!) (fun c:Nat=>Fp.ofNat b[0]![c]!) 0 0 1)=0) :
    RowsOk (a++b) := by
  intro r hr e he
  have hsize:(a++b).size=a.size+b.size := Array.size_append
  by_cases hlt:r+1<a.size
  · have hn:r+1<(a++b).size := by omega
    unfold ProcCodecPhysicalRows.rowEnvAt
    rw [ite_eq_left hn,left_cell a b r (by omega),left_cell a b (r+1) hlt]
    have hh:=hA r (by omega) e he
    simpa only [ProcCodecPhysicalRows.rowEnvAt,ite_eq_left hlt] using hh
  · by_cases hlast:r=a.size-1
    · subst r
      have hn:a.size-1+1<(a++b).size := by omega
      have hnext:a.size-1+1=a.size+0 := by omega
      unfold ProcCodecPhysicalRows.rowEnvAt
      rw [ite_eq_left hn,left_cell a b (a.size-1) (by omega),hnext,right_cell a b 0 hb,
        ite_eq_right (by omega : a.size-1≠0)]
      exact hpair e he
    · have hra:a.size≤r := by omega
      let j:=r-a.size
      have hj:j<b.size := by dsimp [j];omega
      have heq:r=a.size+j := by dsimp [j];omega
      have hn:(r+1<(a++b).size) ↔ j+1<b.size := by omega
      have hnxt : (if r+1<(a++b).size then fun c:Nat=>Fp.ofNat (a++b)[r+1]![c]! else fun _=>0)=
          (if j+1<b.size then fun c:Nat=>Fp.ofNat b[j+1]![c]! else fun _=>0) := by
        by_cases hh:j+1<b.size
        · rw [ite_eq_left hh,ite_eq_left (hn.mpr hh),show r+1=a.size+(j+1) by omega,right_cell a b (j+1) hh]
        · rw [ite_eq_right hh,ite_eq_right (fun h=>hh (hn.mp h))]
      unfold ProcCodecPhysicalRows.rowEnvAt
      rw [hnxt,heq,right_cell a b j hj,ite_eq_right (by omega : a.size+j≠0)]
      exact ProcCodecBoundaryLocal.erase_first _ _ (if j=0 then 1 else 0) 0 1 (hB j hj) e he
/-- Two honest generated Codec blocks concatenate into one physical local
trace. Boundary equations and the changed first selector are derived here. -/
theorem generated_pair (I : Input) (R : Run) (present : Bool) (vid : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h:ProcPriorCodecGen.codecRows I R present vid gb fwd=.ok out) (hn:R.n≤64)
    (I' : Input) (R' : Run) (present' : Bool) (vid' : Nat)
    (gb' : Array Nat) (fwd' : List (Nat×Nat)) (out' : CodecOut)
    (h':ProcPriorCodecGen.codecRows I' R' present' vid' gb' fwd'=.ok out') (hn':R'.n≤64)
    (ht:R.tau<P)
    (hlocal:ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace out.rows codecPad) 0 [])
    (hlocal':ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace out'.rows codecPad) 0 [])
    (t : Nat) (pub : List Fp) :
    ZkFormal.Near.TableLocal ProcPriorCodecActual.table (SchedHeight.trace (out.rows++out'.rows) codecPad) t pub := by
  have hl:=ZkFormal.NearV3.Assembly.CodecDigest.generated_length I R present vid gb fwd out h
  have hl':=ZkFormal.NearV3.Assembly.CodecDigest.generated_length I' R' present' vid' gb' fwd' out' h'
  have hne:1<out.rows.size := by omega
  have hne':0<out'.rows.size := by omega
  have hm:=Nat.mul_le_mul hn hn
  have hm':=Nat.mul_le_mul hn' hn'
  have hcap:(out.rows++out'.rows).size<2^22 := by simp only [Array.size_append];omega
  have hA:=ProcCodecGeneratedBoundary.active_of_local out.rows (by omega) hlocal
  have hB:=ProcCodecGeneratedBoundary.active_of_local out'.rows (by omega) hlocal'
  apply ProcCodecPhysicalRows.table_of_rows _ (by simp;omega) hcap t pub
  · exact append_rows out.rows out'.rows hne hne' hA hB
      (ProcCodecGeneratedBoundary.pair I R present vid gb fwd out h I' R' present' vid' gb' fwd' out' h' ht)
  · intro r hr i hi e he
    unfold ProcCodecPhysicalRows.rowEnvAt
    by_cases ha:r<out.rows.size
    · rw [left_cell out.rows out'.rows r ha]
      exact ProcCodecGeneratedBits.generated_good I R present vid gb fwd out h _ _ _ _
        out.rows[r]! (by simp [ha]) i hi e he
    · have hj:r-out.rows.size<out'.rows.size := by simp only [Array.size_append] at hr;omega
      have hr':r=out.rows.size+(r-out.rows.size) := by omega
      have hc:(out.rows++out'.rows)[r]! =out'.rows[r-out.rows.size]! := by
        rw [hr']
        simpa using right_cell out.rows out'.rows (r-out.rows.size) hj
      rw [hc]
      exact ProcCodecGeneratedBits.generated_good I' R' present' vid' gb' fwd' out' h' _ _ _ _
        out'.rows[r-out.rows.size]! (by simp [hj]) i hi e he
end ZkFormal.NearV3.Candidates.ProcCodecAppendLocal
