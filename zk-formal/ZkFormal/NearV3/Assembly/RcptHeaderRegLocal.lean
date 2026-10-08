import ZkFormal.NearV3.Assembly.RcptHeaderStreams

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- Put the header pair away from the global first row; initialization is
separately proved on the actual planned trace. -/
def headerRegPair (own : Nat) (before : ListPlan→Nat) (fallback : ListPlan→Coord→Nat→Fp)
    (plan : ListPlan) (i : Nat) : Trace Fp :=
  ⟨fun _=>2,fun _ pos col=>headerCell (headerStreamAux own before fallback) plan
    (if pos=1 then ⟨sCL,i,12⟩ else ⟨sCL,i+1,12⟩) col⟩

theorem header_state_zero (aux : ListPlan→Coord→Nat→Fp) (plan : ListPlan)
    (i : Nat) (s : Nat) (hs : s∈states) (hne : s≠sCL) :
    headerCell aux plan ⟨sCL,i,12⟩ s=0 := by
  have hlim := states_limits hs
  rw [header_control_cell aux plan _ (by simp [controlColumn];omega),control_state _ hs]
  simp [hne]

theorem cRegs_groups : cRegs=loadConstraints++[byteHeadConstraint]++shiftConstraints++
    initialTokenConstraints++gasTokenConstraints++carryTokenConstraints := by
  simp only [cRegs,loadConstraints,byteHeadConstraint,shiftConstraints,initialTokenConstraints,
    gasTokenConstraints,carryTokenConstraints,List.append_assoc,List.cons_append,List.nil_append]

/-- All 200 cRegs equations on consecutive header rows, including byte loading,
register shifts, and native token carry. Global-first initialization is separate. -/
theorem header_cRegs (own : Nat) (before : ListPlan→Nat) (fallback : ListPlan→Coord→Nat→Fp)
    (plan : ListPlan) (i : Nat) (pub : List Fp)
    (hown : ∀j,j<8→(headerStream own plan).getD j 0=pub.getD (PH_OWN+j) 0) :
    ∀e∈cRegs,e.eval (headerRegPair own before fallback plan i) 0 1 pub=0 := by
  intro e he
  rw [cRegs_groups] at he
  simp only [List.mem_append,or_assoc] at he
  rcases he with he|he|he|he|he|he

  · obtain ⟨⟨s,es⟩,hs,he⟩ := List.mem_flatMap.mp he
    obtain ⟨⟨ee,j⟩,hentry,rfl⟩ := List.mem_map.mp he
    have hstates := loads_states (s,es) hs
    have hjmem := hentry
    by_cases hcl : s=sCL
    · subst s
      have hfirst : es=pubs PH_OWN 8 := by
        simp only [loads,List.mem_cons,List.not_mem_nil,or_false] at hs
        rcases hs with hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs <;> cases hs <;> rfl
      subst es
      by_cases hi : i=0
      · subst i
        simp [pubs] at hjmem
        obtain ⟨k,hk,hkeq⟩ := List.mem_iff_getElem.mp hjmem
        have hkb : k<8 := by simpa using hk
        have hkeq' : (Expr.pub (PH_OWN+k),k)=(ee,j) := by simpa [List.getElem_zip,List.getElem_map,List.getElem_range,hkb] using hkeq
        cases hkeq'
        simp only [eval_mul3,eval_c,eval_sub,eval_pub]
        change _*_* (headerCell _ plan ⟨sCL,0,12⟩ (reg j)-_)=0
        rw [header_stream_reg _ _ _ _ _ _ (by omega)]
        simp only [Nat.zero_add]
        rw [hown _ hkb]
        grind only
      · simp only [eval_mul3,eval_c,eval_sub]
        change _*headerCell (headerStreamAux own before fallback) plan ⟨sCL,i,12⟩ fs*_=0
        have hz : headerCell (headerStreamAux own before fallback) plan ⟨sCL,i,12⟩ fs=0 := by
          change (if i=0 then (1:Fp) else 0)=0
          simp [hi]
        rw [hz]
        grind only
    · simp only [eval_mul3,eval_c,eval_sub]
      change headerCell _ plan ⟨sCL,i,12⟩ s*_*_=0
      rw [header_state_zero _ _ _ _ hstates hcl]
      grind only
  · have he' : e=byteHeadConstraint := by simpa only [List.mem_singleton] using he
    subst e
    simp only [byteHeadConstraint,eval_mul,eval_sub,eval_c]
    change _*(headerCell _ plan ⟨sCL,i,12⟩ b-headerCell _ plan ⟨sCL,i,12⟩ (reg 0))=0
    rw [header_stream_byte,header_stream_reg _ _ _ _ _ 0 (by decide)]
    simp only [Nat.add_zero]
    grind only
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
    have hj' := List.mem_range.mp hj
    simp only [eval_mul3,eval_not,eval_sub,eval_c,eval_n]
    change _*_*(headerCell _ plan ⟨sCL,i+1,12⟩ (reg j)-headerCell _ plan ⟨sCL,i,12⟩ (reg (j+1)))=0
    rw [header_stream_reg _ _ _ _ _ _ (by omega),header_stream_reg _ _ _ _ _ _ (by omega)]
    have hx : i+1+j=i+(j+1) := by omega
    rw [hx]
    grind only
  · obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
    simp only [eval_mul]
    change (0:Fp)*_=0
    grind only
  · simp only [gasTokenConstraints,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with he|rfl
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
      simp only [eval_mul,eval_sub,eval_c,eval_n]
      change headerCell (headerStreamAux own before fallback) plan ⟨sCL,i,12⟩ sGP*_=0
      rw [header_state_zero _ _ _ _ (by decide) (by decide)]
      grind only
    · simp only [eval_mul,eval_sub,eval_c,eval_n]
      change headerCell (headerStreamAux own before fallback) plan ⟨sCL,i,12⟩ sGP*_=0
      rw [header_state_zero _ _ _ _ (by decide) (by decide)]
      grind only
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
    have hj' := List.mem_range.mp hj
    simp only [eval_mul,eval_sub,eval_c,eval_n]
    change _*(headerCell _ plan ⟨sCL,i+1,12⟩ (tok j)-headerCell _ plan ⟨sCL,i,12⟩ (tok j))=0
    rw [header_stream_token _ _ _ _ _ _ hj',header_stream_token _ _ _ _ _ _ hj']
    grind only

theorem headerStream_own (own : Nat) (plan : ListPlan) (j : Nat) (hj : j<8) :
    (headerStream own plan).getD j 0=Fp.ofNat (((u64 own).getD j 0).toNat) := by
  have hu : (u64 own).length=8 := by simp [u64,leN]
  simp only [headerStream,List.getD_eq_getElem?_getD,List.getElem?_map]
  rw [List.getElem?_append_left (by omega)]
  cases he : (u64 own)[j]? <;> rfl

theorem header_cRegs_public (own : Nat) (before : ListPlan→Nat) (fallback : ListPlan→Coord→Nat→Fp)
    (plan : ListPlan) (i : Nat) (pub : List Fp)
    (hown : ∀j,j<8→pub.getD (PH_OWN+j) 0=Fp.ofNat (((u64 own).getD j 0).toNat)) :
    ∀e∈cRegs,e.eval (headerRegPair own before fallback plan i) 0 1 pub=0 := by
  apply header_cRegs own before fallback plan i pub
  intro j hj
  exact (headerStream_own own plan j hj).trans (hown j hj).symm

end ZkFormal.NearV3.Assembly.RcptSkeleton
