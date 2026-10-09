import ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderInactive
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSideFullKind
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash

def kindGroup : List Expr := cKind.filter (fun x=> !ProcPriorCodecActual.retiredKind.contains x)

theorem decomposition : kindGroup=
    ProcPriorCodecSideKind.booleanGroup++ProcPriorCodecSidePhase.phaseGroup++
    ProcPriorCodecSideZero.zeroTests++ProcPriorCodecSideCarry.carryGroup++
    ProcPriorCodecSideNext.nextGroup++ProcPriorCodecSideBytes.byteGroup++
    ProcPriorCodecHeaderInactive.headerGroup := by decide +kernel

theorem groups (cur nxt : Nat→Fp) (first last trans : Fp)
    (hb:∀e∈ProcPriorCodecSideKind.booleanGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0)
    (hp:∀e∈ProcPriorCodecSidePhase.phaseGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0)
    (hz:∀e∈ProcPriorCodecSideZero.zeroTests,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0)
    (hc:∀e∈ProcPriorCodecSideCarry.carryGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0)
    (hn:∀e∈ProcPriorCodecSideNext.nextGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0)
    (hbyte:∀e∈ProcPriorCodecSideBytes.byteGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0)
    (hh:∀e∈ProcPriorCodecHeaderInactive.headerGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0) :
    ∀e∈kindGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  rw [decomposition]
  simp only [List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨hb,hp⟩,hz⟩,hc⟩,hn⟩,hbyte⟩,hh⟩

open ProcPriorCodecNativeBytes

theorem hash_inside (I : Input) (R : Run) (present : Bool) (vidV base0 : Nat)
    (j : Nat) (hj:j<31) (ht:R.tau<P) (trans : Fp) :
    ∀e∈kindGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (hashRow (instanceCells I R present vidV) (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) present base0 j)[c]!)
      (fun c=>Fp.ofNat (hashRow (instanceCells I R present vidV) (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) present base0 (j+1))[c]!) 0 0 trans)=0 := by
  apply groups
  · exact ProcPriorCodecSideKind.hash_boolean_group I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 j _ _ _ _
  · exact ProcPriorCodecSidePhase.hash_phase I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 j _ _ _ _ rfl rfl
  · exact ProcPriorCodecSideZero.hash_zeros I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 j (by omega) ht _ _ _ _
  · exact ProcPriorCodecSideCarry.same_instance I R present vidV _ _
      (ProcPriorCodecSideCarry.hash_instance I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 j)
      (ProcPriorCodecSideCarry.hash_instance I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 (j+1)) 0 0 trans
  · exact ProcPriorCodecSideNext.hash_inside I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 j 0 0 trans
  · exact ProcPriorCodecSideBytes.hash_bytes I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 j (digest_bound I present j) _ _ _ _
  · exact ProcPriorCodecHeaderInactive.hash_header I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 j _ _ _ _

theorem hash_to_ash (I : Input) (R : Run) (present : Bool) (vidV base0 : Nat)
    (ht:R.tau<P) (trans : Fp) :
    ∀e∈kindGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (hashRow (instanceCells I R present vidV) (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) present base0 31)[c]!)
      (fun c=>Fp.ofNat (ashRow (instanceCells I R present vidV) I base0 0)[c]!) 0 0 trans)=0 := by
  apply groups
  · exact ProcPriorCodecSideKind.hash_boolean_group I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 31 _ _ _ _
  · exact ProcPriorCodecSidePhase.hash_phase I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 31 _ _ _ _ rfl rfl
  · exact ProcPriorCodecSideZero.hash_zeros I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 31 (by omega) ht _ _ _ _
  · exact ProcPriorCodecSideCarry.same_instance I R present vidV _ _
      (ProcPriorCodecSideCarry.hash_instance I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 31)
      (ProcPriorCodecSideCarry.ash_instance I R present vidV base0 0) 0 0 trans
  · exact ProcPriorCodecSideNext.hash_to_ash I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 0 0 trans
  · exact ProcPriorCodecSideBytes.hash_bytes I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 31 (digest_bound I present 31) _ _ _ _
  · exact ProcPriorCodecHeaderInactive.hash_header I R present vidV (ProcPriorCodecNativeBytes.digest I present) (priorHash I present) base0 31 _ _ _ _

theorem ash_inside (I : Input) (R : Run) (present : Bool) (vidV base0 : Nat)
    (j : Nat) (hj:j<31) (ht:R.tau<P) (trans : Fp) :
    ∀e∈kindGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (ashRow (instanceCells I R present vidV) I base0 j)[c]!)
      (fun c=>Fp.ofNat (ashRow (instanceCells I R present vidV) I base0 (j+1))[c]!) 0 0 trans)=0 := by
  apply groups
  · exact ProcPriorCodecSideKind.ash_boolean_group I R present vidV base0 j _ _ _ _
  · exact ProcPriorCodecSidePhase.ash_phase I R present vidV base0 j _ _ _ _ rfl rfl
  · exact ProcPriorCodecSideZero.ash_zeros I R present vidV base0 j (by omega) ht _ _ _ _
  · exact ProcPriorCodecSideCarry.same_instance I R present vidV _ _
      (ProcPriorCodecSideCarry.ash_instance I R present vidV base0 j)
      (ProcPriorCodecSideCarry.ash_instance I R present vidV base0 (j+1)) 0 0 trans
  · exact ProcPriorCodecSideNext.ash_next I R present vidV base0 j _ _ _ _ (Or.inl (by omega))
  · exact ProcPriorCodecSideBytes.ash_bytes I R present vidV base0 j _ _ _ _
  · exact ProcPriorCodecHeaderInactive.ash_header I R present vidV base0 j _ _ _ _

theorem ash_final (I : Input) (R : Run) (present : Bool) (vidV base0 : Nat)
    (ht:R.tau<P) (nxt : Nat→Fp) (hn:nxt act=0 ∨ nxt kF=1) (trans : Fp) :
    ∀e∈kindGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (ashRow (instanceCells I R present vidV) I base0 31)[c]!) nxt 0 0 trans)=0 := by
  apply groups
  · exact ProcPriorCodecSideKind.ash_boolean_group I R present vidV base0 31 _ _ _ _
  · exact ProcPriorCodecSidePhase.ash_phase I R present vidV base0 31 _ _ _ _ rfl rfl
  · exact ProcPriorCodecSideZero.ash_zeros I R present vidV base0 31 (by decide) ht _ _ _ _
  · exact ProcPriorCodecSideNext.ash_final_carry I R present vidV base0 _ _ _ _
  · exact ProcPriorCodecSideNext.ash_next I R present vidV base0 31 _ _ _ _ (Or.inr hn)
  · exact ProcPriorCodecSideBytes.ash_bytes I R present vidV base0 31 _ _ _ _
  · exact ProcPriorCodecHeaderInactive.ash_header I R present vidV base0 31 _ _ _ _

theorem ash_to_header (I : Input) (R : Run) (present : Bool) (vidV base0 : Nat)
    (I' : Input) (R' : Run) (present' : Bool) (vidV' : Nat)
    (ht:R.tau<P) (trans : Fp) :
    ∀e∈kindGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (ashRow (instanceCells I R present vidV) I base0 31)[c]!)
      (fun c=>Fp.ofNat (headerRow (instanceCells I' R' present' vidV')
        (parameters I' R') (ProcPriorCodecNativeBytes.header R') present' 0)[c]!) 0 0 trans)=0 := by
  apply ash_final I R present vidV base0 ht
  right
  rw [(ProcPriorCodecSideMultiplicity.header_flags I' R' present' vidV'
    (parameters I' R') (ProcPriorCodecNativeBytes.header R') 0).2.2.2.2.1]
  rfl

theorem ash_to_zero (I : Input) (R : Run) (present : Bool) (vidV base0 : Nat)
    (ht:R.tau<P) (trans : Fp) :
    ∀e∈kindGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (ashRow (instanceCells I R present vidV) I base0 31)[c]!)
      (fun _=>0) 0 0 trans)=0 :=
  ash_final I R present vidV base0 ht _ (Or.inl rfl) trans

end ZkFormal.NearV3.Candidates.ProcPriorCodecSideFullKind
