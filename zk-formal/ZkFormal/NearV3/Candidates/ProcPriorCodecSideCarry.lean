import ZkFormal.NearV3.Candidates.ProcPriorCodecSideBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSideCarry
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash SchedSetAll

def instanceColumns : List Nat := [tau,pres,vid,nn,NN,base,fair]
def instanceValue (I : Input) (R : Run) (present : Bool) (vidV c : Nat) : Nat :=
  lookup (instanceCells I R present vidV) c 0

def Instance (I : Input) (R : Run) (present : Bool) (vidV : Nat) (row : Array Nat) : Prop :=
  ∀c∈instanceColumns,row[c]! = instanceValue I R present vidV c

theorem header_instance (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) : Instance I R present vidV (headerRow (instanceCells I R present vidV) params hdr present p) := by
  intro c hc
  have hh:c∈ProcPriorCodecRegisterMiss.untouched := by
    simp only [instanceColumns,List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rw [ProcPriorCodecHeaderReads.projection _ _ _ _ p c hh,append]
  unfold instanceValue
  simp only [instanceColumns,List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [ProcPriorCodecHeaderReads.headerScalars,lookup,tau,pres,vid,nn,NN,base,fair,kH,kF,pos,bpost,bpre,vbg,ihp,ehp]

theorem hash_instance (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) : Instance I R present vidV (hashRow (instanceCells I R present vidV) digest hpre present base0 j) := by
  intro c hc
  have hh:c∈ProcPriorCodecRegisterMiss.untouched := by
    simp only [instanceColumns,List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rw [ProcPriorCodecHashReads.projection _ _ _ _ base0 j c hh,append]
  unfold instanceValue
  simp only [instanceColumns,List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [ProcPriorCodecHashReads.hashScalars,lookup,tau,pres,vid,nn,NN,base,fair,pos,bpost,bpre,vbg,kZ,dgg,sj,bsha,isj,esj]

theorem ash_instance (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (base0 j : Nat) : Instance I R present vidV (ashRow (instanceCells I R present vidV) I base0 j) := by
  intro c hc
  have hw:c<Codec.width := (by decide +kernel : ∀c∈instanceColumns,c<Codec.width) c hc
  unfold ashRow
  rw [SchedSetAll.cell _ _ _ hw,append]
  unfold instanceValue
  simp only [instanceColumns,List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [lookup,tau,pres,vid,nn,NN,base,fair,kA,pos,sj,bsha,pm0,pm1,isj,esj]

open ZkFormal.Chacha.Table.E in
def carryGroup : List Expr := instanceColumns.map (fun c0=> .mul gT (sub (n c0) (c c0)))

theorem carry_group_eq : carryGroup=(cKind.drop 70).take 7 := by decide +kernel

theorem carry_group_retained :
    carryGroup.filter (fun x=> !ProcPriorCodecActual.retiredKind.contains x)=carryGroup := by decide +kernel

theorem carry (cur nxt : Nat→Fp) (first last trans : Fp)
    (hc:∀c∈instanceColumns,nxt c=cur c) :
    ∀e∈carryGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  intro e he
  obtain ⟨c,hm,rfl⟩ := List.mem_map.mp he
  change gT.evalWith _*(nxt c+ -cur c)=0
  rw [hc c hm]
  grind only

theorem same_instance (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (row next : Array Nat) (hc:Instance I R present vidV row) (hn:Instance I R present vidV next)
    (first last trans : Fp) :
    ∀e∈carryGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat row[c]!) (fun c=>Fp.ofNat next[c]!) first last trans)=0 := by
  apply carry
  intro c hm
  rw [hc c hm,hn c hm]

end ZkFormal.NearV3.Candidates.ProcPriorCodecSideCarry
