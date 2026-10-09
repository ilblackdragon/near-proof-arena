import ZkFormal.NearV3.Candidates.ProcPriorCodecSideTrailer
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSideMultiplicity
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash ProcPriorCodecSideTrailer SchedSetAll

def Bit (v : Fp) : Prop := v=0 ∨ v=1

theorem side_mult (cur nxt : Nat→Fp) (first last trans : Fp)
    (hz : ∀c∈[kR,fS,fR,fA,rend,fwg,cg,rs],cur c=0)
    (henc : Bit (cur kH+cur kZ)) (hsha : Bit (cur kZ+cur kA))
    (hA : Bit (cur kA)) (hZ : Bit (cur kZ)) (hF : Bit (cur kF)) (hD : Bit (cur dgg)) :
    ∀inter∈ProcPriorCodecActual.interactions,∀e∈inter.mult,
      Bit (e.evalWith (ProcPriorCells.env cur nxt first last trans)) := by
  have hR:=hz kR (by simp)
  have hS:=hz fS (by simp)
  have hFR:=hz fR (by simp)
  have hFA:=hz fA (by simp)
  have hEnd:=hz rend (by simp)
  have hFw:=hz fwg (by simp)
  have hCg:=hz cg (by simp)
  have hRs:=hz rs (by simp)
  simp only [ProcPriorCodecActual.interactions,ProcPriorCodecParameter.table,
    ZkFormal.NearV3.Render.UpsRelay.codecTable,Codec.table,Codec.interactions,
    List.set, List.cons_append,List.nil_append,
    List.forall_mem_cons,ProcPriorCodecActual.presence,
    ProcPriorCodecActual.grid,ProcPriorCodecActual.publicId,ProcPriorCodecActual.priorRead,
    ProcPriorCodecActual.sanity,ProcPriorCodecParameter.interaction,
    ZkFormal.NearV3.Render.UpsRelay.relay]
  simp [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    encG,hR,hS,hFR,hFA,hEnd,hFw,hCg,hRs]
  rcases henc with henc|henc <;> rcases hsha with hsha|hsha <;>
    rcases hA with hA|hA <;> rcases hZ with hZ|hZ <;>
    rcases hF with hF|hF <;> rcases hD with hD|hD <;>
    unfold Bit at * <;> grind

theorem header_flags (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) :
    let row:=headerRow (instanceCells I R present vidV) params hdr present p
    (∀c∈[kR,fS,fR,fA,rend,fwg,cg,rs],row[c]! = 0) ∧
      row[kH]! = 1 ∧ row[kZ]! = 0 ∧ row[kA]! = 0 ∧
      row[kF]! = (if p=0 then 1 else 0) ∧ row[dgg]! = 0 := by
  dsimp only
  constructor
  · intro c hc
    have hsc : c∈scalarColumns := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
    rw [header_scalar _ _ _ _ _ _ _ _ hsc]
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [instanceCells,ProcPriorCodecHeaderReads.headerScalars,lookup,
      act,tau,pres,vid,nn,NN,base,fair,itz,zt,kH,kF,pos,bpost,bpre,vbg,ihp,ehp,kR,fS,fR,fA,rend,fwg,cg,rs]
  · repeat rw [header_scalar _ _ _ _ _ _ _ _ (by decide +kernel)]
    simp [instanceCells,ProcPriorCodecHeaderReads.headerScalars,lookup,
      act,tau,pres,vid,nn,NN,base,fair,itz,zt,kH,kF,pos,bpost,bpre,vbg,ihp,ehp,kZ,kA,dgg]

theorem hash_flags (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) :
    let row:=hashRow (instanceCells I R present vidV) digest hpre present base0 j
    (∀c∈[kR,fS,fR,fA,rend,fwg,cg,rs],row[c]! = 0) ∧
      row[kH]! = 0 ∧ row[kZ]! = 1 ∧ row[kA]! = 0 ∧
      row[kF]! = 0 ∧ row[dgg]! = (if j=0 then 1 else 0) := by
  dsimp only
  constructor
  · intro c hc
    have hsc : c∈scalarColumns := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
    rw [hash_scalar _ _ _ _ _ _ _ _ _ hsc]
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [instanceCells,ProcPriorCodecHashReads.hashScalars,lookup,
      act,tau,pres,vid,nn,NN,base,fair,itz,zt,kZ,dgg,pos,sj,bpost,bpre,bsha,vbg,isj,esj,kR,fS,fR,fA,rend,fwg,cg,rs]
  · repeat rw [hash_scalar _ _ _ _ _ _ _ _ _ (by decide +kernel)]
    simp [instanceCells,ProcPriorCodecHashReads.hashScalars,lookup,
      act,tau,pres,vid,nn,NN,base,fair,itz,zt,kZ,dgg,pos,sj,bpost,bpre,bsha,vbg,isj,esj,kH,kA,kF]

theorem ash_flags (I : Input) (R : Run) (present : Bool) (vidV base0 j : Nat) :
    let row:=ashRow (instanceCells I R present vidV) I base0 j
    (∀c∈[kR,fS,fR,fA,rend,fwg,cg,rs],row[c]! = 0) ∧
      row[kH]! = 0 ∧ row[kZ]! = 0 ∧ row[kA]! = 1 ∧ row[kF]! = 0 ∧ row[dgg]! = 0 := by
  dsimp only
  constructor
  · intro c hc
    have hw : c<Codec.width := (by decide +kernel : ∀c∈[kR,fS,fR,fA,rend,fwg,cg,rs],c<Codec.width) c hc
    unfold ashRow
    rw [SchedSetAll.cell _ _ _ hw]
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [instanceCells,lookup,act,tau,pres,vid,nn,NN,base,fair,itz,zt,
      kA,pos,sj,bsha,pm0,pm1,isj,esj,kR,fS,fR,fA,rend,fwg,cg,rs]
  · unfold ashRow
    repeat rw [SchedSetAll.cell _ _ _ (by decide +kernel)]
    simp [instanceCells,lookup,act,tau,pres,vid,nn,NN,base,fair,itz,zt,
      kA,pos,sj,bsha,pm0,pm1,isj,esj,kH,kZ,kF,dgg]

theorem header_mult (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀inter∈ProcPriorCodecActual.interactions,∀e∈inter.mult,
      Bit (e.evalWith (ProcPriorCells.env
        (fun c=>Fp.ofNat ((headerRow (instanceCells I R present vidV) params hdr present p)[c]!))
        nxt first last trans)) := by
  obtain ⟨hz,hH,hZ,hA,hF,hD⟩ := header_flags I R present vidV params hdr p
  apply side_mult
  · intro c hc; rw [hz c hc]; rfl
  all_goals simp only [hH,hZ,hA,hF,hD]
  all_goals by_cases hp : p=0
  all_goals simp only [hp,ite_true,ite_false,←Fp.ofNat_def]
  all_goals unfold Bit
  all_goals grind

theorem hash_mult (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀inter∈ProcPriorCodecActual.interactions,∀e∈inter.mult,
      Bit (e.evalWith (ProcPriorCells.env
        (fun c=>Fp.ofNat ((hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]!))
        nxt first last trans)) := by
  obtain ⟨hz,hH,hZ,hA,hF,hD⟩ := hash_flags I R present vidV digest hpre base0 j
  apply side_mult
  · intro c hc; rw [hz c hc]; rfl
  all_goals simp only [hH,hZ,hA,hF,hD]
  all_goals by_cases hj : j=0
  all_goals simp only [hj,ite_true,ite_false,←Fp.ofNat_def]
  all_goals unfold Bit
  all_goals grind

theorem ash_mult (I : Input) (R : Run) (present : Bool) (vidV base0 j : Nat)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀inter∈ProcPriorCodecActual.interactions,∀e∈inter.mult,
      Bit (e.evalWith (ProcPriorCells.env
        (fun c=>Fp.ofNat ((ashRow (instanceCells I R present vidV) I base0 j)[c]!))
        nxt first last trans)) := by
  obtain ⟨hz,hH,hZ,hA,hF,hD⟩ := ash_flags I R present vidV base0 j
  apply side_mult
  · intro c hc; rw [hz c hc]; rfl
  all_goals simp only [hH,hZ,hA,hF,hD,←Fp.ofNat_def]
  all_goals unfold Bit
  all_goals grind
end ZkFormal.NearV3.Candidates.ProcPriorCodecSideMultiplicity
