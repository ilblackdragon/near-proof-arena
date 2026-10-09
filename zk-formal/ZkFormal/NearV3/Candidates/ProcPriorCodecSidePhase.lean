import ZkFormal.NearV3.Candidates.ProcPriorCodecSideZero
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSidePhase
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash
open ZkFormal.Chacha.Table.E in
def phaseGroup : List Expr :=
  [sub (c act) (.add (c kH) (.add (c kR) (.add (c kZ) (c kA)))),
   sub (c kR) (.add (c fS) (.add (c fR) (c fA))),
   .mul (c kF) (notE (c kH)), .mul .isLast (c act),
   mul3 .isTransition (notE (c act)) (n act),
   .mul .isFirst (.mul (c act) (notE (c kF)))]

theorem phase_group_eq : phaseGroup=(cKind.drop 46).take 6 := by decide +kernel

theorem phase_group_retained :
    phaseGroup.filter (fun x=> !ProcPriorCodecActual.retiredKind.contains x)=phaseGroup := by decide +kernel

theorem side_phase (cur nxt : Nat→Fp) (first last trans : Fp)
    (ha:cur act=1) (hz:∀c∈[kR,fS,fR,fA],cur c=0)
    (hpart:cur kH+(cur kZ+cur kA)=1) (hk:cur kF*(1-cur kH)=0)
    (hl:last=0) (hf:first*(1-cur kF)=0) :
    ∀e∈phaseGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  have hR:=hz kR (by simp)
  have hS:=hz fS (by simp)
  have hFR:=hz fR (by simp)
  have hA:=hz fA (by simp)
  intro e he
  simp only [phaseGroup,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,notE,mul3,
    Bool.false_eq_true,ite_false,ite_true,ha,hR,hS,hFR,hA,hl]
  all_goals try simp only [←Fp.ofNat_def]
  all_goals grind only

theorem header_phase (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) (nxt : Nat→Fp) (first last trans : Fp)
    (hl:last=0) (hf:first=0 ∨ p=0) :
    ∀e∈phaseGroup,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) params hdr present p)[c]!) nxt first last trans)=0 := by
  obtain ⟨hz,hH,hZ,hA,hF,hD⟩ := ProcPriorCodecSideMultiplicity.header_flags I R present vidV params hdr p
  have ha := (ProcPriorCodecSideZero.header_cells I R present vidV params hdr p).2.1
  apply side_phase
  · rw [ha]; rfl
  · intro c hc
    have hh : c∈[kR,fS,fR,fA,rend,fwg,cg,rs] := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc ⊢
      rcases hc with rfl|rfl|rfl|rfl <;> simp
    rw [hz c hh]; rfl
  · rw [hH,hZ,hA]
    decide +kernel
  · rw [hF,hH]
    split <;> decide +kernel
  · exact hl
  · rw [hF]
    rcases hf with hf|hf
    · rw [hf]; grind
    · simp only [hf,ite_true]
      change first*(1-1)=0
      grind

theorem hash_phase (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) (nxt : Nat→Fp) (first last trans : Fp)
    (hl:last=0) (hf:first=0) :
    ∀e∈phaseGroup,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]!) nxt first last trans)=0 := by
  obtain ⟨hz,hH,hZ,hA,hF,hD⟩ := ProcPriorCodecSideMultiplicity.hash_flags I R present vidV digest hpre base0 j
  have ha := (ProcPriorCodecSideZero.hash_cells I R present vidV digest hpre base0 j).2.1
  apply side_phase
  · rw [ha]; rfl
  · intro c hc
    have hh : c∈[kR,fS,fR,fA,rend,fwg,cg,rs] := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc ⊢
      rcases hc with rfl|rfl|rfl|rfl <;> simp
    rw [hz c hh]; rfl
  · rw [hH,hZ,hA]
    decide +kernel
  · rw [hF,hH]
    decide +kernel
  · exact hl
  · rw [hf]; grind

theorem ash_phase (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (base0 j : Nat) (nxt : Nat→Fp) (first last trans : Fp)
    (hl:last=0) (hf:first=0) :
    ∀e∈phaseGroup,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat (ashRow (instanceCells I R present vidV) I base0 j)[c]!) nxt first last trans)=0 := by
  obtain ⟨hz,hH,hZ,hA,hF,hD⟩ := ProcPriorCodecSideMultiplicity.ash_flags I R present vidV base0 j
  have ha := (ProcPriorCodecSideZero.ash_cells I R present vidV base0 j).2.1
  apply side_phase
  · rw [ha]; rfl
  · intro c hc
    have hh : c∈[kR,fS,fR,fA,rend,fwg,cg,rs] := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc ⊢
      rcases hc with rfl|rfl|rfl|rfl <;> simp
    rw [hz c hh]; rfl
  · rw [hH,hZ,hA]
    decide +kernel
  · rw [hF,hH]
    decide +kernel
  · exact hl
  · rw [hf]; grind

end ZkFormal.NearV3.Candidates.ProcPriorCodecSidePhase
