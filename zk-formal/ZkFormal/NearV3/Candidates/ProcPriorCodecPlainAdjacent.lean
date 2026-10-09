import ZkFormal.NearV3.Candidates.ProcPriorCodecPlainCells
import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeHash
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecPlainAdjacent
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecPlainStep ProcPriorCodecPlainCells ProcPriorCodecNativeHash
open ProcPriorCodecRecordReads SchedSetAll

theorem cells (I : Input) (R : Run) (present : Bool) (gbA : Array Nat)
    (vidV k f g : Nat) (hf:f<2) :
    let r:=row I R present gbA (instanceCells I R present vidV) k f g
    r[kR]! = 1 ∧ r[Codec.g]! = g ∧ r[e7]! = (if g=7 then 1 else 0) ∧
      r[fS]! = (if f=0 then 1 else 0) ∧ r[fR]! = (if f=1 then 1 else 0) ∧
      r[fA]! = 0 ∧ r[kidx]! = k ∧ r[rend]! = 0 := by
  dsimp only
  have h:=projection I R present gbA (instanceCells I R present vidV) k f g
  rw [h kR hf (by simp [columns]),h Codec.g hf (by simp [columns]),h e7 hf (by simp [columns]),
    h fS hf (by simp [columns]),h fR hf (by simp [columns]),h fA hf (by simp [columns]),
    h kidx hf (by simp [columns]),h rend hf (by simp [columns])]
  have hf2:f≠2 := by omega
  simp [scalars,instanceCells,lookup,act,kR,kH,kZ,kA,kF,ehp,fS,fR,fA,
    pos,bpost,bpre,vbg,kidx,klo,khi,Codec.g,ig7,e7,ikl,ekl,tau,pres,vid,nn,NN,base,fair,itz,zt,rend,hf2]

/-- All five inside-field transition equations hold on actual consecutive native rows. -/
theorem inside (I : Input) (R : Run) (present : Bool) (gbA : Array Nat)
    (vidV k f g : Nat) (hf:f<2) (hg:g<7) (first last trans : Fp) :
    let cur:=row I R present gbA (instanceCells I R present vidV) k f g
    let nxt:=row I R present gbA (instanceCells I R present vidV) k f (g+1)
    ∀e∈(cRec.drop 1).take 5,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat cur[c]!) (fun c=>Fp.ofNat nxt[c]!) first last trans)=0 := by
  dsimp only
  have hc:=cells I R present gbA vidV k f g hf
  have hn:=cells I R present gbA vidV k f (g+1) hf
  dsimp only at hc hn
  obtain ⟨hr,hg0,he,hS,hR,hA,hk,hend⟩:=hc
  obtain ⟨nr,ng0,ne,nS,nR,nA,nk,nend⟩:=hn
  have hg7:g≠7 := by omega
  simp only [cRec,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false]
  intro e heq
  rcases heq with rfl|rfl|rfl|rfl|rfl
  all_goals simp [mul3,notE,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,
    hr,hg0,he,hS,hR,hA,hk,ng0,nS,nR,nA,nk,hg7]
  all_goals grind
/-- Two actual loop iterations append the certified adjacent rows, without an
assumed row-shape or successful-execution premise. -/
theorem executed_inside (I : Input) (R : Run) (present : Bool) (gbA : Array Nat)
    (fwd : List (Nat×Nat)) (vidV k f g : Nat) (st : ProcPriorCodecRecordStep.State)
    (hf:f<2) (hg:g<7) (first last trans : Fp) :
    let inst:=instanceCells I R present vidV
    let cur:=row I R present gbA inst k f g
    let nxt:=row I R present gbA inst k f (g+1)
    ProcPriorCodecRecordStep.step I R present gbA fwd inst k f g st =
      .ok (.yield (st.1.push cur,st.2)) ∧
    ProcPriorCodecRecordStep.step I R present gbA fwd inst k f (g+1) (st.1.push cur,st.2) =
      .ok (.yield ((st.1.push cur).push nxt,st.2)) ∧
    ∀e∈(cRec.drop 1).take 5,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat cur[c]!) (fun c=>Fp.ofNat nxt[c]!) first last trans)=0 := by
  dsimp only
  exact ⟨step_eq _ _ _ _ _ _ _ _ _ _ hf,step_eq _ _ _ _ _ _ _ _ _ _ hf,
    inside I R present gbA vidV k f g hf hg first last trans⟩

end ZkFormal.NearV3.Candidates.ProcPriorCodecPlainAdjacent
