import ZkFormal.NearV3.Candidates.ProcPriorCodecGridField
import ZkFormal.NearV3.Candidates.ProcPriorCells
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGridCells
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcPriorCodecGrid ProcPriorCodecGridField Codec

def cell (n k f g : Nat) (bs : List Nat) (c : Nat) : Fp :=
  if c=srcC then Fp.ofNat (sender n k)
  else if c=useC then Fp.ofNat (receiver n k)
  else if c=nn then Fp.ofNat n
  else if c=kidx then Fp.ofNat k
  else if c=hasC then flag (receiver n k+1=n)
  else if c=rs then flag (f=0 ∧ g=0)
  else if c=nzb then flag (f=0 ∧ g=0 ∧ receiver n k=0)
  else if c=ig2 then Fp.ofNat (finv (receiver n k))
  else if c=ib then Fp.ofNat (finv (fsub (receiver n k) (n-1)))
  else if c=kR then 1
  else if c=rend then flag (f=2 ∧ g=7)
  else if c=ekl then flag (k+1=n*n)
  else if c=fA then flag (f=2)
  else if c=fS then flag (f=0)
  else if c=e7 then flag (g=7)
  else if c=bpost then Fp.ofNat (bs.getD g 0)
  else if 79≤c ∧ c<87 then Fp.ofNat (bs.getD (g+(c-79)) 0)
  else 0

def next (n k f g : Nat) (bs : List Nat) : Nat→Fp :=
  if g=7 then
    if f=2 then cell n (k+1) 0 0 bs else cell n k (f+1) 0 bs
  else cell n k f (g+1) bs

def env (n k f g : Nat) (bs : List Nat) : Env Fp :=
  ProcPriorCells.env (cell n k f g bs) (next n k f g bs) 0 0 1

/-- A projection onto exactly the new Codec columns; unaffected record columns
remain the responsibility of the original record equations. -/
theorem index (n k f g : Nat) (bs : List Nat) :
    ((ProcPriorCodecActual.additions)[2]!).evalWith (env n k f g bs)=0 := by
  have h : receiver n k+sender n k*n=k := by simpa only [Nat.add_comm] using reconstruct n k
  simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,Expr.evalWith,env,ProcPriorCells.env,
    cell,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,
    ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
    ZkFormal.Chacha.Table.E.k] at ⊢
  rw [reconstruct]
  grind

theorem sender_transition (n k f g : Nat) (bs : List Nat) (hn:0<n) :
    ((ProcPriorCodecActual.additions)[8]!).evalWith (env n k f g bs)=0 := by
  have hs:=sender_equation n k hn
  by_cases he:f=2 ∧ g=7
  · obtain ⟨rfl,rfl⟩:=he
    simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,Expr.evalWith,env,ProcPriorCells.env,
      cell,next,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k,Codec.mul3,Codec.notE] at ⊢
    try rw [hadd]
    have hone : Fp.ofNat 1=(1 : Fp) := rfl
    rw [hone]
    grind
  · simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,Expr.evalWith,env,ProcPriorCells.env,
      cell,next,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k,Codec.mul3,Codec.notE,flag,he]
    grind

theorem receiver_transition (n k f g : Nat) (bs : List Nat) (hn:0<n) :
    ((ProcPriorCodecActual.additions)[9]!).evalWith (env n k f g bs)=0 := by
  have hs:=receiver_equation n k hn
  have hadd : Fp.ofNat (receiver n k+1)=Fp.ofNat (receiver n k)+1 := by
    change ((receiver n k+1 : Nat) : Fp)=(receiver n k : Fp)+1
    grind
  by_cases he:f=2 ∧ g=7
  · obtain ⟨rfl,rfl⟩:=he
    simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,Expr.evalWith,env,ProcPriorCells.env,
      cell,next,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k,Codec.mul3,Codec.notE] at ⊢
    try rw [hadd]
    have hone : Fp.ofNat 1=(1 : Fp) := rfl
    rw [hone]
    grind
  · simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,Expr.evalWith,env,ProcPriorCells.env,
      cell,next,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k,Codec.mul3,Codec.notE,flag,he]
    grind

theorem receiver_inverse (n k f g : Nat) (bs : List Nat) (hn:0<n) (hn64:n≤64) :
    ((ProcPriorCodecActual.additions)[5]!).evalWith (env n k f g bs)=0 := by
  have hs:=receiver_test n k hn hn64
  simp at hs
  by_cases he:f=0 ∧ g=0
  · obtain ⟨rfl,rfl⟩:=he
    simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,Expr.evalWith,env,ProcPriorCells.env,
      cell,next,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k,Codec.mul3,Codec.notE] at ⊢
    have hone : Fp.ofNat 1=(1 : Fp) := rfl
    try rw [hone]
    grind
  · simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,Expr.evalWith,env,ProcPriorCells.env,
      cell,next,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k,Codec.mul3,Codec.notE,flag,he] at ⊢
    grind

theorem receiver_zero (n k f g : Nat) (bs : List Nat) (hn:0<n) (hn64:n≤64) :
    ((ProcPriorCodecActual.additions)[6]!).evalWith (env n k f g bs)=0 := by
  have hs:=receiver_annihilates n k
  by_cases he:f=0 ∧ g=0
  · obtain ⟨rfl,rfl⟩:=he
    simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,Expr.evalWith,env,ProcPriorCells.env,
      cell,next,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k,Codec.mul3,Codec.notE] at ⊢
    have hone : Fp.ofNat 1=(1 : Fp) := rfl
    try rw [hone]
    grind
  · simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,Expr.evalWith,env,ProcPriorCells.env,
      cell,next,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k,Codec.mul3,Codec.notE,flag,he] at ⊢
    grind

theorem wrap_inverse (n k f g : Nat) (bs : List Nat) (hn:0<n) (hn64:n≤64) :
    ((ProcPriorCodecActual.additions)[3]!).evalWith (env n k f g bs)=0 := by
  have hs:=wrap_test n k hn hn64
  try simp at hs
  have hp : Fp.ofNat (n-1)=Fp.ofNat n-1 := by
    have hh : n-1+1=n := by omega
    have hf:=congrArg Fp.ofNat hh
    change ((n-1+1 : Nat) : Fp)=(n : Fp) at hf
    change ((n-1 : Nat) : Fp)=(n : Fp)-1
    grind
  by_cases he:f=0 ∧ g=0
  · obtain ⟨rfl,rfl⟩:=he
    simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,Expr.evalWith,env,ProcPriorCells.env,
      cell,next,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k,Codec.mul3,Codec.notE] at ⊢
    have hone : Fp.ofNat 1=(1 : Fp) := rfl
    try rw [hone]
    grind
  · simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,Expr.evalWith,env,ProcPriorCells.env,
      cell,next,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k,Codec.mul3,Codec.notE,flag,he] at ⊢
    grind

theorem wrap_zero (n k f g : Nat) (bs : List Nat) (hn:0<n) (hn64:n≤64) :
    ((ProcPriorCodecActual.additions)[4]!).evalWith (env n k f g bs)=0 := by
  have hs:=wrap_annihilates n k
  have hp : Fp.ofNat (n-1)=Fp.ofNat n-1 := by
    have hh : n-1+1=n := by omega
    have hf:=congrArg Fp.ofNat hh
    change ((n-1+1 : Nat) : Fp)=(n : Fp) at hf
    change ((n-1 : Nat) : Fp)=(n : Fp)-1
    grind
  by_cases he:f=0 ∧ g=0
  · obtain ⟨rfl,rfl⟩:=he
    simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,Expr.evalWith,env,ProcPriorCells.env,
      cell,next,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k,Codec.mul3,Codec.notE] at ⊢
    have hone : Fp.ofNat 1=(1 : Fp) := rfl
    try rw [hone]
    grind
  · simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,Expr.evalWith,env,ProcPriorCells.env,
      cell,next,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k,Codec.mul3,Codec.notE,flag,he] at ⊢
    grind

theorem basic (n k f g : Nat) (bs : List Nat) (j : Nat) (hj:j∈[0,1,7,10,11]) :
    ((ProcPriorCodecActual.additions)[j]!).evalWith (env n k f g bs)=0 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl
  all_goals simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,Expr.evalWith,env,ProcPriorCells.env,
      cell,next,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,
      ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k,Codec.mul3,Codec.notE]
  all_goals try simp only [show Fp.ofNat 1=(1 : Fp) from rfl]
  all_goals try unfold flag
  all_goals repeat (first | split | (solve | grind))

theorem id_shift (n k f g : Nat) (bs : List Nat) (i : Nat) (hi:i<7) :
    ((ProcPriorCodecActual.additions)[12+i]!).evalWith (env n k f g bs)=0 := by
  have hc:i=0∨i=1∨i=2∨i=3∨i=4∨i=5∨i=6 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals by_cases hf:f=0
  all_goals by_cases hg:g=7
  all_goals simp [ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte,Codec.prbit,Codec.isZ,
      Expr.evalWith,env,ProcPriorCells.env,cell,next,srcC,useC,nn,kidx,hasC,rs,nzb,ig2,ib,
      kR,rend,ekl,fA,fS,e7,bpost,ehp,bpre,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.n,
      ZkFormal.Chacha.Table.E.k,Codec.mul3,Codec.notE,flag,hf,hg,Nat.add_assoc]
  all_goals try simp only [show Fp.ofNat 1=(1 : Fp) from rfl]
  all_goals grind

/-- All nineteen added constraints vanish on the native record projection.
This does not assert original Codec constraints or generator-array indexing. -/
theorem additions (n k f g : Nat) (bs : List Nat) (hn:0<n) (hn64:n≤64) :
    ∀e∈ProcPriorCodecActual.additions,e.evalWith (env n k f g bs)=0 := by
  intro e he
  obtain ⟨j,hj,he⟩:=List.mem_iff_getElem.mp he
  have hlen:ProcPriorCodecActual.additions.length=19 := by decide +kernel
  have hj19:j<19 := by simpa only [hlen] using hj
  have he' : ProcPriorCodecActual.additions[j]! = e := by simpa only [getElem!_pos ProcPriorCodecActual.additions j hj] using he
  rw [←he']
  by_cases hb:j∈[0,1,7,10,11]
  · exact basic n k f g bs j hb
  by_cases hj2:j=2
  · subst j; exact index n k f g bs
  by_cases hj3:j=3
  · subst j; exact wrap_inverse n k f g bs hn hn64
  by_cases hj4:j=4
  · subst j; exact wrap_zero n k f g bs hn hn64
  by_cases hj5:j=5
  · subst j; exact receiver_inverse n k f g bs hn hn64
  by_cases hj6:j=6
  · subst j; exact receiver_zero n k f g bs hn hn64
  by_cases hj8:j=8
  · subst j; exact sender_transition n k f g bs hn
  by_cases hj9:j=9
  · subst j; exact receiver_transition n k f g bs hn
  have hge:12≤j := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hb; omega
  have hi:j-12<7 := by omega
  simpa only [Nat.add_sub_cancel' hge] using id_shift n k f g bs (j-12) hi

end ZkFormal.NearV3.Candidates.ProcPriorCodecGridCells
