import ZkFormal.NearV3.Candidates.ProcPriorCodecSideKind
import ZkFormal.NearV3.Candidates.ProcKeyInverse
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSideZero
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash SchedSetAll SchedSetAllRange

theorem disabled (cur nxt : Nat→Fp) (first last trans : Fp) (gate x : Expr) (inv flag : Nat)
    (hg : gate.evalWith (ProcPriorCells.env cur nxt first last trans)=0) (hf : cur flag=0) :
    ∀e∈isZ gate x inv flag,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  intro e he
  simp only [isZ,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|rfl|rfl
  all_goals change _=0
  all_goals simp only [Expr.evalWith,ZkFormal.Chacha.Table.E.sub,notE,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ProcPriorCells.env,ite_false,Bool.false_eq_true,hf] at *
  all_goals grind

theorem enabled (cur nxt : Nat→Fp) (first last trans : Fp) (gate x : Expr) (inv flag a : Nat)
    (hg : gate.evalWith (ProcPriorCells.env cur nxt first last trans)=1)
    (hx : x.evalWith (ProcPriorCells.env cur nxt first last trans)=Fp.ofNat a)
    (hi : cur inv=Fp.ofNat (finv a)) (hf : cur flag=if a%P=0 then 1 else 0) :
    ∀e∈isZ gate x inv flag,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  intro e he
  simp only [isZ,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|rfl|rfl
  · change gate.evalWith _*(cur flag+ -(1+ -(x.evalWith _*cur inv)))=0
    rw [hg,hx,hi,hf]
    have h:=SchedField.zero_flag a
    grind
  · change gate.evalWith _*(x.evalWith _*cur flag)=0
    rw [hg,hx,hf]
    have h:=SchedField.flag_annihilates a
    grind
  · change (1+ -gate.evalWith _)*cur flag=0
    rw [hg]
    grind

theorem difference (cur nxt : Nat→Fp) (first last trans : Fp) (gate x : Expr) (inv flag a b : Nat)
    (ha:a<P) (hb:b<P) (hg : gate.evalWith (ProcPriorCells.env cur nxt first last trans)=1)
    (hx : x.evalWith (ProcPriorCells.env cur nxt first last trans)=Fp.ofNat a-Fp.ofNat b)
    (hi : cur inv=Fp.ofNat (finv (fsub a b))) (hf : cur flag=if a=b then 1 else 0) :
    ∀e∈isZ gate x inv flag,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  apply enabled cur nxt first last trans gate x inv flag (fsub a b) hg
  · rw [hx,SchedField.fsub_cast]
  · exact hi
  · simpa only [ProcKeyInverse.difference_zero a b ha hb] using hf

def zeroColumns : List Nat := [act,kH,kR,kZ,kA,fA,e7,e2,ekl,ehp,esj,zt,tau,pos,sj,ihp,isj,itz]

theorem scalar_miss (c v : Nat) (values : Nat→Nat) (hc:c∈zeroColumns) :
    lookup ((List.range 32).map fun i=>(reg i,values i)) c v=v ∧
    lookup ((List.range 8).map fun i=>(pbit i,values i)) c v=v ∧
    lookup ((List.range 8).map fun i=>(prbit i,values i)) c v=v := by
  constructor
  · apply lookup_miss
    intro p hp
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
    have hh : ∀i:Fin 32,∀c∈zeroColumns,reg i.val≠c := by decide +kernel
    exact hh ⟨i,List.mem_range.mp hi⟩ c hc
  · have hh : ∀c∈zeroColumns,(c<16∨24≤c) ∧ (c<79∨87≤c) := by decide +kernel
    exact ⟨miss_block 16 8 c v values (hh c hc).1,miss_block 79 8 c v values (hh c hc).2⟩

theorem header_scalar (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p c : Nat) (hc:c∈zeroColumns) :
    (headerRow (instanceCells I R present vidV) params hdr present p)[c]! =
      lookup (instanceCells I R present vidV++ProcPriorCodecHeaderReads.headerScalars hdr present p) c 0 := by
  have hw : c<Codec.width := (by decide +kernel : ∀c∈zeroColumns,c<Codec.width) c hc
  unfold headerRow
  rw [SchedSetAll.cell _ _ c hw,append,(scalar_miss c _ _ hc).2.2,
    append,(scalar_miss c _ _ hc).2.1,append,(scalar_miss c _ _ hc).1]
  rfl

theorem hash_scalar (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j c : Nat) (hc:c∈zeroColumns) :
    (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]! =
      lookup (instanceCells I R present vidV++ProcPriorCodecHashReads.hashScalars digest hpre present base0 j) c 0 := by
  have hw : c<Codec.width := (by decide +kernel : ∀c∈zeroColumns,c<Codec.width) c hc
  unfold hashRow
  rw [SchedSetAll.cell _ _ c hw,append,(scalar_miss c _ _ hc).2.2,
    append,(scalar_miss c _ _ hc).2.1,append,(scalar_miss c _ _ hc).1]
  rfl

theorem header_lookup (a t pr v n n2 b f it z h kf p bp br vb ip ep : Nat) :
 let xs := [(act,a),(tau,t),(pres,pr),(vid,v),(nn,n),(NN,n2),(base,b),(fair,f),(itz,it),(zt,z),(kH,h),(kF,kf),(pos,p),(bpost,bp),(bpre,br),(vbg,vb),(ihp,ip),(ehp,ep)]
 (∀c∈[kR,kZ,kA,fA,e7,e2,ekl,esj],lookup xs c 0=0) ∧
 lookup xs act 0=a ∧
 lookup xs tau 0=t ∧
 lookup xs itz 0=it ∧
 lookup xs zt 0=z ∧
 lookup xs kH 0=h ∧
 lookup xs pos 0=p ∧
 lookup xs ihp 0=ip ∧
 lookup xs ehp 0=ep := by
  dsimp only
  constructor
  · intro c hc
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [lookup,act,tau,pres,vid,nn,NN,base,fair,itz,zt,kH,kF,pos,bpost,bpre,vbg,ihp,ehp,kR,kZ,kA,fA,e7,e2,ekl,esj]
  · simp [lookup,act,tau,pres,vid,nn,NN,base,fair,itz,zt,kH,kF,pos,bpost,bpre,vbg,ihp,ehp]

theorem header_cells (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) :
    let row:=headerRow (instanceCells I R present vidV) params hdr present p
    (∀c∈[kR,kZ,kA,fA,e7,e2,ekl,esj],row[c]! = 0) ∧ row[act]! = 1 ∧ row[kH]! = 1 ∧
      row[pos]! = p ∧ row[ihp]! = finv (fsub (p) 4) ∧
      row[ehp]! = (if p=4 then 1 else 0) ∧ row[tau]! = R.tau ∧
      row[itz]! = finv R.tau ∧ row[zt]! = (if R.tau=0 then 1 else 0) := by
  have h := header_lookup 1 R.tau (b2n present) vidV R.n (R.n*R.n) I.p.base
    (I.p.maxShardBandwidth/R.n) (finv R.tau) (if R.tau=0 then 1 else 0)
    1 (if p=0 then 1 else 0) p hdr[p]! (if present then hdr[p]! else 0)
    (b2n present) (finv (fsub p 4)) (if p=4 then 1 else 0)
  change (∀c∈[kR,kZ,kA,fA,e7,e2,ekl,esj],lookup (instanceCells I R present vidV++ProcPriorCodecHeaderReads.headerScalars hdr present p) c 0=0) ∧ _ at h
  dsimp only
  constructor
  · intro c hc
    have hsc : c∈zeroColumns := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
    rw [header_scalar I R present vidV params hdr p c hsc]
    exact h.1 c hc
  · simp only [header_scalar I R present vidV params hdr p act (by decide +kernel),
      header_scalar I R present vidV params hdr p kH (by decide +kernel),
      header_scalar I R present vidV params hdr p pos (by decide +kernel),
      header_scalar I R present vidV params hdr p ihp (by decide +kernel),
      header_scalar I R present vidV params hdr p ehp (by decide +kernel),
      header_scalar I R present vidV params hdr p tau (by decide +kernel),
      header_scalar I R present vidV params hdr p itz (by decide +kernel),
      header_scalar I R present vidV params hdr p zt (by decide +kernel)]
    exact ⟨h.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩
theorem hash_lookup (a t pr v n n2 b f it z zz p j bp br bs vb dg ij ej : Nat) :
 let xs := [(act,a),(tau,t),(pres,pr),(vid,v),(nn,n),(NN,n2),(base,b),(fair,f),(itz,it),(zt,z),(kZ,zz),(dgg,dg),(pos,p),(sj,j),(bpost,bp),(bpre,br),(bsha,bs),(vbg,vb),(isj,ij),(esj,ej)]
 (∀c∈[kR,kH,kA,fA,e7,e2,ekl,ehp],lookup xs c 0=0) ∧
 lookup xs act 0=a ∧
 lookup xs tau 0=t ∧
 lookup xs itz 0=it ∧
 lookup xs zt 0=z ∧
 lookup xs kZ 0=zz ∧
 lookup xs sj 0=j ∧
 lookup xs isj 0=ij ∧
 lookup xs esj 0=ej := by
  dsimp only
  constructor
  · intro c hc
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [lookup,act,tau,pres,vid,nn,NN,base,fair,itz,zt,kZ,pos,sj,bpost,bpre,bsha,vbg,dgg,isj,esj,kR,kH,kA,fA,e7,e2,ekl,ehp]
  · simp [lookup,act,tau,pres,vid,nn,NN,base,fair,itz,zt,kZ,pos,sj,bpost,bpre,bsha,vbg,dgg,isj,esj]

theorem hash_cells (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) :
    let row:=hashRow (instanceCells I R present vidV) digest hpre present base0 j
    (∀c∈[kR,kH,kA,fA,e7,e2,ekl,ehp],row[c]! = 0) ∧ row[act]! = 1 ∧ row[kZ]! = 1 ∧
      row[sj]! = j ∧ row[isj]! = finv (fsub (j) 31) ∧
      row[esj]! = (if j=31 then 1 else 0) ∧ row[tau]! = R.tau ∧
      row[itz]! = finv R.tau ∧ row[zt]! = (if R.tau=0 then 1 else 0) := by
  have h := hash_lookup 1 R.tau (b2n present) vidV R.n (R.n*R.n) I.p.base
    (I.p.maxShardBandwidth/R.n) (finv R.tau) (if R.tau=0 then 1 else 0)
    1 (base0+j) j digest[j]! (if present then hpre[j]! else 0) (if present then hpre[j]! else 0) (b2n present) (if j=0 then 1 else 0) (finv (fsub j 31)) (if j=31 then 1 else 0)
  change (∀c∈[kR,kH,kA,fA,e7,e2,ekl,ehp],lookup (instanceCells I R present vidV++ProcPriorCodecHashReads.hashScalars digest hpre present base0 j) c 0=0) ∧ _ at h
  dsimp only
  constructor
  · intro c hc
    have hsc : c∈zeroColumns := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
    rw [hash_scalar I R present vidV digest hpre base0 j c hsc]
    exact h.1 c hc
  · simp only [hash_scalar I R present vidV digest hpre base0 j act (by decide +kernel),
      hash_scalar I R present vidV digest hpre base0 j kZ (by decide +kernel),
      hash_scalar I R present vidV digest hpre base0 j sj (by decide +kernel),
      hash_scalar I R present vidV digest hpre base0 j isj (by decide +kernel),
      hash_scalar I R present vidV digest hpre base0 j esj (by decide +kernel),
      hash_scalar I R present vidV digest hpre base0 j tau (by decide +kernel),
      hash_scalar I R present vidV digest hpre base0 j itz (by decide +kernel),
      hash_scalar I R present vidV digest hpre base0 j zt (by decide +kernel)]
    exact ⟨h.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩

theorem ash_lookup (a t pr v n n2 b f it z aa p j bs p0 p1 ij ej : Nat) :
 let xs := [(act,a),(tau,t),(pres,pr),(vid,v),(nn,n),(NN,n2),(base,b),(fair,f),(itz,it),(zt,z),(kA,aa),(pos,p),(sj,j),(bsha,bs),(pm0,p0),(pm1,p1),(isj,ij),(esj,ej)]
 (∀c∈[kR,kH,kZ,fA,e7,e2,ekl,ehp],lookup xs c 0=0) ∧
 lookup xs act 0=a ∧
 lookup xs tau 0=t ∧
 lookup xs itz 0=it ∧
 lookup xs zt 0=z ∧
 lookup xs kA 0=aa ∧
 lookup xs sj 0=j ∧
 lookup xs isj 0=ij ∧
 lookup xs esj 0=ej := by
  dsimp only
  constructor
  · intro c hc
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [lookup,act,tau,pres,vid,nn,NN,base,fair,itz,zt,kA,pos,sj,bsha,pm0,pm1,isj,esj,kR,kH,kZ,fA,e7,e2,ekl,ehp]
  · simp [lookup,act,tau,pres,vid,nn,NN,base,fair,itz,zt,kA,pos,sj,bsha,pm0,pm1,isj,esj]

theorem ash_cells (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (base0 j : Nat) :
    let row:=ashRow (instanceCells I R present vidV) I base0 j
    (∀c∈[kR,kH,kZ,fA,e7,e2,ekl,ehp],row[c]! = 0) ∧ row[act]! = 1 ∧ row[kA]! = 1 ∧
      row[sj]! = 32+j ∧ row[isj]! = finv (fsub (32+j) 63) ∧
      row[esj]! = (if j=31 then 1 else 0) ∧ row[tau]! = R.tau ∧
      row[itz]! = finv R.tau ∧ row[zt]! = (if R.tau=0 then 1 else 0) := by
  have h := ash_lookup 1 R.tau (b2n present) vidV R.n (R.n*R.n) I.p.base
    (I.p.maxShardBandwidth/R.n) (finv R.tau) (if R.tau=0 then 1 else 0)
    1 (base0+32+j) (32+j) (I.ash.getD j 0).toNat j (I.ash.getD j 0).toNat (finv (fsub (32+j) 63)) (if j=31 then 1 else 0)
  dsimp only
  constructor
  · intro c hc
    have hw : c<Codec.width := (by decide +kernel : ∀c∈[kR,kH,kZ,fA,e7,e2,ekl,ehp],c<Codec.width) c hc
    unfold ashRow
    rw [SchedSetAll.cell _ _ _ hw]
    exact h.1 c hc
  · unfold ashRow
    rw [SchedSetAll.cell _ _ act (by decide +kernel),
      SchedSetAll.cell _ _ kA (by decide +kernel),
      SchedSetAll.cell _ _ sj (by decide +kernel),
      SchedSetAll.cell _ _ isj (by decide +kernel),
      SchedSetAll.cell _ _ esj (by decide +kernel),
      SchedSetAll.cell _ _ tau (by decide +kernel),
      SchedSetAll.cell _ _ itz (by decide +kernel),
      SchedSetAll.cell _ _ zt (by decide +kernel)]
    exact ⟨h.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩

open ZkFormal.Chacha.Table.E in
def recordTests : List Expr := isZ (c kR) (sub (c g) (k 7)) ig7 e7 ++
  isZ (c fA) (sub (c g) (k 2)) ig2 e2 ++
  isZ (c kR) (sub (c kidx) (sub (c NN) (k 1))) ikl ekl

theorem record_tests (row : Array Nat) (nxt : Nat→Fp) (first last trans : Fp)
    (hz : ∀c∈[kR,fA,e7,e2,ekl],row[c]! = 0) :
    ∀e∈recordTests,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat row[c]!) nxt first last trans)=0 := by
  simp only [recordTests,List.forall_mem_append]
  refine ⟨⟨?_,?_⟩,?_⟩
  all_goals apply disabled
  all_goals first
    | (rw [hz _ (by simp)]; rfl)
    | (simp only [ZkFormal.Chacha.Table.E.c,Expr.evalWith,ProcPriorCells.env,ite_false,Bool.false_eq_true]; rw [hz _ (by simp)]; rfl)

theorem tau_test (row : Array Nat) (t : Nat) (ht:t<P) (nxt : Nat→Fp) (first last trans : Fp)
    (ha : row[act]! = 1) (htau : row[tau]! = t) (hi : row[itz]! = finv t)
    (hf : row[zt]! = if t=0 then 1 else 0) :
    ∀e∈isZ (ZkFormal.Chacha.Table.E.c act) (ZkFormal.Chacha.Table.E.c tau) itz zt,
      e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat row[c]!) nxt first last trans)=0 := by
  apply enabled _ nxt first last trans _ _ itz zt t
  · change Fp.ofNat row[act]! = 1
    rw [ha]; rfl
  · change Fp.ofNat row[tau]! = Fp.ofNat t
    rw [htau]
  · rw [hi]
  · rw [hf,Nat.mod_eq_of_lt ht]
    by_cases hz:t=0 <;> simp only [hz,ite_true,ite_false] <;> rfl
open ZkFormal.Chacha.Table.E in
def headerTest : List Expr := isZ (c kH) (sub (c pos) (k 4)) ihp ehp
open ZkFormal.Chacha.Table.E in
def shaTest : List Expr := isZ (.add (c kZ) (c kA)) (sub (c sj) (.add (k 31) (.mul (k 32) (c kA)))) isj esj

theorem header_test (row : Array Nat) (p : Nat) (hp:p<P) (nxt : Nat→Fp) (first last trans : Fp)
    (hk:row[kH]! = 1) (hpos:row[pos]! = p) (hi:row[ihp]! = finv (fsub p 4))
    (hf:row[ehp]! = if p=4 then 1 else 0) :
    ∀e∈headerTest,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat row[c]!) nxt first last trans)=0 := by
  apply difference _ nxt first last trans _ _ ihp ehp p 4 hp (by decide +kernel)
  · change Fp.ofNat row[kH]! = 1
    rw [hk]; rfl
  · change Fp.ofNat row[pos]! + -(Fp.ofNat 4) = _
    rw [hpos,Lean.Grind.Ring.sub_eq_add_neg]
  · rw [hi]
  · rw [hf]
    split <;> rfl

theorem sha_test (row : Array Nat) (a b : Nat) (ha:a<P) (hb:b<P)
    (nxt : Nat→Fp) (first last trans : Fp)
    (hg:Fp.ofNat row[kZ]! + Fp.ofNat row[kA]! = 1)
    (hs:row[sj]! = a) (hbv:Fp.ofNat 31+Fp.ofNat 32*Fp.ofNat row[kA]! = Fp.ofNat b)
    (hi:row[isj]! = finv (fsub a b)) (hf:row[esj]! = if a=b then 1 else 0) :
    ∀e∈shaTest,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat row[c]!) nxt first last trans)=0 := by
  apply difference _ nxt first last trans _ _ isj esj a b ha hb
  · exact hg
  · change Fp.ofNat row[sj]! + -(Fp.ofNat 31+Fp.ofNat 32*Fp.ofNat row[kA]!) = _
    rw [hs,hbv,Lean.Grind.Ring.sub_eq_add_neg]
  · rw [hi]
  · rw [hf]
    split <;> rfl

def zeroTests : List Expr := recordTests++headerTest++shaTest++
  isZ (ZkFormal.Chacha.Table.E.c act) (ZkFormal.Chacha.Table.E.c tau) itz zt

theorem header_zeros (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) (hp:p<5) (ht:R.tau<P)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈zeroTests,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) params hdr present p)[c]!) nxt first last trans)=0 := by
  obtain ⟨hz,ha,hk,hpos,hi,hflag,htau,hit,hzt⟩ := header_cells I R present vidV params hdr p
  have hpP:p<P := by exact Nat.lt_trans hp (by decide +kernel)
  simp only [zeroTests,List.forall_mem_append]
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · apply record_tests
    intro c hc
    apply hz c
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc ⊢
    rcases hc with rfl|rfl|rfl|rfl|rfl <;> simp
  · exact header_test _ p hpP nxt first last trans hk hpos hi hflag
  · apply disabled
    · change Fp.ofNat _ + Fp.ofNat _ = 0
      rw [hz kZ (by simp),hz kA (by simp)]
      decide +kernel
    · change Fp.ofNat _ = 0
      rw [hz esj (by simp)]; rfl
  · exact tau_test _ R.tau ht nxt first last trans ha htau hit hzt

theorem hash_zeros (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) (hj:j<32) (ht:R.tau<P)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈zeroTests,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]!) nxt first last trans)=0 := by
  obtain ⟨hz,ha,hk,hpos,hi,hflag,htau,hit,hzt⟩ := hash_cells I R present vidV digest hpre base0 j
  have hjP:j<P := by exact Nat.lt_trans hj (by decide +kernel)
  simp only [zeroTests,List.forall_mem_append]
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · apply record_tests
    intro c hc
    apply hz c
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc ⊢
    rcases hc with rfl|rfl|rfl|rfl|rfl <;> simp
  · apply disabled
    · change Fp.ofNat _ = 0
      rw [hz kH (by simp)]; rfl
    · change Fp.ofNat _ = 0
      rw [hz ehp (by simp)]; rfl
  · apply sha_test _ j 31 hjP (by decide +kernel) nxt first last trans
    · rw [hk,hz kA (by simp)]
      decide +kernel
    · exact hpos
    · rw [hz kA (by simp)]
      decide +kernel
    · exact hi
    · exact hflag
  · exact tau_test _ R.tau ht nxt first last trans ha htau hit hzt

theorem ash_zeros (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (base0 j : Nat) (hj:j<32) (ht:R.tau<P)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈zeroTests,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat (ashRow (instanceCells I R present vidV) I base0 j)[c]!) nxt first last trans)=0 := by
  obtain ⟨hz,ha,hk,hpos,hi,hflag,htau,hit,hzt⟩ := ash_cells I R present vidV base0 j
  have hjP:32+j<P := by
    have hh:64<P := by decide +kernel
    omega
  simp only [zeroTests,List.forall_mem_append]
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · apply record_tests
    intro c hc
    apply hz c
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc ⊢
    rcases hc with rfl|rfl|rfl|rfl|rfl <;> simp
  · apply disabled
    · change Fp.ofNat _ = 0
      rw [hz kH (by simp)]; rfl
    · change Fp.ofNat _ = 0
      rw [hz ehp (by simp)]; rfl
  · apply sha_test _ (32+j) 63 hjP (by decide +kernel) nxt first last trans
    · rw [hk,hz kZ (by simp)]
      decide +kernel
    · exact hpos
    · rw [hk]
      decide +kernel
    · exact hi
    · simpa only [show 32+j=63 ↔ j=31 by omega] using hflag
  · exact tau_test _ R.tau ht nxt first last trans ha htau hit hzt

theorem zero_group_eq : zeroTests = (cKind.drop 52).take 18 := by decide +kernel

theorem zero_group_retained :
    zeroTests.filter (fun x=> !ProcPriorCodecActual.retiredKind.contains x) = zeroTests := by decide +kernel

end ZkFormal.NearV3.Candidates.ProcPriorCodecSideZero
