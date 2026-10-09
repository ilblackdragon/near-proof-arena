import ZkFormal.NearV3.Candidates.ProcPriorCodecSidePhase
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSideBytes
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash SchedSetAll

def byteValue (x : Nat) : Fp :=
  Fp.ofNat 1*Fp.ofNat (Gen.bit x 0)+(Fp.ofNat 2*Fp.ofNat (Gen.bit x 1)+
  (Fp.ofNat 4*Fp.ofNat (Gen.bit x 2)+(Fp.ofNat 8*Fp.ofNat (Gen.bit x 3)+
  (Fp.ofNat 16*Fp.ofNat (Gen.bit x 4)+(Fp.ofNat 32*Fp.ofNat (Gen.bit x 5)+
  (Fp.ofNat 64*Fp.ofNat (Gen.bit x 6)+(Fp.ofNat 128*Fp.ofNat (Gen.bit x 7)+0)))))))

theorem byte_value (x : Nat) (hx:x<256) : byteValue x=Fp.ofNat x := by
  have h : ∀x:Fin 256,byteValue x.val=Fp.ofNat x.val := by decide +kernel
  exact h ⟨x,hx⟩

theorem bits_value (row : Array Nat) (x : Nat) (hx:x<256)
    (hb:∀i,i<8→row[pbit i]! = Gen.bit x i) (nxt : Nat→Fp) (first last trans : Fp) :
    pbitsE.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat row[c]!) nxt first last trans)=Fp.ofNat x := by
  simp only [pbitsE,ZkFormal.Chacha.Rng.Table.num,List.range_succ,List.range_zero,
    List.map_cons,List.map_nil,List.nil_append,List.cons_append,
    ZkFormal.Chacha.Table.E.sum,ZkFormal.Chacha.Table.E.smul,Expr.evalWith,
    ProcPriorCells.env,Bool.false_eq_true,ite_false]
  rw [hb 0 (by decide),hb 1 (by decide),hb 2 (by decide),hb 3 (by decide),
    hb 4 (by decide),hb 5 (by decide),hb 6 (by decide),hb 7 (by decide)]
  exact byte_value x hx

open ZkFormal.Chacha.Table.E in
def byteGroup : List Expr :=
  [.mul encG (sub (c bpost) pbitsE),.mul (notE (c pres)) (c bpre),
   sub (c vbg) (.mul (c pres) encG)]

theorem byte_group_eq : byteGroup=
    ((cKind.drop 79).take 4).filter (fun x=> !ProcPriorCodecActual.retiredKind.contains x) := by decide +kernel

theorem bytes (cur nxt : Nat→Fp) (first last trans : Fp)
    (hR:cur kR=0) (hpost:cur bpost=pbitsE.evalWith (ProcPriorCells.env cur nxt first last trans))
    (hpre:(1-cur pres)*cur bpre=0) (hv:cur vbg=cur pres*(cur kH+cur kZ)) :
    ∀e∈byteGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  simp only [ProcPriorCells.env] at hpost
  intro e he
  simp only [byteGroup,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|rfl|rfl
  all_goals simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,notE,encG,
    Bool.false_eq_true,ite_false,hR]
  all_goals try simp only [←Fp.ofNat_def]
  all_goals grind only

theorem header_byte_cells (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) :
    let row:=headerRow (instanceCells I R present vidV) params hdr present p
    row[pres]! = b2n present ∧ row[bpost]! = hdr[p]! ∧
    row[bpre]! = (if present then hdr[p]! else 0) ∧ row[vbg]! = b2n present := by
  dsimp only
  rw [ProcPriorCodecSideKind.header_scalar I R present vidV params hdr p pres (by decide +kernel),
    ProcPriorCodecHeaderReads.post_byte,
    ProcPriorCodecHeaderReads.projection _ _ _ _ p bpre (by decide +kernel),
    ProcPriorCodecSideTrailer.header_scalar I R present vidV params hdr p vbg (by decide +kernel)]
  simp [instanceCells,ProcPriorCodecHeaderReads.headerScalars,lookup,act,tau,pres,vid,nn,NN,base,fair,itz,zt,kH,kF,pos,bpost,bpre,vbg,ihp,ehp]

theorem hash_byte_cells (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) :
    let row:=hashRow (instanceCells I R present vidV) digest hpre present base0 j
    row[pres]! = b2n present ∧ row[bpost]! = digest[j]! ∧
    row[bpre]! = (if present then hpre[j]! else 0) ∧ row[vbg]! = b2n present := by
  dsimp only
  rw [ProcPriorCodecSideKind.hash_scalar I R present vidV digest hpre base0 j pres (by decide +kernel),
    ProcPriorCodecHashReads.post_byte,
    ProcPriorCodecHashReads.projection _ _ _ _ base0 j bpre (by decide +kernel),
    ProcPriorCodecSideTrailer.hash_scalar I R present vidV digest hpre base0 j vbg (by decide +kernel)]
  simp [instanceCells,ProcPriorCodecHashReads.hashScalars,lookup,act,tau,pres,vid,nn,NN,base,fair,itz,zt,pos,bpost,bpre,vbg,kZ,dgg,sj,bsha,isj,esj]

theorem header_bytes (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) (hb:hdr[p]!<256)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈byteGroup,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) params hdr present p)[c]!) nxt first last trans)=0 := by
  obtain ⟨hz,hH,hZ,hA,hF,hD⟩ := ProcPriorCodecSideMultiplicity.header_flags I R present vidV params hdr p
  obtain ⟨hpr,hpost,hprev,hv⟩ := header_byte_cells I R present vidV params hdr p
  apply bytes
  · rw [hz kR (by simp)]; rfl
  · rw [hpost]
    exact (bits_value _ _ hb (ProcPriorCodecSideKind.header_post_bit I R present vidV params hdr p) nxt first last trans).symm
  · rw [hpr,hprev]
    cases present <;> simp only [b2n,Bool.false_eq_true,ite_false,ite_true]
    all_goals try simp only [←Fp.ofNat_def]
    all_goals grind only
  · rw [hv,hpr,hH,hZ]
    cases present <;> decide +kernel

theorem hash_bytes (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) (hb:digest[j]!<256)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈byteGroup,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]!) nxt first last trans)=0 := by
  obtain ⟨hz,hH,hZ,hA,hF,hD⟩ := ProcPriorCodecSideMultiplicity.hash_flags I R present vidV digest hpre base0 j
  obtain ⟨hpr,hpost,hprev,hv⟩ := hash_byte_cells I R present vidV digest hpre base0 j
  apply bytes
  · rw [hz kR (by simp)]; rfl
  · rw [hpost]
    exact (bits_value _ _ hb (ProcPriorCodecSideKind.hash_post_bit I R present vidV digest hpre base0 j) nxt first last trans).symm
  · rw [hpr,hprev]
    cases present <;> simp only [b2n,Bool.false_eq_true,ite_false,ite_true]
    all_goals try simp only [←Fp.ofNat_def]
    all_goals grind only
  · rw [hv,hpr,hH,hZ]
    cases present <;> decide +kernel

theorem bytes_inactive (cur nxt : Nat→Fp) (first last trans : Fp)
    (hz:∀c∈[kH,kR,kZ,bpre,vbg],cur c=0) :
    ∀e∈byteGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  have hH:=hz kH (by simp)
  have hR:=hz kR (by simp)
  have hZ:=hz kZ (by simp)
  have hpre:=hz bpre (by simp)
  have hv:=hz vbg (by simp)
  intro e he
  simp only [byteGroup,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|rfl|rfl
  all_goals simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,notE,encG,
    Bool.false_eq_true,ite_false,hH,hR,hZ,hpre,hv]
  all_goals grind only

theorem ash_bytes (I : Input) (R : Run) (present : Bool) (vidV base0 j : Nat)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈byteGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (ashRow (instanceCells I R present vidV) I base0 j)[c]!) nxt first last trans)=0 := by
  apply bytes_inactive
  intro c hc
  have hw:c<Codec.width := (by decide +kernel : ∀c∈[kH,kR,kZ,bpre,vbg],c<Codec.width) c hc
  unfold ashRow
  rw [SchedSetAll.cell _ _ _ hw]
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl
  all_goals simp [instanceCells,lookup,act,tau,pres,vid,nn,NN,base,fair,itz,zt,
    kH,kR,kZ,kA,pos,sj,bsha,pm0,pm1,isj,esj,bpre,vbg]
  all_goals rfl

end ZkFormal.NearV3.Candidates.ProcPriorCodecSideBytes
