import ZkFormal.NearV3.Candidates.ProcCodecSuffixKind
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderRegisters
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash SchedSetAll SchedSetAllRange
open ProcPriorCodecNativeBytes

theorem header_register (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p i : Nat) (hi:i<32) :
    (headerRow (instanceCells I R present vidV) params hdr present p)[reg i]! = params.getD (p+i) 0 := by
  have hw : reg i<Codec.width := (by decide +kernel : ∀i:Fin 32,reg i.val<Codec.width) ⟨i,hi⟩
  have hb : (reg i<16∨24≤reg i) ∧ (reg i<79∨87≤reg i) :=
    (by decide +kernel : ∀i:Fin 32,(reg i.val<16∨24≤reg i.val) ∧ (reg i.val<79∨87≤reg i.val)) ⟨i,hi⟩
  have hqb (values : Nat→Nat) (v : Nat) : lookup ((List.range 8).map fun j=>(prbit j,values j)) (reg i) v=v :=
    miss_block 79 8 (reg i) v values hb.2
  have hpb (values : Nat→Nat) (v : Nat) : lookup ((List.range 8).map fun j=>(pbit j,values j)) (reg i) v=v :=
    miss_block 16 8 (reg i) v values hb.1
  unfold headerRow
  rw [SchedSetAll.cell _ _ _ hw,append,hqb,append,hpb,append,
    ProcPriorCodecSideTrailer.register_value _ _ i hi]

theorem native_header_byte (I : Input) (R : Run) (p : Nat) (hp:p<5) :
    (parameters I R).getD p 0=(ProcPriorCodecNativeBytes.header R)[p]! := by
  have h:p=0∨p=1∨p=2∨p=3∨p=4 := by omega
  rcases h with rfl|rfl|rfl|rfl|rfl
  all_goals simp [parameters,ProcPriorCodecNativeBytes.header,List.getD]

theorem native_register_zero (I : Input) (R : Run) (present : Bool) (vidV p : Nat) (hp:p<5) :
    (headerRow (instanceCells I R present vidV) (parameters I R)
      (ProcPriorCodecNativeBytes.header R) present p)[reg 0]! = (ProcPriorCodecNativeBytes.header R)[p]! := by
  rw [header_register _ _ _ _ _ _ _ _ (by decide),Nat.add_zero,native_header_byte I R p hp]

theorem digit2 (n : Nat) (hn:n<65536) : n%256+256*(n/256%256)=n := by omega

theorem digit3 (n : Nat) (hn:n<16777216) :
    n%256+256*(n/256%256)+65536*(n/65536%256)=n := by omega

theorem initial_registers (I : Input) (R : Run) (present : Bool) (vidV : Nat) :
    let row:=headerRow (instanceCells I R present vidV) (parameters I R)
      (ProcPriorCodecNativeBytes.header R) present 0
    row[reg 0]! = 0 ∧ row[reg 3]! = 0 ∧ row[reg 4]! = 0 ∧
    row[reg 1]! = (R.n*R.n)%256 ∧ row[reg 2]! = (R.n*R.n)/256%256 ∧
    row[reg 5]! = I.p.base%256 ∧ row[reg 6]! = I.p.base/256%256 ∧ row[reg 7]! = I.p.base/65536%256 ∧
    row[reg 8]! = (I.p.maxShardBandwidth/R.n)%256 ∧
    row[reg 9]! = (I.p.maxShardBandwidth/R.n)/256%256 ∧
    row[reg 10]! = (I.p.maxShardBandwidth/R.n)/65536%256 := by
  dsimp only
  simp only [header_register I R present vidV _ _ 0 0 (by decide),
    header_register I R present vidV _ _ 0 3 (by decide),
    header_register I R present vidV _ _ 0 4 (by decide),
    header_register I R present vidV _ _ 0 1 (by decide),
    header_register I R present vidV _ _ 0 2 (by decide),
    header_register I R present vidV _ _ 0 5 (by decide),
    header_register I R present vidV _ _ 0 6 (by decide),
    header_register I R present vidV _ _ 0 7 (by decide),
    header_register I R present vidV _ _ 0 8 (by decide),
    header_register I R present vidV _ _ 0 9 (by decide),
    header_register I R present vidV _ _ 0 10 (by decide)]
  simp [parameters,ProcPriorCodecNativeBytes.header,bytesLE,List.range_succ,List.getD]

theorem instance_fields (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (params hdr : List Nat) (p : Nat) :
    let row:=headerRow (instanceCells I R present vidV) params hdr present p
    row[nn]! = R.n ∧ row[NN]! = R.n*R.n ∧ row[base]! = I.p.base ∧
    row[fair]! = I.p.maxShardBandwidth/R.n := by
  have hh:=ProcPriorCodecSideCarry.header_instance I R present vidV params hdr p
  have hn:=hh nn (by decide +kernel)
  have hN:=hh NN (by decide +kernel)
  have hb:=hh base (by decide +kernel)
  have hf:=hh fair (by decide +kernel)
  simp only [ProcPriorCodecSideCarry.instanceValue,instanceCells,lookup,List.foldl_cons,List.foldl_nil] at hn hN hb hf
  simp only [act,tau,pres,vid,nn,NN,base,fair,itz,zt,Nat.reduceEqDiff,ite_true,ite_false,eq_self_iff_true] at hn hN hb hf
  exact ⟨hn,hN,hb,hf⟩

theorem cast_mul (a b : Nat) : Fp.ofNat (a*b)=Fp.ofNat a*Fp.ofNat b := by
  apply Fp.ext
  simp only [Fp.toNat_ofNat,Fp.mul_def,Fp.toNat_mul]
  exact Nat.mul_mod _ _ _

end ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderRegisters
