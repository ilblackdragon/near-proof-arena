import ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderRegisters
import ZkFormal.NearV3.Candidates.ProcActualParameterGuard
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderInitial
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash ProcPriorCodecHeaderRegisters ProcPriorCodecNativeBytes
open ProcPriorCodecSideNext (cast_add)

open ZkFormal.Chacha.Table.E in
def initialGroup : List Expr :=
  [.mul (c kF) (c pos), .mul (c kF) (c (reg 0)),
   .mul (c kF) (c (reg 3)), .mul (c kF) (c (reg 4)),
   .mul (c kF) (sub (c NN) (.add (c (reg 1)) (smul 256 (c (reg 2))))),
   .mul (c kF) (sub (c NN) (.mul (c nn) (c nn))),
   .mul (c kF) (sub (c base) (.add (c (reg 5)) (.add (smul 256 (c (reg 6))) (smul 65536 (c (reg 7)))))),
   .mul (c kF) (sub (c fair) (.add (c (reg 8)) (.add (smul 256 (c (reg 9))) (smul 65536 (c (reg 10))))))]

theorem initial_group_eq : initialGroup=(cKind.drop 83).take 8 := by decide +kernel

theorem initial_zero (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (hn:R.n*R.n<65536) (hb:I.p.base<16777216) (hf:I.p.maxShardBandwidth/R.n<16777216)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈initialGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) (parameters I R)
        (ProcPriorCodecNativeBytes.header R) present 0)[c]!) nxt first last trans)=0 := by
  obtain ⟨h0,h3,h4,h1,h2,h5,h6,h7,h8,h9,h10⟩ := initial_registers I R present vidV
  obtain ⟨hnn,hNN,hbase,hfair⟩ := instance_fields I R present vidV (parameters I R) (ProcPriorCodecNativeBytes.header R) 0
  have hk := (ProcPriorCodecSideMultiplicity.header_flags I R present vidV
    (parameters I R) (ProcPriorCodecNativeBytes.header R) 0).2.2.2.2.1
  have hp := (ProcPriorCodecSideZero.header_cells I R present vidV
    (parameters I R) (ProcPriorCodecNativeBytes.header R) 0).2.2.2.1
  have hN := congrArg Fp.ofNat (digit2 (R.n*R.n) hn)
  have hB := congrArg Fp.ofNat (digit3 I.p.base hb)
  have hF := congrArg Fp.ofNat (digit3 (I.p.maxShardBandwidth/R.n) hf)
  simp only [cast_add,cast_mul] at hN hB hF
  intro e he
  simp only [initialGroup,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.smul,
    Bool.false_eq_true,ite_false,ite_true,hk,hp,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,hnn,hNN,hbase,hfair]
  all_goals try simp only [cast_mul,show Fp.ofNat 0=0 by rfl,show Fp.ofNat 1=1 by rfl]
  all_goals grind only

theorem inactive (cur nxt : Nat→Fp) (first last trans : Fp) (hk:cur kF=0) :
    ∀e∈initialGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  intro e he
  simp only [initialGroup,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.smul,
    Bool.false_eq_true,ite_false,hk]
  all_goals grind only

theorem header_initial (I : Input) (R : Run) (present : Bool) (vidV p : Nat)
    (hn:R.n*R.n<65536) (hb:I.p.base<16777216) (hf:I.p.maxShardBandwidth/R.n<16777216)
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈initialGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) (parameters I R)
        (ProcPriorCodecNativeBytes.header R) present p)[c]!) nxt first last trans)=0 := by
  by_cases hp:p=0
  · subst p
    exact initial_zero I R present vidV hn hb hf nxt first last trans
  · apply inactive
    rw [(ProcPriorCodecSideMultiplicity.header_flags I R present vidV
      (parameters I R) (ProcPriorCodecNativeBytes.header R) p).2.2.2.2.1,ite_eq_right (by exact hp)]
    rfl

theorem native_bounds (I : Input) (R : Run)
    (hp:NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (hn:R.n≤64) : R.n*R.n<65536 ∧ I.p.base<16777216 ∧ I.p.maxShardBandwidth/R.n<16777216 := by
  have hsq:=Nat.mul_le_mul hn hn
  have hb:=(ProcActualParameterGuard.bounds I.p I.ids.length hp).1
  have hm:I.p.maxShardBandwidth=4500000 := by rw [lp_calc hp]
  have hd:=Nat.div_le_self I.p.maxShardBandwidth R.n
  rw [hm] at hd ⊢
  omega

theorem native_initial (I : Input) (R : Run) (present : Bool) (vidV p : Nat)
    (hp:NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p)
    (hn:R.n≤64) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈initialGroup,e.evalWith (ProcPriorCells.env
      (fun c=>Fp.ofNat (headerRow (instanceCells I R present vidV) (parameters I R)
        (ProcPriorCodecNativeBytes.header R) present p)[c]!) nxt first last trans)=0 := by
  obtain ⟨hnn,hb,hf⟩:=native_bounds I R hp hn
  exact header_initial I R present vidV p hnn hb hf nxt first last trans

end ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderInitial
