import ZkFormal.NearV3.Candidates.ProcPriorCodecNativeBytes
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderInactive
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ProcPriorCodecAssignments ProcPriorCodecNativeHash

open ZkFormal.Chacha.Table.E in
def headerGroup : List Expr :=
[
    .mul (c kF) (c pos),
    .mul (c kF) (c (reg 0)), .mul (c kF) (c (reg 3)), .mul (c kF) (c (reg 4)),
    .mul (c kF) (sub (c NN) (.add (c (reg 1)) (smul 256 (c (reg 2))))),
    .mul (c kF) (sub (c NN) (.mul (c nn) (c nn))),
    .mul (c kF) (sub (c base) (.add (c (reg 5)) (.add (smul 256 (c (reg 6))) (smul 65536 (c (reg 7)))))),
    .mul (c kF) (sub (c fair) (.add (c (reg 8)) (.add (smul 256 (c (reg 9))) (smul 65536 (c (reg 10)))))),
    .mul (c kH) (sub (c bpost) (c (reg 0))),
    .mul (c kH) (sub (c bpre) (.mul (c pres) (c bpost))),
    mul3 (c kH) (notE (c ehp)) (notE (n kH)) ] ++
  (List.range 31).map (fun i => mul3 (c kH) (notE (c ehp)) (sub (n (reg i)) (c (reg (i + 1))))) ++
  [ -- header → first record
    .mul (c ehp) (notE (n fS)), .mul (c ehp) (n kidx), .mul (c ehp) (n g), .mul (c ehp) (notE (n rs)) ]

theorem header_group_eq : headerGroup=cKind.drop 83 := by decide +kernel

theorem header_group_size : headerGroup.length=46 := by decide +kernel

theorem header_group_retained :
    headerGroup.filter (fun x=> !ProcPriorCodecActual.retiredKind.contains x)=headerGroup := by decide +kernel

theorem inactive (cur nxt : Nat→Fp) (first last trans : Fp)
    (hF:cur kF=0) (hH:cur kH=0) (hE:cur ehp=0) :
    ∀e∈headerGroup,e.evalWith (ProcPriorCells.env cur nxt first last trans)=0 := by
  intro e he
  simp only [headerGroup,List.mem_append] at he
  rcases he with (h|h)|h
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,
      notE,mul3,Bool.false_eq_true,ite_false,ite_true,hF,hH,hE]
    all_goals grind only
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,
      notE,mul3,Bool.false_eq_true,ite_false,ite_true,hH,hE]
    grind only
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    all_goals simp only [Expr.evalWith,ProcPriorCells.env,ZkFormal.Chacha.Table.E.c,
      ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.sub,
      notE,Bool.false_eq_true,ite_false,ite_true,hE]
    all_goals grind only

theorem hash_header (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (digest hpre : List Nat) (base0 j : Nat) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈headerGroup,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat (hashRow (instanceCells I R present vidV) digest hpre present base0 j)[c]!) nxt first last trans)=0 := by
  obtain ⟨hz,hH,hZ,hA,hF,hD⟩ := ProcPriorCodecSideMultiplicity.hash_flags I R present vidV digest hpre base0 j
  have he:=(ProcPriorCodecSideZero.hash_cells I R present vidV digest hpre base0 j).1 ehp (by simp)
  apply inactive
  · rw [hF]; rfl
  · rw [hH]; rfl
  · rw [he]; rfl

theorem ash_header (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (base0 j : Nat) (nxt : Nat→Fp) (first last trans : Fp) :
    ∀e∈headerGroup,e.evalWith (ProcPriorCells.env (fun c=>Fp.ofNat (ashRow (instanceCells I R present vidV) I base0 j)[c]!) nxt first last trans)=0 := by
  obtain ⟨hz,hH,hZ,hA,hF,hD⟩ := ProcPriorCodecSideMultiplicity.ash_flags I R present vidV base0 j
  have he:=(ProcPriorCodecSideZero.ash_cells I R present vidV base0 j).1 ehp (by simp)
  apply inactive
  · rw [hF]; rfl
  · rw [hH]; rfl
  · rw [he]; rfl

end ZkFormal.NearV3.Candidates.ProcPriorCodecHeaderInactive
