import ZkFormal.NearV3.Candidates.ProcPriorCodecEndRows
import ZkFormal.NearV3.Candidates.ProcPriorCodecTerminalValue
import ZkFormal.NearV3.Candidates.ProcPriorCodecAllowanceData
import ZkFormal.NearV3.Candidates.ProcActualRunProjection
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecEndLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec NearSpecV3.Scheduler
open ProcPriorCodecRecordStep ProcPriorCodecNativeHash ProcPriorCodecEndArithmetic

/-- The native record-end debit, allowance, and high-byte equations, with
subtraction and serialized-value bounds derived from the prepared native run. -/
theorem native (sp : SchedPub) (hs : SchedPubOk sp)
    (prev : NearSpec.Bandwidth.State) (tauV : Nat) (R : Run)
    (hr : ActualRun.run (ProcPreparedSequence.input sp prev) tauV=.ok R)
    (present : Bool) (gb : Array Nat) (fwd : List (Nat×Nat)) (vidV k : Nat)
    (rows : Array (Array Nat)) (cmps : List (Nat×Nat×Nat)) (mid out : State)
    (hi : k<sp.ids.length*sp.ids.length)
    (hp : forIn (List.range 7) (rows,cmps,0,0,0,0)
      (fun g s=>step (ProcPreparedSequence.input sp prev) R present gb fwd
        (instanceCells (ProcPreparedSequence.input sp prev) R present vidV) k 2 g s)=.ok mid)
    (ht : step (ProcPreparedSequence.input sp prev) R present gb fwd
      (instanceCells (ProcPreparedSequence.input sp prev) R present vidV) k 2 7 mid=.ok (.yield out))
    (nxt : Nat→Fp) (first last trans : Fp) :
    ∃a,out.1=mid.1.push a ∧ ∀e∈(cRec.drop 54).take 1 ++ (cRec.drop 56).take 3,e.evalWith
      (ProcPriorCells.env (fun c=>Fp.ofNat a[c]!) nxt first last trans)=0 := by
  let I := ProcPreparedSequence.input sp prev
  have hn : R.n=I.ids.length := (ProcActualRunProjection.run_fields I tauV R hr).2.1
  have hk : k<R.n*R.n := by simpa [hn,I,ProcPreparedSequence.input] using hi
  obtain ⟨a,har,ha1,ha2,hg2,hafin,hal,hbase,hrend,hbf⟩ := ProcPriorCodecEndRows.cells I R present gb fwd vidV k mid out hk ht
  obtain ⟨a',ha'r,_,hapost,hbig⟩ := ProcPriorCodecTerminalValue.native sp hs prev tauV R hr present gb fwd
    (instanceCells I R present vidV) k rows cmps mid out hk hi hp ht
  have he : a'=a := Array.push_inj_right.mp (ha'r.symm.trans har)
  subst a'
  obtain ⟨a',ha'r,_,hnzb,_⟩ := ProcPriorCodecAllowanceData.cells I R present gb fwd
    (instanceCells I R present vidV) k 7 mid out (by decide) hk ht
  have he : a'=a := Array.push_inj_right.mp (ha'r.symm.trans har)
  subst a'
  obtain ⟨a',ha'r,_,_,hmidbig⟩ := ProcPriorCodecAccumulatorRows.cells I R present gb fwd
    (instanceCells I R present vidV) k 7 mid out (by decide) ht
  have he : a'=a := Array.push_inj_right.mp (ha'r.symm.trans har)
  subst a'
  have hb0 : a[bF]! =0 := by rw [hbf]; simp [←hmidbig,hbig]
  have hdebit : Fp.ofNat a[a2]! =Fp.ofNat a[a1]! -Fp.ofNat a[al]!*Fp.ofNat a[base]! := by
    rw [ha2,ha1,hal,hbase]
    exact debit_field I R present k mid.2.2.2.2.2 hn hs.n1 hs.params
  have hgfield : Fp.ofNat a[g2]! =Fp.ofNat a[al]!*Fp.ofNat a[base]! := by
    rw [hg2,hal,hbase,cast_mul]
  have hv : Fp.ofNat a[apost]! =Fp.ofNat a[afin]! := by rw [hapost,hafin]
  refine ⟨a,har,?_⟩
  simp only [cRec,List.map_cons,List.map_nil,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,
    List.mem_cons,List.mem_nil_iff,or_false]
  intro e heq
  rcases heq with rfl|rfl|rfl|rfl
  all_goals simp only [mul3,notE,ZkFormal.Chacha.Table.E.sub,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.n,ZkFormal.Chacha.Table.E.k,Expr.evalWith,ProcPriorCells.env,
    hdebit,hgfield,hv,hb0,hbig,hnzb,show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl]
  all_goals grind only
end ZkFormal.NearV3.Candidates.ProcPriorCodecEndLocal
