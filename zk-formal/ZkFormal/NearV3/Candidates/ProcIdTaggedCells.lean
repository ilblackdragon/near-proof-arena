import ZkFormal.NearV3.Candidates.ProcNativeIdBalance
import ZkFormal.NearV3.Candidates.ProcPriorIdLocal
namespace ZkFormal.NearV3.Candidates.ProcIdTaggedCells
open ZkFormal.Algebra ProcPriorIdRows

abbrev Tagged := Nat × Row

def top (a : Tagged) : Nat := 65536*a.1+ProcPriorIdLimbs.hi a.2.event.key

def cross (a b : Tagged) : Nat→Fp :=
  let base:=ProcPriorIdCells.cells a.2 (some b.2) a.1
  fun c=>if c=10 ∨ c=16 ∨ c=17 ∨ c=18 ∨ c=19 then 0
    else if c=13 then (Fp.ofNat (top b)-Fp.ofNat (top a))⁻¹ else base c

def cells (a : Tagged) (next : Option Tagged) : Nat→Fp :=
  match next with
  | none=>ProcPriorIdCells.cells a.2 none a.1
  | some b=>if a.1=b.1 then ProcPriorIdCells.cells a.2 (some b.2) a.1 else cross a b

theorem data (a : Tagged) (next : Option Tagged) (c : Nat) (hc:c<10) :
    cells a next c=ProcPriorIdCells.cells a.2 (next.map Prod.snd) a.1 c := by
  cases next with
  | none=>rfl
  | some b=>
    simp only [cells,Option.map_some]
    split
    · rfl
    · simp only [cross]
      rw [ite_eq_right (by omega),ite_eq_right (by omega)]

theorem data_next (a : Row) (b c : Option Row) (tau col : Nat) (hc:col<10) :
    ProcPriorIdCells.cells a b tau col=ProcPriorIdCells.cells a c tau col := by
  have hd:col=0∨col=1∨col=2∨col=3∨col=4∨col=5∨col=6∨col=7∨col=8∨col=9:=by omega
  rcases hd with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem top_bound (a : Tagged) (ht:a.1<32) (hk:a.2.event.key<2^64) : top a<P := by
  have h:ProcPriorIdLimbs.hi a.2.event.key<65536:=(ProcPriorIdLimbs.bounds _ hk).2.2
  unfold top P
  omega

theorem top_lt (a b : Tagged) (ht:a.1<b.1) (hk:a.2.event.key<2^64) : top a<top b := by
  have h:ProcPriorIdLimbs.hi a.2.event.key<65536:=(ProcPriorIdLimbs.bounds _ hk).2.2
  unfold top
  omega
end ZkFormal.NearV3.Candidates.ProcIdTaggedCells
