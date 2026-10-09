import ZkFormal.NearV3.Candidates.ProcCodecPublicIdEnumeration
import ZkFormal.NearV3.Candidates.ProcCodecPriorReadPhysical
namespace ZkFormal.NearV3.Candidates.ProcCodecPriorReadInventory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecPublicIdEnumeration

theorem at_eighteen {α : Type} (base : Nat) (G : Nat→List α) (a : List α)
    (h : ∀j<24,G (base+j)=if j=18 then a else []) :
    (List.range' base 24).flatMap G=a := by
  have he : List.range' base 24=List.range' base 18++List.range' (base+18) 6 := by
    rw [List.range'_append_1]
  rw [he,List.flatMap_append]
  have hz : (List.range' base 18).flatMap G=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    have hh:=List.mem_range'.mp hr
    have he:r=base+(r-base):=by omega
    rw [he,h (r-base) (by omega),if_neg (by omega)]
  rw [hz,List.nil_append,List.range'_succ,List.flatMap_cons,h 18 (by decide),if_pos rfl]
  have hz : (List.range' (base+18+1) 5).flatMap G=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    have hh:=List.mem_range'.mp hr
    have he:r=base+(r-base):=by omega
    rw [he,h (r-base) (by omega),if_neg (by omega)]
  rw [hz,List.append_nil]

theorem physical (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (hn : 0<R.n) (hn64 : R.n≤64) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActual.table.interactions
      (SchedHeight.trace out.rows codecPad) t r pub 68 false)=
      (List.range (R.n*R.n)).map (fun k=>ProcCodecPriorReadRecord.message R.tau k (ProcCodecPriorReadCells.prior I present k)) := by
  let G := fun r=>rowTraffic ProcPriorCodecActual.table.interactions (SchedHeight.trace out.rows codecPad) t r pub 68 false
  let msg := fun k=>ProcCodecPriorReadRecord.message R.tau k (ProcCodecPriorReadCells.prior I present k)
  have hcap:5+24*(R.n*R.n)≤2^22 := by
    have hh:=Nat.mul_le_mul hn64 hn64
    omega
  have hz : ∀r,r<5 ∨ 5+24*(R.n*R.n)≤r→G r=[] := by
    intro r hr
    dsimp only [G]
    rw [ProcCodecPriorReadPhysical.row I R present vidV gb fwd out h]
    rw [ite_eq_right (by omega)]
  have hrec : ∀k<R.n*R.n,(List.range' (5+24*k) 24).flatMap G=
      [msg k] := by
    intro k hk
    apply at_eighteen
    intro j hj
    have he:5+24*k+j=5+24*k+8*(j/8)+j%8 := by omega
    dsimp only [G]
    conv => lhs; rw [he]
    rw [ProcCodecPriorReadRecord.record I R present vidV gb fwd out h k (j/8) (j%8) hk (by omega) (by omega)]
    by_cases hj18:j=18
    · simp [hj18,msg]
    · have hneq:¬(j/8=2 ∧ j%8=2) := by omega
      simp only [ite_eq_right hneq,ite_eq_right hj18]
  have hp : (List.range' 0 5).flatMap G=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    exact hz r (Or.inl (by have hh:=List.mem_range'.mp hr; omega))
  have ht : (List.range' (5+24*(R.n*R.n)) (2^22-(5+24*(R.n*R.n)))).flatMap G=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    exact hz r (Or.inr (by have hh:=List.mem_range'.mp hr; omega))
  have hsplit : List.range (2^22)=List.range' 0 5++List.range' 5 (24*(R.n*R.n))++
      List.range' (5+24*(R.n*R.n)) (2^22-(5+24*(R.n*R.n))) := by
    rw [List.append_assoc,List.range'_append_1,List.range'_append_1,List.range_eq_range']
    congr 1
    omega
  change (List.range (2^22)).flatMap G=_
  rw [hsplit,List.flatMap_append,List.flatMap_append,hp,ht,List.nil_append,List.append_nil,
    blocks,flat_congr _ _ _ (fun k hk=>hrec k (List.mem_range.mp hk))]
  have hm : ∀xs : List Nat,xs.flatMap (fun k=>[msg k])=xs.map msg := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih]
  exact hm _

theorem count (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (hn : 0<R.n) (hn64 : R.n≤64) (t : Nat) (pub msg : List Fp) :
    tableBusCount ProcPriorCodecActual.table.interactions (SchedHeight.trace out.rows codecPad)
      t pub 68 false msg=
      ((List.range (R.n*R.n)).map (fun k=>ProcCodecPriorReadRecord.message R.tau k (ProcCodecPriorReadCells.prior I present k))).count msg := by
  rw [tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (physical I R present vidV gb fwd out h hn hn64 t pub)
end ZkFormal.NearV3.Candidates.ProcCodecPriorReadInventory
