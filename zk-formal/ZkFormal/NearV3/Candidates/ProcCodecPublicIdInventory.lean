import ZkFormal.NearV3.Candidates.ProcCodecPublicIdEnumeration
namespace ZkFormal.NearV3.Candidates.ProcCodecPublicIdInventory
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen Codec
open ZkFormal.NearV3.Assembly.CodecDigest ProcCodecPublicIdEnumeration

theorem physical (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (hn : 0<R.n) (hn64 : R.n≤64) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r=>rowTraffic ProcPriorCodecActual.table.interactions
      (SchedHeight.trace out.rows codecPad) t r pub 70 true)=
      (List.range R.n).map (fun s=>ProcCodecPublicIdRecord.idMessage R.tau s (I.ids.getD s 0)) := by
  let G := fun r=>rowTraffic ProcPriorCodecActual.table.interactions (SchedHeight.trace out.rows codecPad) t r pub 70 true
  let msg := fun s=>ProcCodecPublicIdRecord.idMessage R.tau s (I.ids.getD s 0)
  have hcap:5+24*(R.n*R.n)≤2^22 := by
    have hh:=Nat.mul_le_mul hn64 hn64
    omega
  have hz : ∀r,r<5 ∨ 5+24*(R.n*R.n)≤r→G r=[] := by
    intro r hr
    dsimp only [G]
    rw [ProcCodecPublicIdPhysical.row I R present vidV gb fwd out h]
    rw [ite_eq_right (by omega)]
  have hrec : ∀k<R.n*R.n,(List.range' (5+24*k) 24).flatMap G=
      if k%R.n=0 then [msg (k/R.n)] else [] := by
    intro k hk
    apply one_record
    intro j hj
    have he:5+24*k+j=5+24*k+8*(j/8)+j%8 := by omega
    dsimp only [G]
    conv => lhs; rw [he]
    rw [ProcCodecPublicIdRecord.record I R present vidV gb fwd out h k (j/8) (j%8) hk (by omega) (by omega)]
    by_cases hj0:j=0
    · simp [hj0,msg]
    · have hneq:¬(j/8=0 ∧ j%8=0 ∧ k%R.n=0) := by omega
      simp only [ite_eq_right hneq,ite_eq_right hj0]
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
  exact sampled R.n hn msg

theorem count (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gb : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gb fwd=.ok out)
    (hn : 0<R.n) (hn64 : R.n≤64) (t : Nat) (pub msg : List Fp) :
    tableBusCount ProcPriorCodecActual.table.interactions (SchedHeight.trace out.rows codecPad)
      t pub 70 true msg=
      ((List.range R.n).map (fun s=>ProcCodecPublicIdRecord.idMessage R.tau s (I.ids.getD s 0))).count msg := by
  rw [tableBusCount_eq]
  exact congrArg (fun xs=>xs.count msg) (physical I R present vidV gb fwd out h hn hn64 t pub)
end ZkFormal.NearV3.Candidates.ProcCodecPublicIdInventory
