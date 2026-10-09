import ZkFormal.NearV3.Assembly.RcptCandidateRoutePrefix
-- Source RouteCompare.lean SHA256: 409503e919d3416e5aa34217a33624acb18324808038f66b54100e8aeb745f02.
-- Candidate-local proof migration; no original TableLocal conclusion assumed.
import ZkFormal.NearV3.Rcpt.Extract.V.RoutePrefix

namespace ZkFormal.NearV3.Assembly.ReceiptCandidateProof
open ZkFormal.NearV3.RcptV3Proof ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal receiptArithmeticCandidate tr tt pub)
include hL

/-- The active lower-bound equality bit is equivalent to actual field equality. -/
theorem route_lower_eq {q : Nat} (hq : q<tr.height tt) (hg : tr.cell tt q gBd=1) :
    tr.cell tt q eL=1 ↔ cv tr tt q vB=cv tr tt q loB := by
  have ci := con hL hq (e:=.mul (c gBd) (sub (.mul (sub (c vB) (c loB)) (c iL)) (Dsl.not (c eL)))) (mem_ro (by simp [cRoute]))
  have cz := con hL hq (e:=mul3 (c gBd) (c eL) (sub (c vB) (c loB))) (mem_ro (by simp [cRoute]))
  simp only [eval_mul,eval_mul3,eval_sub,eval_not,eval_c,hg] at ci cz
  constructor
  · intro he
    rw [he] at cz
    have hz : tr.cell tt q vB=tr.cell tt q loB := by grind
    simp [cv,hz]
  · intro he
    have hz : tr.cell tt q vB=tr.cell tt q loB := by rw [cell_eq_cast tr tt q vB,cell_eq_cast tr tt q loB,he]
    rw [hz] at ci
    grind

/-- The active upper-bound equality bit is equivalent to actual field equality. -/
theorem route_upper_eq {q : Nat} (hq : q<tr.height tt) (hg : tr.cell tt q gBd=1) :
    tr.cell tt q eH=1 ↔ cv tr tt q vB=cv tr tt q hiB := by
  have ci := con hL hq (e:=.mul (c gBd) (sub (.mul (sub (c hiB) (c vB)) (c iH)) (Dsl.not (c eH)))) (mem_ro (by simp [cRoute]))
  have cz := con hL hq (e:=mul3 (c gBd) (c eH) (sub (c hiB) (c vB))) (mem_ro (by simp [cRoute]))
  simp only [eval_mul,eval_mul3,eval_sub,eval_not,eval_c,hg] at ci cz
  constructor
  · intro he
    rw [he] at cz
    have hz : tr.cell tt q vB=tr.cell tt q hiB := by grind
    simp [cv,hz]
  · intro he
    have hz : tr.cell tt q vB=tr.cell tt q hiB := by rw [cell_eq_cast tr tt q vB,cell_eq_cast tr tt q hiB,he]
    rw [hz] at ci
    grind

/-- The lower-prefix constraint is a natural unsigned-byte comparison, without field wrap. -/
theorem route_lower_le {q : Nat} (hq : q<tr.height tt) (hg : tr.cell tt q gBd=1)
    (hp : tr.cell tt q eqL=1) (hv : cv tr tt q vB<256) (hl : cv tr tt q loB<256) :
    cv tr tt q loB≤cv tr tt q vB := by
  have cb := con hL hq (e:=.mul (c gBd) (sub (bitsX 20 9) (.add (sub (c vB) (c loB)) (k 255)))) (mem_ro (by simp [cRoute]))
  have cs := con hL hq (e:=.mul (mul3 (c gBd) (c eqL) (Dsl.not (c (xb 28)))) (Dsl.not (c eL))) (mem_ro (by simp [cRoute]))
  obtain ⟨be,bl⟩ := bitsX_eval hL hq 20 9 (by omega)
  simp only [eval_mul,eval_mul3,eval_sub,eval_add,eval_k,eval_c,eval_not,hg,hp] at cb cs
  rw [be,cell_eq_cast tr tt q vB,cell_eq_cast tr tt q loB] at cb
  have hn : bitsVal (fun j => cv tr tt q (xb j)) 20 9+cv tr tt q loB=cv tr tt q vB+255 := by
    apply ofNat_inj (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add]
    grind
  rcases isBool hL hq (x:=eL) (by simp [boolCols]) with he|he
  · rw [he] at cs
    have hb : tr.cell tt q (xb 28)=1 := by grind
    have hbN : cv tr tt q (xb 28)=1 := by simp [cv,hb,Fp.toNat_one]
    have hlo : 256≤bitsVal (fun j => cv tr tt q (xb j)) 20 9 := by
      change 256≤bitsVal (fun j => cv tr tt q (xb j)) 20 8+256*cv tr tt q (xb 28)
      rw [hbN]
      omega
    omega
  · have hh := (route_lower_eq hL hq hg).mp he
    omega

/-- The upper-prefix constraint is a natural unsigned-byte comparison, without field wrap. -/
theorem route_upper_le {q : Nat} (hq : q<tr.height tt) (hg : tr.cell tt q gBd=1)
    (hp : tr.cell tt q eqH=1) (hv : cv tr tt q vB<256) (hh : cv tr tt q hiB<256) :
    cv tr tt q vB≤cv tr tt q hiB := by
  have cb := con hL hq (e:=.mul (c gBd) (sub (bitsX 29 9) (.add (sub (c hiB) (c vB)) (k 255)))) (mem_ro (by simp [cRoute]))
  have cs := con hL hq (e:=.mul (mul3 (c gBd) (c eqH) (Dsl.not (c (xb 37)))) (Dsl.not (c eH))) (mem_ro (by simp [cRoute]))
  obtain ⟨be,bl⟩ := bitsX_eval hL hq 29 9 (by omega)
  simp only [eval_mul,eval_mul3,eval_sub,eval_add,eval_k,eval_c,eval_not,hg,hp] at cb cs
  rw [be,cell_eq_cast tr tt q vB,cell_eq_cast tr tt q hiB] at cb
  have hn : bitsVal (fun j => cv tr tt q (xb j)) 29 9+cv tr tt q vB=cv tr tt q hiB+255 := by
    apply ofNat_inj (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add]
    grind
  rcases isBool hL hq (x:=eH) (by simp [boolCols]) with he|he
  · rw [he] at cs
    have hb : tr.cell tt q (xb 37)=1 := by grind
    have hbN : cv tr tt q (xb 37)=1 := by simp [cv,hb,Fp.toNat_one]
    have hlo : 256≤bitsVal (fun j => cv tr tt q (xb j)) 29 9 := by
      change 256≤bitsVal (fun j => cv tr tt q (xb j)) 29 8+256*cv tr tt q (xb 37)
      rw [hbN]
      omega
    omega
  · have hh := (route_upper_eq hL hq hg).mp he
    omega

end ZkFormal.NearV3.Assembly.ReceiptCandidateProof
