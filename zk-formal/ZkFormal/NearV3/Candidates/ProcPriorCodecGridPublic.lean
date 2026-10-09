import ZkFormal.NearV3.Candidates.ProcPriorCodecGridIndices
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGridPublic
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
variable {tr:Trace Fp} {t:Nat} {pub:List Fp}

/-- Every layout index has a live physical public-ID send. Repeated IDs remain separate indices. -/
theorem sender (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {f n j:Nat}
    (hf:f<tr.height t) (hF:cv tr t f kF=1) (hn:cv tr t f nn=n)
    (hpos:0<n) (h64:n≤64) (hNN:cv tr t f NN=n*n) (hj:j<n) :
    ∃r,r<tr.height t ∧ cv tr t r rs=1 ∧ cv tr t r nzb=1 ∧
      cv tr t r srcC=j ∧ cv tr t r tau=cv tr t f tau ∧
      ProcPriorCodecActual.publicId.multNat tr t r pub=1 := by
  have hkn:j*n<n*n:=Nat.mul_lt_mul_of_pos_right hj hpos
  have hN:cv tr t f NN≤4096:=by have :=Nat.mul_le_mul h64 h64;omega
  obtain ⟨hb,hs,hki,hc⟩:=ProcPriorCodecGridComplete.records hL hf hF hN (j*n) (by omega)
  obtain ⟨hsrc,huse⟩:=ProcPriorCodecGridIndices.indices hL hf hF hn hpos h64 hNN (j*n) hkn
  have hsj:cv tr t (f+5+24*(j*n)) srcC=j:=by simpa [Nat.mul_div_cancel j hpos] using hsrc
  have hu0:cv tr t (f+5+24*(j*n)) useC=0:=by simpa using huse
  have hz:=ProcPriorCodecGridCounters.zero_receiver hL hb hs hu0
  refine ⟨f+5+24*(j*n),hb,hs,hz,hsj,hc tau (by simp),?_⟩
  have hsr:tr.cell t (f+5+24*(j*n)) rs=(1:Fp):=by
    rw [←Fp.ofNat_toNat (tr.cell t (f+5+24*(j*n)) rs)]
    change Fp.ofNat (cv tr t (f+5+24*(j*n)) rs)=1
    rw [hs];rfl
  have hzr:tr.cell t (f+5+24*(j*n)) nzb=(1:Fp):=by
    rw [←Fp.ofNat_toNat (tr.cell t (f+5+24*(j*n)) nzb)]
    change Fp.ofNat (cv tr t (f+5+24*(j*n)) nzb)=1
    rw [hz];rfl
  simp [ProcPriorCodecActual.publicId,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,c,hsr,hzr]
  rfl
end ZkFormal.NearV3.Candidates.ProcPriorCodecGridPublic
