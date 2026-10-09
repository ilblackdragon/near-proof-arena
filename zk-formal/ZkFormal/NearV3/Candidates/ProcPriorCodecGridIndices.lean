import ZkFormal.NearV3.Candidates.ProcPriorCodecGridCounters
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecGridIndices
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
variable {tr:Trace Fp} {t:Nat} {pub:List Fp}
set_option maxHeartbeats 1000000

theorem advance (k n:Nat) (hn:0<n) :
    (k+1)/n=k/n+(if k%n+1=n then 1 else 0) ∧
    (k+1)%n=if k%n+1=n then 0 else k%n+1 := by
  have hm:(k+1)%n=(k%n+1)%n:=by simp [Nat.add_mod]
  have hb:=Nat.mod_lt k hn
  by_cases he:k%n+1=n
  · simp only [if_pos he]
    have hz:(k+1)%n=0:=by rw [hm,he];simp
    exact ⟨Nat.succ_div_of_mod_eq_zero hz,hz⟩
  · simp only [if_neg he,Nat.add_zero]
    have hr:(k+1)%n=k%n+1:=by rw [hm,Nat.mod_eq_of_lt (by omega)]
    exact ⟨Nat.succ_div_of_mod_ne_zero (by omega),hr⟩

/-- Exact sender/receiver enumeration is forced by the actual corrected grid. -/
theorem indices (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {f n:Nat}
    (hf:f<tr.height t) (hF:cv tr t f kF=1) (hn:cv tr t f nn=n)
    (hpos:0<n) (h64:n≤64) (hNN:cv tr t f NN=n*n) :
    ∀k,k<n*n→cv tr t (f+5+24*k) srcC=k/n ∧ cv tr t (f+5+24*k) useC=k%n := by
  have hN:cv tr t f NN≤4096:=by have :=Nat.mul_le_mul h64 h64;omega
  intro k
  induction k with
  | zero =>
    intro _
    simpa using ProcPriorCodecGridCounters.initial hL hf hF
  | succ k ih =>
    intro hk
    obtain ⟨hs,hu⟩:=ih (by omega)
    obtain ⟨hb,hr,hki,hc⟩:=ProcPriorCodecGridComplete.records hL hf hF hN k (by omega)
    have hnn:cv tr t (f+5+24*k) nn=n:=(hc nn (by simp)).trans hn
    have hNNk:cv tr t (f+5+24*k) NN=n*n:=(hc NN (by simp)).trans hNN
    have hdiv:k/n<n:=(Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
    have hmod:=Nat.mod_lt k hpos
    obtain ⟨hsn,hun⟩:=ProcPriorCodecGridCounters.next hL hb hr (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rw [hs] at hsn
    simp only [hu,hnn] at hsn hun
    have he:f+5+24*k+24=f+5+24*(k+1):=by omega
    rw [he] at hsn hun
    obtain ⟨hd,hm⟩:=advance k n hpos
    exact ⟨hsn.trans hd.symm,hun.trans hm.symm⟩
end ZkFormal.NearV3.Candidates.ProcPriorCodecGridIndices
