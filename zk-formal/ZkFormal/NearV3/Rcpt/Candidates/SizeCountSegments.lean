import ZkFormal.NearV3.Rcpt.Candidates.SizeCountPrefix

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Near

private theorem prefix_zero_span (mark : Nat → Bool) (s n : Nat)
    (h : ∀ r,s≤r → r<s+n → mark r=false) : recordPrefix mark (s+n)=recordPrefix mark s := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := ih (fun r hr hl => h r hr (by omega))
    rw [show s+(n+1)=(s+n)+1 by omega,recordPrefix,h (s+n) (by omega) (by omega)]
    simpa using hh

theorem prefix_one_segment (mark : Nat → Bool) (s n : Nat) (hn : 0<n)
    (h : ∀ r,s<r → r<s+n → mark r=false) :
    recordPrefix mark (s+n)=recordPrefix mark s+(if mark s then 1 else 0) := by
  have hh := prefix_zero_span mark (s+1) (n-1) (fun r hr hl => h r (by omega) (by omega))
  rw [show s+1+(n-1)=s+n by omega,recordPrefix] at hh
  exact hh

/-- Complete consecutive segmentation converts physical prefix counts into the
EXACT filtered view length; only first-row flags are used. -/
theorem prefix_segments (mark : Nat → Bool) (keep : Nat×Nat → Bool)
    (segs : List (Nat×Nat)) (s : Nat) (hc : Consec s segs)
    (h : ∀ p∈segs,0<p.2 ∧ mark p.1=keep p ∧
      ∀ r,p.1<r → r<p.1+p.2 → mark r=false) :
    recordPrefix mark (segEnd s segs)=recordPrefix mark s+(segs.filter keep).length := by
  induction segs generalizing s with
  | nil => simp [segEnd]
  | cons p ps ih =>
    rcases p with ⟨a,n⟩
    obtain ⟨rfl,hc⟩ := hc
    obtain ⟨hn,hm,hzero⟩ := h (a,n) (by simp)
    have ht := ih (a+n) hc (fun p hp => h p (by simp [hp]))
    have hs := prefix_one_segment mark a n hn hzero
    rw [hm] at hs
    simp only [segEnd]
    rw [ht,hs]
    cases hk : keep (a,n) <;> simp [hk] <;> omega

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
