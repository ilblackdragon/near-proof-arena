import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Padded

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra DedupPartitionTable

def variableCells (sa sb sc : Nat) (A B C D : Nat → Nat → Fp) : Nat → Nat → Fp :=
  prefixCells sa A (prefixCells sb B (prefixCells sc C D))

theorem variable_steps {sa sb sc sd : Nat} (haPos : 0<sa) (hbPos : 0<sb) (hcPos : 0<sc)
    (A B C D : Nat → Nat → Fp) (pub : Nat → Fp)
    (ha : ∀ r, r<sa → SourceRow (A r) (A (r+1)) (if r=0 then 1 else 0) 0 1 pub)
    (hb : ∀ r, r<sb → SourceRow (B r) (B (r+1)) 0 0 1 pub)
    (hc : ∀ r, r<sc → SourceRow (C r) (C (r+1)) 0 0 1 pub)
    (hd : ∀ r, r<sd → SourceRow (D r) (D (r+1)) 0 0 1 pub)
    (hab : ∀ x, x<57 → A sa x=B 0 x)
    (hbc : ∀ x, x<57 → B sb x=C 0 x)
    (hcd : ∀ x, x<57 → C sc x=D 0 x) :
    ∀ r, r<sa+sb+sc+sd → SourceRow (variableCells sa sb sc A B C D r)
      (variableCells sa sb sc A B C D (r+1)) (if r=0 then 1 else 0) 0 1 pub := by
  have hcd' := prefix_steps hcPos C D 0 pub (by simpa using hc) hd hcd
  have hbc' := prefix_steps hbPos B (prefixCells sc C D) 0 pub
    (by simpa using hb) (by simpa using hcd') (by
      intro x hx
      rw [prefix_before sc C D hcPos]
      exact hbc x hx)
  have hab' := prefix_steps haPos A (prefixCells sb B (prefixCells sc C D)) 1 pub
    ha (by simpa using hbc') (by
      intro x hx
      rw [prefix_before sb B (prefixCells sc C D) hbPos]
      exact hab x hx)
  intro r hr
  exact hab' r (by omega)

theorem variable_terminal (sa sb sc sd : Nat) (A B C D : Nat → Nat → Fp) :
    variableCells sa sb sc A B C D (sa+sb+sc+sd)=D sd := by
  unfold variableCells
  rw [show sa+sb+sc+sd=sa+(sb+(sc+sd)) by omega,prefix_after,prefix_after,prefix_after]

/-- Pad any finite source row sequence by cloning its authenticated inactive
terminal row. The logical height need not match any physical table height. -/
def terminalPad (n : Nat) (cells : Nat → Nat → Fp) (r : Nat) : Nat → Fp :=
  cells (min r n)

theorem terminalPad_constraints {n H : Nat} (hn : 0<n) (hH : n<H)
    (cells : Nat → Nat → Fp) (next : Nat → Fp) (pub : Nat → Fp)
    (hsteps : ∀ r, r<n → SourceRow (cells r) (cells (r+1)) (if r=0 then 1 else 0) 0 1 pub)
    (hfinal : SourceRow (cells n) next 0 1 0 pub) (hi : Inactive (cells n)) :
    ∀ r, r<H → SourceRow (terminalPad n cells r) (terminalPad n cells ((r+1)%H))
      (if r=0 then 1 else 0) (if r+1=H then 1 else 0) (if r+1=H then 0 else 1) pub := by
  intro r hr
  by_cases hpre : r<n
  · have hm : (r+1)%H=r+1 := Nat.mod_eq_of_lt (by omega)
    simp only [show r+1≠H by omega,ite_false,hm,terminalPad,
      Nat.min_eq_left (show r≤n by omega),Nat.min_eq_left (show r+1≤n by omega)]
    exact hsteps r hpre
  · have hz : r≠0 := by omega
    simp only [terminalPad,Nat.min_eq_right (show n≤r by omega),hz,ite_false]
    by_cases hlast : r+1=H
    · simp only [hlast,ite_true,Nat.mod_self,Nat.zero_min]
      intro e he
      rw [inactive_terminal_retarget _ _ next hi 1 1 pub e he]
      exact hfinal e he
    · simp only [hlast,ite_false,Nat.mod_eq_of_lt (show r+1<H by omega),
        Nat.min_eq_right (show n≤r+1 by omega)]
      intro e he
      rw [inactive_self_step _ next hi 1 pub e he]
      exact hfinal e he

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
