import ZkFormal.NearV3.Rcpt.Candidates.SourceLog22Extract

namespace ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra DedupPartitionTable

/-- The prefix owns its first n rows; its carried row is owned by the suffix. -/
def prefixCells (n : Nat) (A B : Nat → Nat → Fp) (r : Nat) : Nat → Fp :=
  if r<n then A r else B (r-n)

theorem prefix_before (n : Nat) (A B : Nat → Nat → Fp) {r : Nat} (h : r<n) :
    prefixCells n A B r=A r := by simp [prefixCells,h]

theorem prefix_after (n q : Nat) (A B : Nat → Nat → Fp) :
    prefixCells n A B (n+q)=B q := by
  simp [prefixCells,show ¬n+q<n by omega]

theorem prefix_successor {n r : Nat} (hr : r<n) (A B : Nat → Nat → Fp)
    (hc : ∀ x, x<57 → A n x=B 0 x) :
    ∀ x, x<57 → prefixCells n A B (r+1) x=A (r+1) x := by
  intro x hx
  by_cases hn : r+1<n
  · rw [prefix_before n A B hn]
  · have he : r+1=n := by omega
    rw [he]
    simpa [prefixCells] using (hc x hx).symm

/-- Splicing authenticated rows preserves every original field equation.
The suffix has no global-first row, regardless of its physical table origin. -/
theorem prefix_steps {n m : Nat} (hn : 0<n) (A B : Nat → Nat → Fp)
    (first : Fp) (pub : Nat → Fp)
    (ha : ∀ r, r<n → SourceRow (A r) (A (r+1)) (if r=0 then first else 0) 0 1 pub)
    (hb : ∀ r, r<m → SourceRow (B r) (B (r+1)) 0 0 1 pub)
    (hc : ∀ x, x<57 → A n x=B 0 x) :
    ∀ r, r<n+m → SourceRow (prefixCells n A B r) (prefixCells n A B (r+1))
      (if r=0 then first else 0) 0 1 pub := by
  intro r hr
  by_cases hpre : r<n
  · intro e he
    rw [cellEnv_congr e (base_constraint_width e he)
      (C':=A r) (D':=A (r+1))
      (fun x _ => congrFun (prefix_before n A B hpre) x)
      (prefix_successor hpre A B hc)]
    exact ha r hpre e he
  · have hz : r≠0 := by omega
    have he : r=n+(r-n) := by omega
    have hq : r-n<m := by omega
    simp only [hz,ite_false]
    rw [he,Nat.add_assoc,prefix_after,prefix_after]
    exact hb (r-n) hq

def fourCells (s : Nat) (A B C D : Nat → Nat → Fp) : Nat → Nat → Fp :=
  prefixCells s A (prefixCells s B (prefixCells s C D))

/-- Three distinct authenticated overlaps reconstruct one ordered source trace.
No honest cell values or integer lifting is used in this soundness step. -/
theorem four_steps {s : Nat} (hs : 0<s) (A B C D : Nat → Nat → Fp) (pub : Nat → Fp)
    (ha : ∀ r, r<s → SourceRow (A r) (A (r+1)) (if r=0 then 1 else 0) 0 1 pub)
    (hb : ∀ r, r<s → SourceRow (B r) (B (r+1)) 0 0 1 pub)
    (hc : ∀ r, r<s → SourceRow (C r) (C (r+1)) 0 0 1 pub)
    (hd : ∀ r, r<s → SourceRow (D r) (D (r+1)) 0 0 1 pub)
    (hab : ∀ x, x<57 → A s x=B 0 x)
    (hbc : ∀ x, x<57 → B s x=C 0 x)
    (hcd : ∀ x, x<57 → C s x=D 0 x) :
    ∀ r, r<4*s → SourceRow (fourCells s A B C D r)
      (fourCells s A B C D (r+1)) (if r=0 then 1 else 0) 0 1 pub := by
  have hcd' := prefix_steps hs C D 0 pub (by simpa using hc) hd hcd
  have hbc' := prefix_steps hs B (prefixCells s C D) 0 pub
    (by simpa using hb) (by simpa using hcd') (by
      intro x hx
      rw [prefix_before s C D hs]
      exact hbc x hx)
  have hab' := prefix_steps hs A (prefixCells s B (prefixCells s C D)) 1 pub
    ha (by simpa using hbc') (by
      intro x hx
      rw [prefix_before s B (prefixCells s C D) hs]
      exact hab x hx)
  intro r hr
  exact hab' r (by omega)

end ZkFormal.NearV3.Rcpt.Candidates.SourceLog22
