import ZkFormal.NearV3.Candidates.ProcPriorRawFrame
namespace ZkFormal.NearV3.Candidates.ProcPriorRawSlots

inductive Slot where
  | header (offset : Nat)
  | record (index offset : Nat)
  | hash (offset : Nat)
  | padding
  deriving DecidableEq, Repr

def length (n : Nat) : Nat:=37+24*n
def slot (n i : Nat) : Slot:=
  if i<5 then .header i else if i<5+24*n then .record ((i-5)/24) ((i-5)%24)
  else if i<length n then .hash (i-(5+24*n)) else .padding

theorem header (n g : Nat) (h:g<5) : slot n g=.header g := by simp [slot,h]

theorem record (n j g : Nat) (hj:j<n) (hg:g<24) : slot n (5+24*j+g)=.record j g := by
  have h0:¬5+24*j+g<5:=by omega
  have hn:5+24*j+g<5+24*n:=by omega
  have hd:(5+24*j+g-5)/24=j:=by omega
  have hm:(5+24*j+g-5)%24=g:=by omega
  simp [slot,h0,hn,hd,hm]

theorem hash (n g : Nat) (h:g<32) : slot n (5+24*n+g)=.hash g := by
  have h0:¬5+24*n+g<5:=by omega
  have hn:¬5+24*n+g<5+24*n:=by omega
  have hl:5+24*n+g<length n:=by unfold length; omega
  simp [slot,h0,hn,hl]

theorem padding (n i : Nat) (h:length n≤i) : slot n i=.padding := by
  have h0:¬i<5:=by unfold length at h; omega
  have hn:¬i<5+24*n:=by unfold length at h; omega
  simp [slot,h0,hn,show ¬i<length n by omega]

theorem coverage (n i : Nat) (h:i<length n) :
    (∃g,g<5 ∧ i=g ∧ slot n i=.header g) ∨
    (∃j g,j<n ∧ g<24 ∧ i=5+24*j+g ∧ slot n i=.record j g) ∨
    (∃g,g<32 ∧ i=5+24*n+g ∧ slot n i=.hash g) := by
  by_cases h0:i<5
  · exact Or.inl ⟨i,h0,rfl,header n i h0⟩
  · right
    by_cases hn:i<5+24*n
    · left
      have hj:(i-5)/24<n:=by omega
      have hg:(i-5)%24<24:=by omega
      have he:i=5+24*((i-5)/24)+(i-5)%24:=by omega
      exact ⟨(i-5)/24,(i-5)%24,hj,hg,he,(congrArg (slot n) he).trans (record n _ _ hj hg)⟩
    · right
      have hg:i-(5+24*n)<32:=by unfold length at h; omega
      have he:i=5+24*n+(i-(5+24*n)):=by omega
      exact ⟨i-(5+24*n),hg,he,(congrArg (slot n) he).trans (hash n _ hg)⟩

theorem header_next (n g : Nat) (h:g<4) : slot n (g+1)=.header (g+1) := header n _ (by omega)

theorem header_end (n : Nat) : slot n 5=if n=0 then .hash 0 else .record 0 0 := by
  by_cases h:n=0
  · subst n; exact hash 0 0 (by decide +kernel)
  · rw [ite_eq_right h]
    exact record n 0 0 (by omega) (by decide +kernel)

theorem record_next (n j g : Nat) (hj:j<n) (hg:g<23) :
    slot n (5+24*j+g+1)=.record j (g+1) := by
  rw [show 5+24*j+g+1=5+24*j+(g+1) by omega]
  exact record n j _ hj (by omega)

theorem record_end (n j : Nat) (hj:j<n) :
    slot n (5+24*j+23+1)=if j+1=n then .hash 0 else .record (j+1) 0 := by
  by_cases h:j+1=n
  · rw [ite_eq_left h,show 5+24*j+23+1=5+24*n+0 by omega]
    exact hash n 0 (by decide +kernel)
  · rw [ite_eq_right h,show 5+24*j+23+1=5+24*(j+1)+0 by omega]
    exact record n (j+1) 0 (by omega) (by decide +kernel)

theorem hash_next (n g : Nat) (hg:g<31) : slot n (5+24*n+g+1)=.hash (g+1) := by
  rw [show 5+24*n+g+1=5+24*n+(g+1) by omega]
  exact hash n _ (by omega)

theorem hash_end (n : Nat) : slot n (5+24*n+31+1)=.padding := padding n _ (by unfold length; omega)

end ZkFormal.NearV3.Candidates.ProcPriorRawSlots
