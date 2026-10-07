import ZkFormal.NearV3.Qv.Extract.ParserFacts

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable {s n : Nat} (hfit : s+n≤tr.height tt)
variable (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
variable (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
include hL hfit hw hs

private theorem last_zero (r : Nat) (hr : s≤r) (hb : r+1<s+n) : tr.cell tt r vl=0 := by
  have hz := hs.2.2.2.2.2 r hr hb
  rcases isBool hL (show r<tr.height tt by omega) (hw r hr (by omega)) (x:=vl)
      (by simp) with he | he
  · exact he
  · simp [isOne,he] at hz

theorem position : ∀ r, s≤r → r<s+n → tr.cell tt r pos=((r-s:Nat):Fp) := by
  have hp := hs.1
  have hf : tr.cell tt s vf=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.1
  have hh := con hL (show s<tr.height tt by omega) (hw s (by omega) (by omega))
    (e:=.mul (c vf) (c pos)) (by simp [constraints])
  simp only [eval_mul,eval_c,hf] at hh
  have hz : tr.cell tt s pos=(0:Nat) := by grind
  have hstep : ∀ r, s≤r → r+1<s+n → tr.cell tt (r+1) pos=tr.cell tt r pos+1 := by
    intro r hr hb
    have ha : tr.cell tt r act=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 r hr (by omega)
    exact (inside_next hL (by omega) (hw r hr (by omega)) (by omega) ha (last_zero hL hfit hw hs r hr hb)).2.2
  simpa only [Nat.zero_add] using counter_of (f:=fun r => tr.cell tt r pos) (ℓ:=n) hz hstep

theorem metadata {x : Nat} (hx : x∈[vid,len,users,tau,count,mEmpty,mBuffer,mRaw]) :
    ∀ r, s≤r → r<s+n → tr.cell tt r x=tr.cell tt s x := by
  apply const_of (f:=fun r => tr.cell tt r x)
  intro r hr hb
  have ha : tr.cell tt r act=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 r hr (by omega)
  exact inside_metadata hL (by omega) (hw r hr (by omega)) (by omega) ha
    (last_zero hL hfit hw hs r hr hb) hx

/-- A zero-length marker is the complete record, not a byte inside a longer one. -/
theorem empty_length (r : Nat) (hr : s≤r) (hb : r<s+n) (hz : tr.cell tt r vz=1) :
    n=1 ∧ cv tr tt s len=0 := by
  have hmarker := empty_marker hL (show r<tr.height tt by omega) (hw r hr hb) hz
  have hstart : r=s := by
    by_cases he : r=s
    · exact he
    · have hh := hs.2.2.2.2.1 r (by omega) hb
      simp [isOne,hmarker.2.1] at hh
  have hend : r+1=s+n := by
    by_cases he : r+1=s+n
    · exact he
    · have hh := hs.2.2.2.2.2 r hr (by omega)
      simp [isOne,hmarker.2.2.1] at hh
  refine ⟨by omega,?_⟩
  subst r
  simp only [cv,hmarker.2.2.2.1,Fp.toNat_zero]

theorem nonempty_length (hz : tr.cell tt (s+n-1) vz=0) : cv tr tt s len=n := by
  have hp := hs.1
  have hr : s+n-1<tr.height tt := by omega
  have hl : tr.cell tt (s+n-1) vl=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.1
  have hh := con hL hr (hw _ (by omega) (by omega))
    (e:=mul3 (c vl) (Dsl.not (c vz)) (sub (c len) (.add (c pos) (k 1)))) (by simp [constraints])
  have hpos := position hL hfit hw hs (s+n-1) (by omega) (by omega)
  have hm := metadata hL hfit hw hs (x:=len) (by simp) (s+n-1) (by omega) (by omega)
  simp only [eval_mul3,eval_not,eval_sub,eval_add,eval_c,eval_k,hl,hz,hpos,hm] at hh
  have he : tr.cell tt s len=(n:Fp) := by
    have hn : n=(s+n-1-s)+1 := by omega
    rw [hn,natCast_add]
    grind
  have hbound := height_le hL
  have hn : n<P := by unfold P; omega
  simp only [cv,he,toNat_natCast,Nat.mod_eq_of_lt hn]

theorem length_cases : (n=1 ∧ cv tr tt s len=0) ∨ cv tr tt s len=n := by
  have hp := hs.1
  have hr : s+n-1<tr.height tt := by omega
  rcases isBool hL hr (hw _ (by omega) (by omega)) (x:=vz) (by simp) with hz | hz
  · exact Or.inr (nonempty_length hL hfit hw hs hz)
  · exact Or.inl (empty_length hL hfit hw hs (s+n-1) (by omega) (by omega) hz)

end ZkFormal.NearV3.Qv.Extract.Parser
