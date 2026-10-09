import ZkFormal.NearV3.Assembly.RoutingSelection

namespace ZkFormal.NearV3.Assembly.RoutingBoundedLayout
open NearSpec NearSpecV3

def samePrefix (a b : Bytes) : Nat→Bool
  | 0=>true
  | n+1=>samePrefix a b n && (a.getD n 0==b.getD n 0)

theorem samePrefix_iff (a b : Bytes) (n : Nat) :
    samePrefix a b n=true ↔ ∀i,i<n → a.getD i 0=b.getD i 0 := by
  induction n with
  | zero => simp [samePrefix]
  | succ n ih =>
    simp only [samePrefix,Bool.and_eq_true,beq_iff_eq,ih]
    constructor
    · intro h i hi
      by_cases he : i=n
      · simpa [he] using h.2
      · exact h.1 i (by omega)
    · intro h;exact ⟨fun i hi=>h i (by omega),h n (by omega)⟩

/-- Native lower-bound ordering supplies every comparison required while the
padded prefixes agree. No sorted-layout premise enters this byte lemma. -/
theorem lexLe_prefix_lower : ∀ (i : Nat) (lo v : Bytes), i≤v.length →
    lexLe lo v=true → (∀k,k<i → lo.getD k 0=v.getD k 0) →
    (lo.getD i 0).toNat≤(v.getD i 0).toNat
  | 0,[],v,_,_,_ => by simp
  | 0,_::_,[],_,h,_ => by simp [lexLe] at h
  | 0,a::lo,b::v,_,h,_ => by
    simp only [lexLe,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at h
    simp only [List.getD_cons_zero]
    rcases h with h|⟨he,_⟩
    · exact Nat.le_of_lt (UInt8.lt_iff_toNat_lt.mp h)
    · simp [he]
  | i+1,[],v,_,_,_ => by simp
  | i+1,_::_,[],hi,_,_ => by simp at hi
  | i+1,a::lo,b::v,hi,h,he => by
    have hab := he 0 (by omega)
    simp only [List.getD_cons_zero] at hab
    subst b
    have ht : lexLe lo v=true := by simpa [lexLe] using h
    simp only [List.getD_cons_succ]
    apply lexLe_prefix_lower i lo v (by simpa using hi) ht
    intro k hk
    simpa using he (k+1) (by omega)

/-- Native strict upper-bound ordering gives weak comparisons before the end
and a strict one at the receiver's zero end marker. -/
theorem lexLe_prefix_upper : ∀ (i : Nat) (hi v : Bytes),
    (∀b∈hi,0<b.toNat) → i≤v.length → lexLe hi v=false →
    (∀k,k<i → v.getD k 0=hi.getD k 0) →
    (v.getD i 0).toNat≤(hi.getD i 0).toNat ∧
      (i=v.length → (v.getD i 0).toNat<(hi.getD i 0).toNat)
  | _,[],_,_,_,h,_ => by simp [lexLe] at h
  | 0,a::_,[],hpos,_,_,_ => by
    have h := hpos a (by simp)
    simp only [List.getD_nil,List.getD_cons_zero,List.length_nil]
    exact ⟨Nat.le_of_lt h,fun _=>h⟩
  | 0,a::hi,b::v,_,_,h,_ => by
    have ha : b.toNat≤a.toNat := by
      simp only [lexLe,Bool.or_eq_false_iff,decide_eq_false_iff_not] at h
      have hh : ¬a.toNat<b.toNat := by simpa only [UInt8.lt_iff_toNat_lt] using h.1
      omega
    exact ⟨ha,by simp⟩
  | i+1,_::_,[],_,hn,_,_ => by simp at hn
  | i+1,a::hi,b::v,hpos,hn,h,he => by
    have hab := he 0 (by omega)
    simp only [List.getD_cons_zero] at hab
    subst b
    have ht : lexLe hi v=false := by simpa [lexLe] using h
    obtain ⟨hl,hs⟩ := lexLe_prefix_upper i hi v (fun b hb=>hpos b (by simp [hb]))
      (by simpa using hn) ht (fun k hk=>by simpa using he (k+1) (by omega))
    refine ⟨hl,?_⟩
    intro he
    exact hs (by simpa using he)

end ZkFormal.NearV3.Assembly.RoutingBoundedLayout
