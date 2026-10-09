import ZkFormal.NearV3.Candidates.ProcConvertedFacts
namespace ZkFormal.NearV3.Candidates.ProcSenderPotential
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen

def phi (m n : Nat) (a : Array Nat) : Nat :=
  ((List.range n).map (fun i=>a[i]!/m)).sum

theorem grant_phi (m n : Nat) (a : Array Nat) (ha : a.size=n) (s inc : Nat)
    (hs : s<n) (hm : 0<m) (hi : m≤inc) (ok : Bool)
    (hok : ok=true → inc≤a[s]!) :
    phi m n (a.set! s (if ok then a[s]!-inc else a[s]!)) + (if ok then 1 else 0)≤phi m n a := by
  cases ok with
  | false =>
    simp only [Bool.false_eq_true,ite_false,Nat.add_zero]
    apply sum_range_le
    intro i _
    simp only [getElem!_set!_eq]
    split
    · next h => rw [←h.1]; exact Nat.le_refl _
    · exact Nat.le_refl _
  | true =>
    simp only [ite_true]
    refine sum_range_lt _ _ ?_ n hs ?_
    · rw [Array.getElem!_set!_self a s (a[s]!-inc) (by omega)]
      have hd := div_sub_lt hm hi (hok rfl)
      omega
    · intro i _
      simp only [getElem!_set!_eq]
      split
      · next h => rw [←h.1]; exact Nat.div_le_div_right (Nat.sub_le _ _)
      · exact Nat.le_refl _

theorem push_charge (ok rest : Bool) :
    (if ok && rest then (1 : Nat) else 0)≤(if ok then 1 else 0) := by
  cases ok <;> cases rest <;> decide

theorem grant_push_phi (m n : Nat) (a : Array Nat) (ha : a.size=n) (s inc : Nat)
    (hs : s<n) (hm : 0<m) (hi : m≤inc) (ok rest : Bool)
    (hok : ok=true → inc≤a[s]!) (pushes : Nat) :
    phi m n (a.set! s (if ok then a[s]!-inc else a[s]!)) +
      (pushes+(if ok && rest then 1 else 0))≤phi m n a+pushes := by
  have hg := grant_phi m n a ha s inc hs hm hi ok hok
  have hp := push_charge ok rest
  omega

theorem initial_bound (n m : Nat) (p : NearSpecV3.Scheduler.Params)
    (allowed : Array Bool) (a0 : Array Nat) :
    phi m n (linkPass n p allowed a0).sb≤n*(p.maxShardBandwidth/m) := by
  apply sum_range_const
  intro s _
  apply Nat.div_le_div_right
  simp only [linkPass,getElem!_def,Array.getElem?_map]
  split
  · next h =>
    simp only [Option.map_eq_some_iff] at h
    rcases h with ⟨c,hc,rfl⟩
    exact Nat.sub_le _ _
  · exact Nat.zero_le _

theorem initial_pv86 (I : Input)
    (hp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length=some I.p) :
    phi ((I.p.maxSingleGrant-I.p.base)/40) I.ids.length
      (linkPass I.ids.length I.p I.allowed (a0Src I.ids I.prev)).sb≤43*I.ids.length := by
  have hh := initial_bound I.ids.length ((I.p.maxSingleGrant-I.p.base)/40) I.p I.allowed (a0Src I.ids I.prev)
  have hk := (pv86_kappa hp).2
  have hm := Nat.mul_le_mul_left I.ids.length hk
  rw [Nat.mul_comm I.ids.length 43] at hm
  exact Nat.le_trans hh hm
theorem count_phi (m n : Nat) (a : Array Nat) (ha : a.size=n) (s inc : Nat)
    (hs : s<n) (hm : 0<m) (hi : m≤inc) (ok : Bool)
    (hok : ok=true → inc≤a[s]!) (before after : Nat)
    (hc : after≤before+(if ok then 1 else 0)) :
    phi m n (a.set! s (if ok then a[s]!-inc else a[s]!))+after≤phi m n a+before := by
  have hg := grant_phi m n a ha s inc hs hm hi ok hok
  omega
end ZkFormal.NearV3.Candidates.ProcSenderPotential
