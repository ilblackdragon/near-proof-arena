/-!
# ZkFormal.NearV3.Sched.Spec.MemCons — offline memory consistency for time-ordered segments

Abstract form of what the memory table gives the link layer. Ops `(a, t, vin, vout)` on
addresses; per address the ops have distinct times, and each op reads the value written by the
op on its address with the largest earlier time (or the initial value `v0 a`): **`chained`**.
A simulation `σ t a` (value of address `a` before time `t`) changes an address only at the
times of its ops (**frame**), and each time step is **correct**: if every op at time `t` reads
`σ t`, every such op writes `σ (t+1)`. Then every op reads the simulation (`mem_consistent`).
-/

namespace ZkFormal.NearV3.Sched

structure MOp where
  a : Nat
  t : Nat
  vin : Nat
  vout : Nat
  deriving DecidableEq, Repr

section
variable (ops : List MOp) (v0 : Nat → Nat) (σ : Nat → Nat → Nat)

/-- Each op reads the latest earlier op of its address (or the initial value). -/
def Chained : Prop :=
  ∀ o ∈ ops,
    (∃ o' ∈ ops, o'.a = o.a ∧ o'.t < o.t ∧ (∀ o'' ∈ ops, o''.a = o.a → o''.t < o.t → o''.t ≤ o'.t) ∧
      o.vin = o'.vout) ∨
    ((∀ o'' ∈ ops, o''.a = o.a → ¬ o''.t < o.t) ∧ o.vin = v0 o.a)

/-- An address changes only at the times of its ops. -/
def Frame : Prop := ∀ t a, (∀ o ∈ ops, ¬ (o.a = a ∧ o.t = t)) → σ (t + 1) a = σ t a

/-- Each time step is correct on its ops. -/
def StepOk : Prop :=
  ∀ t, (∀ o ∈ ops, o.t = t → o.vin = σ t o.a) → ∀ o ∈ ops, o.t = t → o.vout = σ (t + 1) o.a

theorem frame_iter (hF : Frame ops σ) (a : Nat) :
    ∀ d s, (∀ o ∈ ops, o.a = a → ¬ (s ≤ o.t ∧ o.t < s + d)) → σ (s + d) a = σ s a
  | 0, _, _ => rfl
  | d + 1, s, h => by
    have ih := frame_iter hF a d s (fun o ho hoa ⟨h1, h2⟩ => h o ho hoa ⟨h1, by omega⟩)
    rw [show s + (d + 1) = s + d + 1 by omega, hF (s + d) a (fun o ho ⟨hoa, hot⟩ =>
      h o ho hoa ⟨by omega, by omega⟩), ih]

/-- **Memory consistency.** -/
theorem mem_consistent (hC : Chained ops v0) (hF : Frame ops σ) (hS : StepOk ops σ)
    (h0 : ∀ a, σ 0 a = v0 a) : ∀ o ∈ ops, o.vin = σ o.t o.a := by
  have key : ∀ T, ∀ o ∈ ops, o.t < T → o.vin = σ o.t o.a := by
    intro T
    induction T with
    | zero => intro o _ h; omega
    | succ T ih =>
      intro o ho hoT
      rcases Nat.lt_or_ge o.t T with hlt | hge
      · exact ih o ho hlt
      have hT : o.t = T := by omega
      rcases hC o ho with ⟨o', ho', ha', ht', hmax, hv⟩ | ⟨hnone, hv⟩
      · -- the predecessor's step was correct
        have hstep := hS o'.t (fun o2 ho2 h2 => by rw [← h2]; exact ih o2 ho2 (by omega)) o' ho' rfl
        rw [hv, hstep, ← ha']
        have := frame_iter ops σ hF o'.a (o.t - (o'.t + 1)) (o'.t + 1) (fun o2 ho2 ha2 ⟨h1, h2⟩ => by
          have := hmax o2 ho2 (by rw [ha2, ha']) (by omega)
          omega)
        rw [show o'.t + 1 + (o.t - (o'.t + 1)) = o.t by omega] at this
        exact this.symm
      · rw [hv, ← h0]
        have := frame_iter ops σ hF o.a o.t 0 (fun o2 ho2 ha2 ⟨_, h2⟩ => hnone o2 ho2 ha2 (by omega))
        rw [Nat.zero_add] at this
        exact this.symm
  intro o ho
  exact key (o.t + 1) o ho (by omega)

end

end ZkFormal.NearV3.Sched
