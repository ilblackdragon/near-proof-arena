import ZkFormal.Size.Aligned

/-! Header construction for the v3 arity-8 schedule, with a maximum trace log of 22.
These lemmas establish height arithmetic and FRI alignment. Each table's render
must separately prove its constraints and traffic at the selected height. -/
namespace ZkFormal.Size
open ZkFormal.Stark ZkFormal.Air ZkFormal.V2.SizeSched

/-- Round a required log upward to one of 1, 4, 7, …, 22. -/
def padLog22 (l : Nat) : Nat := 22 - 3 * ((22 - l) / 3)

theorem padLog22_bounds (l : Nat) (h : 1 ≤ l ∧ l ≤ 22) :
    l ≤ padLog22 l ∧ padLog22 l ≤ 22 ∧ padLog22 l % 3 = 1 := by
  unfold padLog22
  omega

/-- Rounding does not exceed a cap that already has the target residue. -/
theorem padLog22_le (l cap : Nat) (hl : l ≤ cap) (hc : cap ≤ 22) (hr : cap % 3 = 1) :
    padLog22 l ≤ cap := by
  unfold padLog22
  omega

theorem padLog22_idem (l : Nat) (h : 1 ≤ l ∧ l ≤ 22) :
    padLog22 (padLog22 l) = padLog22 l := by
  have := padLog22_bounds l h
  unfold padLog22
  omega

/-- Common trace-log residue makes every roll-in a regular arity-8 boundary.
The maximum query height is derived from the actual layout, not assumed 26. -/
theorem rollAligned_of_header_mod3 (A : Air) (prm : Params) (hdr : List Nat)
    (hm : prm.maxArityLog = 3) (hh : ∀ l ∈ hdr, l % 3 = 1) :
    RollAligned A prm hdr := by
  have hres : ∀ L ∈ layout A prm hdr, L.lde % 3 = (1 + prm.logBlowup) % 3 := by
    intro L hL
    simp only [layout, List.mem_map] at hL
    obtain ⟨⟨T, l⟩, hp, rfl⟩ := hL
    have hl := hh l (List.of_mem_zip hp).2
    dsimp only
    omega
  apply rollAligned_of_layout
  intro L hL
  rcases foldr_max_mem ((layout A prm hdr).map (·.lde)) with hz | hmax
  · change queryLog A prm hdr = 0 at hz
    rw [hz, Nat.zero_sub]
    exact Nat.dvd_zero _
  · obtain ⟨Lmax, hmemb, he⟩ := List.mem_map.mp hmax
    change Lmax.lde = queryLog A prm hdr at he
    have h1 := hres L hL
    have h2 := hres Lmax hmemb
    rw [he] at h2
    rw [hm]
    change 3 ∣ queryLog A prm hdr - L.lde
    apply Nat.dvd_of_mod_eq_zero
    omega

def padHeader22 (hdr : List Nat) : List Nat := hdr.map padLog22

theorem padHeader22_aligned (A : Air) (prm : Params) (hdr : List Nat)
    (hm : prm.maxArityLog = 3) (hh : ∀ l ∈ hdr, 1 ≤ l ∧ l ≤ 22) :
    RollAligned A prm (padHeader22 hdr) := by
  apply rollAligned_of_header_mod3 A prm _ hm
  intro l hl
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
  exact (padLog22_bounds k (hh k hk)).2.2

/-- Assembly-facing criterion on each generated table's actual log height. -/
theorem rollAligned_of_trace_mod3 (A : Air) (prm : Params) (tr : Trace Algebra.Fp)
    (hm : prm.maxArityLog = 3) (ht : ∀ t, t < A.tables.length → tr.log t % 3 = 1) :
    RollAligned A prm (Prover.trHdr A tr) := by
  apply rollAligned_of_header_mod3 A prm _ hm
  intro l hl
  obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hl
  exact ht t (List.mem_range.mp ht')

end ZkFormal.Size
