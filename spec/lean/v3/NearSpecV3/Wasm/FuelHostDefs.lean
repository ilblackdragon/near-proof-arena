import NearSpecV3.Wasm.Fuel
/-!
# The host-arm obligation of W02 fuel sufficiency (`HostsOK`)

`HostMono s s'`: a successful host arm keeps the call frames and `prepaid` and does not raise the
remaining gas. `HostsOK` states it for every arm `dispatchArm` selects; `Wasm/FuelHost.lean` proves
it (`hostsOK`). Both fuel-sufficiency proofs use it: the certificate-relative one
(`Wasm/FuelSufficiency.lean`) and the general one (`Wasm/FuelGeneral.lean`, through
`Wasm/FuelSuff.lean`). This module also carries the few `Keeps` facts `FuelHost` needs, so that
`FuelHost` does not depend on either proof.
-/
namespace NearSpecV3.Wasm

/-- Host functions keep the call frames and never give gas back. -/
def HostMono (s s' : St) : Prop :=
  s'.frames = s.frames ∧ s'.gas.remaining ≤ s.gas.remaining ∧ s'.gas.prepaid = s.gas.prepaid

def HostsOK : Prop := ∀ (s : St) (name : String) (h : HM Unit) (u : Unit) (s' : St),
  dispatchArm s name = some h → h.run s = .ok u s' → HostMono s s'

/-- `s'` has the frames and the gas of `s`. -/
def Keeps (s s' : St) : Prop := s'.frames = s.frames ∧ s'.gas = s.gas

theorem Keeps.refl (s : St) : Keeps s s := ⟨rfl, rfl⟩
theorem Keeps.trans {a b c : St} (h1 : Keeps a b) (h2 : Keeps b c) : Keeps a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem keeps_popV (s : St) : Keeps s (popV s).2 := ⟨rfl, rfl⟩
theorem keeps_popN (s : St) : Keeps s (popN s).2 := by
  unfold popN; split <;> rename_i h <;> rw [← (Prod.ext_iff.mp h).2] <;> exact keeps_popV s

theorem list_loop'_keeps2 : ∀ (l : List Nat) (body : (i : Nat) → i ∈ l → St → Id (ForInStep St))
    (_ : ∀ i h s, ∃ t, body i h s = .yield t ∧ Keeps s t) (s : St), Keeps s (Id.run (forIn' l s body))
  | [], _, _, s => Keeps.refl s
  | x :: xs, body, hb, s => by
    simp only [List.forIn'_cons]
    obtain ⟨t, ht, hk⟩ := hb x (List.mem_cons_self) s
    rw [ht]
    exact hk.trans (list_loop'_keeps2 xs _ (fun i h t => hb i _ t) _)

theorem keeps_writeBytes (s : St) (a : Nat) (d : ByteArray) : Keeps s (writeBytes s a d) := by
  unfold writeBytes
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply list_loop'_keeps2
  intro i h t
  exact ⟨_, rfl, rfl, rfl⟩

end NearSpecV3.Wasm
