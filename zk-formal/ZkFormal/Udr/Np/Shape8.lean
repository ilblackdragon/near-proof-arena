import ZkFormal.Udr.Np.Msg4

/-!
# ZkFormal.Udr.Np.Shape8 — a shaped transcript at `E = 8`

Its entries are exactly: header + main oracle, `α_fp`, `[]`, `γ`,
aux oracle + finals, `α_c`, quotient oracle, `z`.
-/

namespace ZkFormal.Udr.Np

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra

/-- The oracle fits the matrix shapes `ms`. -/
def OFits (o : Oracle Fp) (ms : List (Nat × Nat)) : Prop :=
  o.length = ms.length ∧ ∀ k (hk : k < o.length), ∃ sh, ms[k]? = some sh ∧
    o[k].log = sh.1 ∧ o[k].width = sh.2 ∧ ∀ i, i < 2 ^ o[k].log → (o[k].row i).length = o[k].width

structure Shape8 (A : Air) (prm : Params) (τ : PTn) where
  l : List Nat
  o0 : Oracle Fp
  o1 : Oracle Fp
  o2 : Oracle Fp
  fins : List Fp8
  c1 : Fp8
  c3 : Fp8
  c5 : Fp8
  c7 : Fp8
  hl : τ.header? = some l
  hh : headerOk A prm l = true
  hent : τ.entries = [.msg [.header l, .oracle o0], .chal c1, .msg [], .chal c3,
    .msg [.oracle o1, .elems fins], .chal c5, .msg [.oracle o2], .chal c7]
  hf0 : OFits o0 ((layout A prm l).map fun L => (L.lde, L.width))
  hfins : fins.length = ((layout A prm l).map fun L => L.sendG + L.recvG).sum

theorem sched_odd (A : Air) (prm : Params) (l : List Nat) :
    (schedule A prm l)[1]? = some (.chal false) ∧ (schedule A prm l)[3]? = some (.chal false) ∧
    (schedule A prm l)[5]? = some (.chal false) ∧ (schedule A prm l)[7]? = some (.chal true) ∧
    (schedule A prm l)[8]? = some (.msg [.elems ((layout A prm l).map fun L =>
      2 * L.width + 2 * L.aux + L.quot).sum]) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem shape8 {A : Air} {prm : Params} {τ : PTn} (hs : Shaped (Vnp A prm) τ)
    (hE : τ.entries.length = 8) : Nonempty (Shape8 A prm τ) := by
  have hne : τ.entries ≠ [] := fun h => by rw [h] at hE; simp at hE
  obtain ⟨l, hl, hh, _⟩ := shaped_hdr hs hne
  have F := fun k (hk : k < 8) => shaped_fits hs hl k (by omega)
  obtain ⟨s0, h01, h02⟩ := F 0 (by omega)
  rw [(sched_get l).1] at h01; cases h01
  obtain ⟨a, b, he0, ha, hb⟩ := fits_two h02
  obtain ⟨o0, rfl⟩ := fits_oracle hb
  obtain ⟨l', rfl⟩ := fits_header ha
  obtain ⟨s2, h21, h22⟩ := F 2 (by omega)
  rw [(sched_get l).2.1] at h21; cases h21
  have he2 := fits_nil h22
  obtain ⟨s4, h41, h42⟩ := F 4 (by omega)
  rw [(sched_get l).2.2.1] at h41; cases h41
  obtain ⟨a4, b4, he4, ha4, hb4⟩ := fits_two h42
  obtain ⟨o1, rfl⟩ := fits_oracle ha4
  obtain ⟨fins, rfl, hfl⟩ := fits_elems hb4
  obtain ⟨s6, h61, h62⟩ := F 6 (by omega)
  rw [(sched_get l).2.2.2.1] at h61; cases h61
  obtain ⟨a6, he6, ha6⟩ := fits_one h62
  obtain ⟨o2, rfl⟩ := fits_oracle ha6
  obtain ⟨s1, h11, h12⟩ := F 1 (by omega)
  rw [(sched_odd A prm l).1] at h11; cases h11
  obtain ⟨c1, he1⟩ := fits_chal h12
  obtain ⟨s3, h31, h32⟩ := F 3 (by omega)
  rw [(sched_odd A prm l).2.1] at h31; cases h31
  obtain ⟨c3, he3⟩ := fits_chal h32
  obtain ⟨s5, h51, h52⟩ := F 5 (by omega)
  rw [(sched_odd A prm l).2.2.1] at h51; cases h51
  obtain ⟨c5, he5⟩ := fits_chal h52
  obtain ⟨s7, h71, h72⟩ := F 7 (by omega)
  rw [(sched_odd A prm l).2.2.2.1] at h71; cases h71
  obtain ⟨c7, he7⟩ := fits_chal h72
  match hes : τ.entries, hE with
  | [e0, e1, e2, e3, e4, e5, e6, e7], _ =>
    simp only [hes, List.getElem_cons_zero, List.getElem_cons_succ] at he0 he1 he2 he3 he4 he5 he6 he7
    subst he0 he1 he2 he3 he4 he5 he6 he7
    have hl' : l' = l := by
      have : τ.header? = some l' := by unfold PT.header?; rw [hes]
      rw [hl] at this; cases this; rfl
    subst hl'
    exact ⟨⟨l', o0, o1, o2, fins, c1, c3, c5, c7, hl, hh, by rw [hes], hb, hfl⟩⟩

end ZkFormal.Udr.Np
