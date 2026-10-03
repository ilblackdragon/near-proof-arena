import ReexecNpai.Spec.RecAux30

/-!
# Record parse: the push after a record body, and the record start
-/

set_option maxRecDepth 8000

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

section
variable {pub cb pb : Bytes} {rs : List Receipt} {R N o : Nat} {A : List Ent} {K S : List Nat} {m m1 : M}

theorem RecStart.mk' (h : ParseInv cb pb rs R N o A K S m) (hlt : o < pb.length) (hcap : A.length < NCAP)
    (hm : m1.mem = m.mem) (h10 : m1.regs 10 = PF + o + 1) (h0 : m1.regs 0 = (m.mem (PF + o)).toNat)
    (fr : ∀ j, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 10 → j ≠ 13 → m1.regs j = m.regs j) :
    RecStart cb pb rs R N o A K S m m1 :=
  ⟨h, hlt, hcap, hm, h10, by rw [h0]; exact byteProof h.st.proof hlt, fr⟩

theorem RecStart.mono (hs : RecStart cb pb rs R N o A K S m m1) {m' : M} (hm : m'.mem = m1.mem)
    (hr : ∀ j, j ≠ 1 → j ≠ 2 → m'.regs j = m1.regs j) : RecStart cb pb rs R N o A K S m m' :=
  ⟨hs.inv, hs.olt, hs.cap, by rw [hm, hs.mem], by rw [hr 10 (by omega) (by omega), hs.r10],
    by rw [hr 0 (by omega) (by omega), hs.r0],
    fun j h0 h1 h2 h10 h13 => by rw [hr j h1 h2, hs.fr j h0 h1 h2 h10 h13]⟩

/-- The post-state of `pRecord; LTU 4 10 9`. -/
def RecPost (cb pb : Bytes) (rs : List Receipt) (R N o : Nat) (A : List Ent) (m' : M) : Prop :=
  ∃ o' A' K' S', ParseInv cb pb rs R N o' A' K' S' m' ∧ A'.length = A.length + 1 ∧ o < o' ∧
    m'.regs 4 = (if o' < pb.length then 1 else 0)

def RecPostT (cb pb : Bytes) (rs : List Receipt) (R N o' : Nat) (A : List Ent) (m' : M) : Prop :=
  ∃ A' K' S', ParseInv cb pb rs R N o' A' K' S' m' ∧ A'.length = A.length + 1 ∧
    m'.regs 4 = (if o' < pb.length then 1 else 0)

theorem push_core {o' : Nat} {A' : List Ent} {K' S0 : List Nat} {m2 : M}
    (hpre : PreInv cb pb rs R N o' A' K' S0 m2) :
    twp P (Inp pub cb pb) (.seq pPush (LTU 4 10 9)) m2 (fun m' c =>
      ParseInv cb pb rs R N o' A' K' (S0 ++ [A'.length - 1]) m' ∧
      m'.regs 4 = (if o' < pb.length then 1 else 0) ∧ c = 17) := by
  have hcap := hpre.cap
  have hkl := hpre.klen
  have hre := hpre.re
  simp only [NCAP] at hcap
  refine twp_mono (pPush_exe hpre.st.k1 hpre.st.k8 hpre.rsp (e := A'.length - 1) (by omega)
    (by simp only [NCAP]; omega) (by simp only [NCAP]; omega)) ?_
  rintro m' c ⟨hm, h7, h8, h4, hr, hc⟩
  refine ⟨preInv_push hpre hm h7 (by rw [h8]; omega) hr, ?_, hc⟩
  rw [h4, hpre.rP, hpre.rE]
  by_cases h : o' < pb.length
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem push_wp {m2 : M} (hb : BodyPost cb pb rs R N o A m2) {Q : M → Prop}
    (hQ : ∀ m4, RecPost cb pb rs R N o A m4 → Q m4) :
    wp P (Inp pub cb pb) pPush m2 (fun m3 => wp P (Inp pub cb pb) (LTU 4 10 9) m3 Q) := by
  obtain ⟨o', A', K', S0, hpre, hlen, hoo⟩ := hb
  rw [← wp_seq]
  exact wp_of_spec (push_core hpre) (fun m' c ⟨hp, h4, _⟩ => hQ m' ⟨o', A', K', _, hp, hlen, hoo, h4⟩)

theorem push_twp {m2 : M} {o' X : Nat} (hb : BodyPostT cb pb rs R N o o' A m2 X) {Q : M → Nat → Prop}
    (hQ : ∀ m4, X + 40 ≤ 80 * (o' - o) → RecPostT cb pb rs R N o' A m4 → Q m4 17) :
    twp P (Inp pub cb pb) pPush m2 (fun m3 c3 => twp P (Inp pub cb pb) (LTU 4 10 9) m3 (fun m4 c4 => Q m4 (c3 + c4))) := by
  obtain ⟨A', K', S0, hpre, hlen, hoo, hX⟩ := hb
  have := push_core (pub := pub) hpre
  rw [twp_seq] at this
  refine twp_mono this ?_
  intro m3 c3 h3
  refine twp_mono h3 ?_
  rintro m4 c4 ⟨hp, h4, hc⟩
  rw [hc]
  exact hQ m4 hX ⟨A', K', _, hp, hlen, h4⟩

end

end ReexecNpai
