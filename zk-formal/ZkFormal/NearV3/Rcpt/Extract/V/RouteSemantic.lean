import ZkFormal.NearV3.Rcpt.Extract.V.RouteValues
import ZkFormal.NearV3.Rcpt.Link.Lex

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem padB_lt256 (xs : List Nat) (hb : ∀ a∈xs,a<256) (k : Nat) : padB xs k<256 := by
  induction xs generalizing k with
  | nil => simp [padB]
  | cons a as ih =>
    cases k with
    | zero => exact hb a (by simp)
    | succ k => exact ih (fun a ha => hb a (by simp [ha])) k

variable (hL : TableLocal RcptV3.table tr tt pub) {y : RS}
variable (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
include hL lay

/-- An equal lower prefix keeps the actual lower-prefix flag set. -/
theorem route_lower_prefix (lo : List Nat)
    (hr : ∀ e∈(rcptOf tr tt y).rlk,e.2.1=padB lo e.1) :
    ∀ i,i≤y.Lv → (∀ k,k<i → padB (rcptOf tr tt y).v k=padB lo k) →
      tr.cell tt (lkRow y i) eqL=1 := by
  intro i
  induction i with
  | zero => intro _ _; exact (route_start hL lay).1
  | succ i ih =>
    intro hi hp
    have he := ih (by omega) (fun k hk => hp k (by omega))
    have hg := route_gate hL lay i (by omega)
    rw [he] at hg
    have hg1 : tr.cell tt (lkRow y i) gBd=1 := by grind
    have hl := hr _ (route_record hL lay i (by omega) hg1)
    simp only at hl
    have hv := route_value hL lay i (by omega)
    have hb := (route_lower_eq hL (route_height hL lay i (by omega)) hg1).mpr (by rw [hl,hv]; exact hp i (by omega))
    have hn := (route_step hL lay i (by omega)).1
    rw [he,hb] at hn
    grind

/-- An equal upper prefix keeps its flag set when the upper bound exists. -/
theorem route_upper_prefix (hi : List Nat)
    (hr : ∀ e∈(rcptOf tr tt y).rlk,e.2.2.1=padB hi e.1 ∧ e.2.2.2.1=0) :
    ∀ i,i≤y.Lv → (∀ k,k<i → padB (rcptOf tr tt y).v k=padB hi k) →
      tr.cell tt (lkRow y i) eqH=1 := by
  intro i
  induction i with
  | zero =>
    intro _ _
    have h0 := route_start hL lay
    have hz := (hr _ (route_record hL lay 0 (by omega) h0.2.2)).2
    simp only at hz
    have hzF : tr.cell tt (lkRow y 0) hnB=0 := by
      rw [cell_eq_cast tr tt (lkRow y 0) hnB,hz]
      rfl
    rw [hzF] at h0
    grind
  | succ i ih =>
    intro hi' hp
    have he := ih (by omega) (fun k hk => hp k (by omega))
    have hg := route_gate hL lay i (by omega)
    rw [he] at hg
    have hg1 : tr.cell tt (lkRow y i) gBd=1 := by grind
    have hh := (hr _ (route_record hL lay i (by omega) hg1)).1
    simp only at hh
    have hv := route_value hL lay i (by omega)
    have hb := (route_upper_eq hL (route_height hL lay i (by omega)) hg1).mpr (by rw [hh,hv]; exact hp i (by omega))
    have hn := (route_step hL lay i (by omega)).2
    rw [he,hb] at hn
    grind

/-- The physical routing comparator proves exactly the semantic boundary interval. -/
theorem route_of : RouteOk (rcptOf tr tt y) := by
  refine ⟨route_positions hL lay,route_length hL lay,?_⟩
  intro lo hi hn hlo hhi _ _ hhn hr
  have hv := route_receiver_bytes hL lay
  have hlr : ∀ e∈(rcptOf tr tt y).rlk,e.2.1=padB lo e.1 := fun e he => (hr e he).1
  have hlen : (rcptOf tr tt y).v.length=y.Lv := colAt_len _ _ _ _ _
  have hvb : ∀ k,k≤y.Lv → cv tr tt (lkRow y k) vB<256 := by
    intro k hk
    rw [route_value hL lay k hk]
    exact padB_lt256 _ (fun a ha => (hv a ha).2) k
  constructor
  · apply lex_lo lo (rcptOf tr tt y).v hlo hv
    intro i hi' heq
    have hi0 : i≤y.Lv := by omega
    have he := route_lower_prefix hL lay lo hlr i hi0 heq
    have hg := route_gate hL lay i hi0
    rw [he] at hg
    have hg1 : tr.cell tt (lkRow y i) gBd=1 := by grind
    have hl := hlr _ (route_record hL lay i hi0 hg1)
    simp only at hl
    have hb : cv tr tt (lkRow y i) loB<256 := by rw [hl]; exact padB_lt256 _ (fun a ha => (hlo a ha).2) i
    have hc := route_lower_le hL (route_height hL lay i hi0) hg1 he (hvb i hi0) hb
    rwa [hl,route_value hL lay i hi0] at hc
  · by_cases he : hn=1
    · exact Or.inl he
    right
    have hn0 : hn=0 := by omega
    have hhr : ∀ e∈(rcptOf tr tt y).rlk,e.2.2.1=padB hi e.1 ∧ e.2.2.2.1=0 := by
      intro e he
      exact ⟨(hr e he).2.1,(hr e he).2.2.trans hn0⟩
    apply lex_hi hi (rcptOf tr tt y).v hhi hv
    intro i hi' heq
    have hi0 : i≤y.Lv := by omega
    have hep := route_upper_prefix hL lay hi hhr i hi0 heq
    have hg := route_gate hL lay i hi0
    rw [hep] at hg
    have hg1 : tr.cell tt (lkRow y i) gBd=1 := by grind
    have hh := (hhr _ (route_record hL lay i hi0 hg1)).1
    simp only at hh
    have hb : cv tr tt (lkRow y i) hiB<256 := by rw [hh]; exact padB_lt256 _ (fun a ha => (hhi a ha).2) i
    have hc := route_upper_le hL (route_height hL lay i hi0) hg1 hep (hvb i hi0) hb
    rw [hh,route_value hL lay i hi0] at hc
    refine ⟨hc,?_⟩
    intro hiEnd
    have hiLv : i=y.Lv := by omega
    have hz : tr.cell tt (lkRow y i) eH=0 := by rw [hiLv] at hep ⊢; exact route_upper_end hL lay hep
    have hne : padB (rcptOf tr tt y).v i≠padB hi i := by
      intro heq'
      have hf := (route_upper_eq hL (route_height hL lay i hi0) hg1).mpr (by rw [hh,route_value hL lay i hi0]; exact heq')
      rw [hz] at hf
      exact (by decide : (0:Fp)≠1) hf
    omega

end ZkFormal.NearV3.RcptV3Proof
