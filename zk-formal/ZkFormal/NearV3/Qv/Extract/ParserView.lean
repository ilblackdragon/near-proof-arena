import ZkFormal.NearV3.Qv.Extract.ParserSegments

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

/-- Parser records in physical row coordinates after the queue-walk prefix. -/
structure ParserChain (tr : Trace Fp) (tt start : Nat) where
  segs : List (Nat × Nat)
  consecutive : Consec start segs
  fits : segEnd start segs≤tr.height tt
  valid : ∀ p∈segs, IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) p.1 p.2
  suffix : ∀ r, segEnd start segs≤r → r<tr.height tt → isOne tr tt act r=false

private theorem shift_consec (l : List (Nat × Nat)) (off s : Nat) (hc : Consec s l) :
    Consec (off+s) (l.map (fun p => (off+p.1,p.2))) := by
  induction l generalizing s with
  | nil => trivial
  | cons p rest ih =>
    obtain ⟨hp,hrest⟩ := hc
    refine ⟨by simp [hp],?_⟩
    simpa only [Nat.add_assoc] using ih (s+p.2) hrest

private theorem shift_end (l : List (Nat × Nat)) (off s : Nat) :
    segEnd (off+s) (l.map (fun p => (off+p.1,p.2)))=off+segEnd s l := by
  induction l generalizing s with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.map_cons,segEnd]
    rw [Nat.add_assoc,ih]

private theorem shift_valid {tr : Trace Fp} {tt : Nat} (off s n : Nat)
    (hs : IsSeg (fun r => isOne tr tt act (off+r)) (fun r => isOne tr tt vf (off+r))
      (fun r => isOne tr tt vl (off+r)) s n) :
    IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) (off+s) n := by
  have hp := hs.1
  refine ⟨hp,hs.2.1,?_,?_,?_,?_⟩
  · have he : off+s+n-1=off+(s+n-1) := by omega
    rw [he]
    exact hs.2.2.1
  · intro r hr hb
    have he : off+(r-off)=r := by omega
    simpa only [he] using hs.2.2.2.1 (r-off) (by omega) (by omega)
  · intro r hr hb
    have he : off+(r-off)=r := by omega
    simpa only [he] using hs.2.2.2.2.1 (r-off) (by omega) (by omega)
  · intro r hr hb
    have he : off+(r-off)=r := by omega
    simpa only [he] using hs.2.2.2.2.2 (r-off) (by omega) (by omega)

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}

theorem parser_chain_exists (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
    (q : WalkChain tr tt) : Nonempty (ParserChain tr tt (segEnd 0 q.segs)) := by
  let S := segEnd 0 q.segs
  have hfit : S≤tr.height tt := q.fits
  by_cases hr : S<tr.height tt
  · have hw := zero_of_false hL hr (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix S (Nat.le_refl _) hr)
    rcases Parser.isBool hL hr hw (x:=act) (by simp) with hz | ha
    · refine ⟨⟨[],trivial,hfit,by simp,?_⟩⟩
      intro r hstart hb
      change S≤r at hstart
      have hh := parser_suffix_inactive hL q hz (r-S) (by change S+(r-S)<tr.height tt; omega)
      have he : S+(r-S)=r := by omega
      change tr.cell tt (S+(r-S)) act=0 at hh
      rw [he] at hh
      simp [isOne,hh]
    · obtain ⟨l,hc,hb,hv,hpad⟩ := parser_suffix_segments hL q ha hr
      have hc' := shift_consec l S 0 hc
      have he := shift_end l S 0
      simp only [Nat.add_zero] at hc' he
      refine ⟨⟨l.map (fun p => (S+p.1,p.2)),hc',?_,?_,?_⟩⟩
      · rw [he]
        change segEnd 0 l≤tr.height tt-S at hb
        omega
      · intro p hp
        obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
        exact shift_valid S a.1 a.2 (hv a ha)
      · intro r hstart hrow
        rw [he] at hstart
        have hh := hpad (r-S) (by omega) (by change r-S<tr.height tt-S; omega)
        have he' : S+(r-S)=r := by omega
        change isOne tr tt act (S+(r-S))=false at hh
        simpa only [he'] using hh
  · refine ⟨⟨[],trivial,hfit,by simp,?_⟩⟩
    intro r hstart hb
    change S≤r at hstart
    omega

theorem parser_chain_lengths (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
    (q : WalkChain tr tt) (v : ParserChain tr tt (segEnd 0 q.segs)) :
    ∀ p∈v.segs, (p.2=1 ∧ cv tr tt p.1 len=0) ∨ cv tr tt p.1 len=p.2 := by
  intro p hp
  have hb := seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
  have hfit : p.1+p.2≤tr.height tt := Nat.le_trans hb.2 v.fits
  apply Parser.length_cases hL hfit _ (v.valid p hp)
  intro r hr hrow
  exact zero_of_false hL (by omega) (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
    (q.suffix r (by omega) (by omega))

end ZkFormal.NearV3.Qv.Extract
