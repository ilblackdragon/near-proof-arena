import ZkFormal.NearV3.Qv.Extract.BufferedLayout

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp} {s n : Nat}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (hfit : s+n≤tr.height tt)
variable (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
variable (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
variable (hm : tr.cell tt s mBuffer=1)
include hL hfit hw hs hm

/-- The entry number is constant across all 24 bytes of one entry. -/
theorem buffered_entry_constant {r : Nat} (hr : s≤r) (hb : r<s+n)
    (hp : tr.cell tt r shard=1) (hz : tr.cell tt r (sel 0)=1) :
    ∀ q, r≤q → q<r+24 → tr.cell tt q entry=tr.cell tt r entry := by
  have rows := buffered_entry_rows hL hfit hw hs hm hr hb hp hz
  apply const_of
  intro q hq hqb
  have hrow : q<tr.height tt := by omega
  have hwalk := hw q (by omega) (by omega)
  have hend : tr.cell tt q nextIndex*tr.cell tt q (sel 7)=0 := by
    by_cases hsh : q<r+8
    · have hh := (rows.2.1 (q-r) (by omega)).1
      have he : r+(q-r)=q := by omega
      rw [he] at hh
      have hz := (phase_exclusive hL hrow hwalk (x:=shard) (by simp [phases]) hh).2
        nextIndex (by simp [phases]) (by decide)
      rw [hz]; grind
    · by_cases hf : q<r+16
      · have hh := (rows.2.2.1 (q-(r+8)) (by omega)).1
        have he : r+8+(q-(r+8))=q := by omega
        rw [he] at hh
        have hz := (phase_exclusive hL hrow hwalk (x:=firstIndex) (by simp [phases]) hh).2
          nextIndex (by simp [phases]) (by decide)
        rw [hz]; grind
      · have hh := rows.2.2.2 (q-(r+16)) (by omega)
        have he : r+16+(q-(r+16))=q := by omega
        rw [he] at hh
        have hx := phase_exclusive hL hrow hwalk (x:=nextIndex) (by simp [phases]) hh.1
        have hraw := hx.2 mRaw (by simp [phases]) (by decide)
        have h7 := selector_exclusive hL hrow hwalk hx.1 hraw (by omega) hh.2 7 (by omega) (by omega)
        rw [h7]; grind
  have hnot := hs.2.2.2.2.2 q (by omega) (by omega)
  have hl : tr.cell tt q vl=0 := by
    rcases isBool hL hrow hwalk (x:=vl) (by simp) with hl|hl
    · exact hl
    · simp [isOne,hl] at hnot
  have hc := (record_continue hL hfit hw hs q (by omega) (by omega) hl).2
  exact entry_carry hL hrow hwalk (by omega) hc hend

/-- The first entry retains the initial counter zero through the four-byte header. -/
theorem buffered_first_entry_zero (hn : 4<n) : tr.cell tt (s+4) entry=0 := by
  have hf : tr.cell tt s vf=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.1
  have hzero := (start_state hL (show s<tr.height tt by omega) (hw s (by omega) (by omega)) hf).1
  have carry : ∀ q, s≤q → q<s+5 → tr.cell tt q entry=tr.cell tt s entry := by
    apply const_of
    intro q hq hqb
    have hh := (buffered_header_rows hL hfit hw hs hm (q-s) (by omega)).2.1
    have he : s+(q-s)=q := by omega
    rw [he] at hh
    have hrow : q<tr.height tt := by omega
    have hwalk := hw q hq (by omega)
    have hz := (phase_exclusive hL hrow hwalk (x:=header) (by simp [phases]) hh).2
      nextIndex (by simp [phases]) (by decide)
    have hnot := hs.2.2.2.2.2 q hq (by omega)
    have hl : tr.cell tt q vl=0 := by
      rcases isBool hL hrow hwalk (x:=vl) (by simp) with hl|hl
      · exact hl
      · simp [isOne,hl] at hnot
    have hc := (record_continue hL hfit hw hs q hq (by omega) hl).2
    apply entry_carry hL hrow hwalk (by omega) hc
    rw [hz]; grind
  rw [carry (s+4) (by omega) (by omega),hzero]

/-- The entry field numbers each physical entry by its zero-based ordinal. -/
theorem buffered_entry_ordinal {k : Nat} (hlen : n=4+24*k)
    (hstarts : ∀ j, j<k → tr.cell tt (s+4+24*j) shard=1 ∧ tr.cell tt (s+4+24*j) (sel 0)=1) :
    ∀ j, j<k → tr.cell tt (s+4+24*j) entry=(j: Fp) := by
  intro j
  induction j with
  | zero =>
    intro hj
    simpa only [Nat.mul_zero,Nat.add_zero,Lean.Grind.Semiring.natCast_zero] using buffered_first_entry_zero hL hfit hw hs hm (by omega)
  | succ j ih =>
    intro hj
    have prev := ih (by omega)
    have start := hstarts j (by omega)
    have he := buffered_entry_exit hL hfit hw hs hm (r:=s+4+24*j)
      (by omega) (by omega) start.1 start.2
    have hconst := buffered_entry_constant hL hfit hw hs hm (r:=s+4+24*j)
      (by omega) (by omega) start.1 start.2 (s+4+24*j+23) (by omega) (by omega)
    rcases he with he|he
    · omega
    · have hend := he.2.2.2
      rw [hconst,prev] at hend
      have hrow : s+4+24*j+24=s+4+24*(j+1) := by omega
      rw [hrow] at hend
      simpa only [natCast_add,Lean.Grind.Semiring.natCast_one] using hend

/-- The declared field count is precisely the number of physical entries. -/
theorem buffered_count_exact {k : Nat} (hlen : n=4+24*k)
    (hstarts : ∀ j, j<k → tr.cell tt (s+4+24*j) shard=1 ∧ tr.cell tt (s+4+24*j) (sel 0)=1) :
    cv tr tt s count=k := by
  have hcount : tr.cell tt s count=(k:Fp) := by
    by_cases hk : k=0
    · rcases buffered_header_exit hL hfit hw hs hm with he|he
      · simpa only [hk,Lean.Grind.Semiring.natCast_zero] using he.2
      · omega
    · have start := hstarts (k-1) (by omega)
      have he := buffered_entry_exit hL hfit hw hs hm (r:=s+4+24*(k-1))
        (by omega) (by omega) start.1 start.2
      have hconst := buffered_entry_constant hL hfit hw hs hm (r:=s+4+24*(k-1))
        (by omega) (by omega) start.1 start.2 (s+4+24*(k-1)+23) (by omega) (by omega)
      have hord := buffered_entry_ordinal hL hfit hw hs hm hlen hstarts (k-1) (by omega)
      rcases he with he|he
      · rw [hconst,hord] at he
        have heq : k=(k-1)+1 := by omega
        rw [heq,natCast_add,Lean.Grind.Semiring.natCast_one]
        exact he.2.symm
      · omega
  have hheight := height_le hL
  have hk : k<P := by unfold P; omega
  simp only [cv,hcount,toNat_natCast,Nat.mod_eq_of_lt hk]

end ZkFormal.NearV3.Qv.Extract.Parser
