import ZkFormal.NearV3.Qv.Extract.BufferedStructure
import ZkFormal.NearV3.Qv.Extract.ParserBytes

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

/-- The physical parser contributes one shard-byte message or one count message
at its selected gates; it never receives on the shard channel. -/
theorem shard_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (sd : Bool) :
    rowTraffic interactions tr tt r pub B_QSH sd=
      (if sd ∧ tr.cell tt r shard=1 then
        [[tr.cell tt r tau,tr.cell tt r entry,subpos.eval tr tt r pub,tr.cell tt r byte]] else []) ++
      (if sd ∧ tr.cell tt r header*tr.cell tt r (sel 3)=1 then
        [[tr.cell tt r tau,0,8,tr.cell tt r count]] else []) := by
  cases sd <;> by_cases hsh : tr.cell tt r shard=1 <;>
    by_cases hh : tr.cell tt r header*tr.cell tt r (sel 3)=1 <;>
    simp [rowTraffic,interactions,send,recv,B_QVC,B_VBYTES,B_QSH,
      Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,
      headerEnd,hsh,hh,eval_c,eval_mul,eval_k] <;> grind

variable {tr : Trace Fp} {tt r : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable (hr : r<tr.height tt) (hw : tr.cell tt r Candidates.CombinedTable.walk=0)
include hL hr hw

theorem selected_subpos (ha : tr.cell tt r act=1) (hm : tr.cell tt r mRaw=0)
    {i : Nat} (hi : i<8) (hsel : tr.cell tt r (sel i)=1) :
    subpos.eval tr tt r pub=(i:Fp) := by
  have hz := selector_exclusive hL hr hw ha hm hi hsel
  have hv : ∀ j, j<8 → tr.cell tt r (sel j)=if j=i then 1 else 0 := by
    intro j hj
    by_cases he : j=i
    · simpa only [he,ite_true] using hsel
    · simp only [he,ite_false]; exact hz j hj he
  have h0 := hv 0 (by omega)
  have h1 := hv 1 (by omega)
  have h2 := hv 2 (by omega)
  have h3 := hv 3 (by omega)
  have h4 := hv 4 (by omega)
  have h5 := hv 5 (by omega)
  have h6 := hv 6 (by omega)
  have h7 := hv 7 (by omega)
  have heval (v : Nat) : (Expr.const v).eval tr tt r pub=(v:Fp) := rfl
  simp only [subpos,List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
    List.append_assoc,List.nil_append,smul]
  have hc : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp <;> grind

/-- A selected shard row emits its exact byte ordinal. -/
theorem shard_selected_row (hp : tr.cell tt r shard=1)
    {i : Nat} (hi : i<8) (hsel : tr.cell tt r (sel i)=1) :
    rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH true=
      [[tr.cell tt r tau,tr.cell tt r entry,(i:Fp),tr.cell tt r byte]] := by
  have hx := phase_exclusive hL hr hw (x:=shard) (by simp [phases]) hp
  have hh := hx.2 header (by simp [phases]) (by decide)
  have hm := hx.2 mRaw (by simp [phases]) (by decide)
  rw [parser_traffic hL hr hw,shard_row]
  have hz := selected_subpos hL hr hw hx.1 hm hi hsel
  simp only [hp,hh,hz]
  have he : (0:Fp)*tr.cell tt r (sel 3)≠1 := by grind
  simp [he]

/-- The last header row emits precisely the declared count. -/
theorem shard_header_row (hp : tr.cell tt r header=1) (hsel : tr.cell tt r (sel 3)=1) :
    rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH true=
      [[tr.cell tt r tau,0,8,tr.cell tt r count]] := by
  have hx := phase_exclusive hL hr hw (x:=header) (by simp [phases]) hp
  have hz := hx.2 shard (by simp [phases]) (by decide)
  rw [parser_traffic hL hr hw,shard_row]
  simp only [hz,hp,hsel]
  have h0 : (0:Fp)≠1 := by decide
  have h1 : (1:Fp)*1=1 := by grind
  simp [h0,h1]

/-- First-index, next-index and raw rows are silent on the shard channel. -/
theorem shard_nonphase_row {x : Nat} (hx : x∈[firstIndex,nextIndex,mRaw])
    (hp : tr.cell tt r x=1) (sd : Bool) :
    rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH sd=[] := by
  have hxp : x∈phases := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [phases]
  have hhx : header≠x := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> decide
  have hsx : shard≠x := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> decide
  have he := phase_exclusive hL hr hw hxp hp
  have hh := he.2 header (by simp [phases]) hhx
  have hsh := he.2 shard (by simp [phases]) hsx
  rw [parser_traffic hL hr hw,shard_row]
  have hz : (0:Fp)≠1 := by decide
  have he : (0:Fp)*tr.cell tt r (sel 3)≠1 := by grind
  simp [hh,hsh,hz,he]

/-- Earlier header bytes do not emit a count message. -/
theorem shard_header_early (hp : tr.cell tt r header=1)
    {i : Nat} (hi : i<3) (hsel : tr.cell tt r (sel i)=1) (sd : Bool) :
    rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH sd=[] := by
  have hx := phase_exclusive hL hr hw (x:=header) (by simp [phases]) hp
  have hz := hx.2 shard (by simp [phases]) (by decide)
  have hm := hx.2 mRaw (by simp [phases]) (by decide)
  have h3 := selector_exclusive hL hr hw hx.1 hm (by omega) hsel 3 (by omega) (by omega)
  rw [parser_traffic hL hr hw,shard_row]
  have h0 : (0:Fp)≠1 := by decide
  have h1 : (1:Fp)*0≠1 := by grind
  simp [hp,hz,h3,h0,h1]

theorem shard_parser_recv :
    rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QSH false=[] := by
  rw [parser_traffic hL hr hw,shard_row]
  simp

end ZkFormal.NearV3.Qv.Extract.Parser
