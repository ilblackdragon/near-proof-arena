import ZkFormal.NearV3.Qv.Extract.ParserView

namespace ZkFormal.NearV3.Qv.Extract.Parser
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.ValueTable

def endpointMessage (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (sd : Bool) : List Fp :=
  [tr.cell tt r vid,tr.cell tt r tau,mode.eval tr tt r pub,if sd then 0 else tr.cell tt r users]

theorem endpoint_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp) (sd : Bool) :
    rowTraffic interactions tr tt r pub B_QVC sd=
      if tr.cell tt r vf=1 then [endpointMessage tr tt r pub sd] else [] := by
  cases sd <;> by_cases hf : tr.cell tt r vf=1 <;>
    simp [rowTraffic,interactions,send,recv,B_QVC,B_VBYTES,B_QSH,
      Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,endpointMessage,hf,eval_c,eval_k,
      Lean.Grind.Semiring.natCast_zero]

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable {s n : Nat} (hfit : s+n≤tr.height tt)
variable (hw : ∀ r, s≤r → r<s+n → tr.cell tt r Candidates.CombinedTable.walk=0)
variable (hs : IsSeg (isOne tr tt act) (isOne tr tt vf) (isOne tr tt vl) s n)
include hL hfit hw hs

theorem endpoint_constant (r : Nat) (hr : s≤r) (hb : r<s+n) (sd : Bool) :
    endpointMessage tr tt r pub sd=endpointMessage tr tt s pub sd := by
  have hv := metadata hL hfit hw hs (x:=vid) (by simp) r hr hb
  have ht := metadata hL hfit hw hs (x:=tau) (by simp) r hr hb
  have hu := metadata hL hfit hw hs (x:=users) (by simp) r hr hb
  have hm := metadata hL hfit hw hs (x:=mBuffer) (by simp) r hr hb
  have hh := metadata hL hfit hw hs (x:=mRaw) (by simp) r hr hb
  simp only [endpointMessage,mode,eval_add,eval_smul,eval_c,hv,ht,hu,hm,hh]

theorem endpoint_segment_row (r : Nat) (hr : s≤r) (hb : r<s+n) (sd : Bool) :
    rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QVC sd=
      if r=s then [endpointMessage tr tt s pub sd] else [] := by
  rw [parser_traffic hL (by omega) (hw r hr hb),endpoint_row]
  have hf : tr.cell tt r vf=1 ↔ r=s := by
    constructor
    · intro hf
      by_cases he : r=s
      · exact he
      · have hz := hs.2.2.2.2.1 r (by omega) hb
        simp [isOne,hf] at hz
    · intro he
      subst r
      simpa only [isOne,decide_eq_true_eq] using hs.2.1
  simp only [hf,endpoint_constant hL hfit hw hs r hr hb sd]

theorem endpoint_segment (sd : Bool) :
    (List.range' s n).flatMap (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QVC sd)=
      [endpointMessage tr tt s pub sd] := by
  have hp := hs.1
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
  have he : List.range' s n=s::List.range' (s+1) k := by rw [hk,List.range'_succ]
  rw [he,List.flatMap_cons,endpoint_segment_row hL hfit hw hs s (by omega) (by omega) sd,if_pos rfl]
  have hz : (List.range' (s+1) k).flatMap
      (fun r => rowTraffic Candidates.CombinedTable.interactions tr tt r pub B_QVC sd)=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro r hr
    have hb := List.mem_range'.mp hr
    rw [endpoint_segment_row hL hfit hw hs r (by omega) (by omega) sd,if_neg (by omega)]
  rw [hz,List.append_nil]

end ZkFormal.NearV3.Qv.Extract.Parser
