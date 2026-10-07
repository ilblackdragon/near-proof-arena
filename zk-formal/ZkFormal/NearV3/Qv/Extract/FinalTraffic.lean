import ZkFormal.NearV3.Qv.Extract.WalkCount
import ZkFormal.Near.Extract.BusCount

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable
open Candidates.ValueTable (tau vid)

/-- The authenticated lookup result requested by this queue row. -/
def finalMessage (tr : Trace Fp) (tt r : Nat) (pub : List Fp) : List Fp :=
  [wid.eval tr tt r pub,tr.cell tt r tau,tr.cell tt r absent,tr.cell tt r vid]

theorem final_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    rowTraffic interactions tr tt r pub B_FINAL false=
      if tr.cell tt r wl=1 then [finalMessage tr tt r pub] else [] := by
  by_cases h : tr.cell tt r wl=1 <;>
    simp [h,rowTraffic,interactions,send,recv,B_FINAL,B_KEYNIB,B_VBYTES,B_QSH,Candidates.ValueTable.B_QVC,
    Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,finalMessage,eval_c]

theorem final_send_empty (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    rowTraffic interactions tr tt r pub B_FINAL true=[] := by
  simp [rowTraffic,interactions,send,recv,B_FINAL,B_KEYNIB,B_VBYTES,B_QSH,Candidates.ValueTable.B_QVC]

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
variable {s len : Nat} (hfit : s+len≤tr.height tt)
variable (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s len)
include hL hfit hs

theorem final_message_constant (r : Nat) (hr : s≤r) (hb : r<s+len) :
    finalMessage tr tt r pub=finalMessage tr tt s pub := by
  have ht := walk_metadata hL hfit hs (x:=tau) (by simp) r hr hb
  have hv := walk_metadata hL hfit hs (x:=vid) (by simp) r hr hb
  have ha := walk_metadata hL hfit hs (x:=absent) (by simp) r hr hb
  have hslot := walk_metadata hL hfit hs (x:=slot) (by simp) r hr hb
  simp only [finalMessage,wid,eval_sum_cons,eval_sum_nil,eval_k,eval_c,eval_smul,ht,hv,ha,hslot]

theorem final_segment_row (r : Nat) (hr : s≤r) (hb : r<s+len) :
    rowTraffic interactions tr tt r pub B_FINAL false=
      if r+1=s+len then [finalMessage tr tt s pub] else [] := by
  rw [final_row]
  by_cases he : r+1=s+len
  · have hrend : r=s+len-1 := by omega
    have hl : tr.cell tt r wl=1 := by
      rw [hrend]
      simpa only [isOne,decide_eq_true_eq] using hs.2.2.1
    rw [if_pos hl,if_pos he,final_message_constant hL hfit hs r hr hb]
  · have hz := zero_of_false hL (show r<tr.height tt by omega) (x:=wl) (by simp [walkBools])
      (hs.2.2.2.2.2 r hr (by omega))
    rw [if_neg (by rw [hz]; decide),if_neg he]


end ZkFormal.NearV3.Qv.Extract
