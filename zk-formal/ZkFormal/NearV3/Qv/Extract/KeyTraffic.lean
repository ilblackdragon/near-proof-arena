import ZkFormal.NearV3.Qv.Extract.FinalAggregate

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable

/-- Key-symbol messages of one row, retaining the exact two-nibble byte order. -/
def keyRowMessages (tr : Trace Fp) (tt r : Nat) (pub : List Fp) : List (List Fp) :=
  (if tr.cell tt r wf=1 then [[wid.eval tr tt r pub,0,(SYM_START:Nat),0]] else []) ++
  (if tr.cell tt r walk=1 then
    [[wid.eval tr tt r pub,2*tr.cell tt r wp+1,(nibble 4).eval tr tt r pub,0],
     [wid.eval tr tt r pub,2*tr.cell tt r wp+2,(nibble 0).eval tr tt r pub,0]] else []) ++
  (if tr.cell tt r wl=1 then
    [[wid.eval tr tt r pub,2*tr.cell tt r wp+3,(SYM_END:Nat),1]] else [])

theorem key_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    rowTraffic interactions tr tt r pub B_KEYNIB true=keyRowMessages tr tt r pub := by
  by_cases hf : tr.cell tt r wf=1 <;> by_cases ha : tr.cell tt r walk=1 <;>
    by_cases hl : tr.cell tt r wl=1 <;>
    simp [rowTraffic,interactions,send,recv,B_FINAL,B_KEYNIB,B_VBYTES,B_QSH,Candidates.ValueTable.B_QVC,
      Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,keyRowMessages,hf,ha,hl,
      eval_c,eval_k,eval_add,eval_smul,Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one]
  all_goals grind

theorem key_recv_empty (tr : Trace Fp) (tt r : Nat) (pub : List Fp) :
    rowTraffic interactions tr tt r pub B_KEYNIB false=[] := by
  simp [rowTraffic,interactions,send,recv,B_FINAL,B_KEYNIB,B_VBYTES,B_QSH,Candidates.ValueTable.B_QVC]

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
include hL

theorem key_inactive {r : Nat} (hr : r<tr.height tt) (ha : tr.cell tt r walk=0) :
    rowTraffic interactions tr tt r pub B_KEYNIB true=[] := by
  have hf : ¬tr.cell tt r wf=1 := by
    intro hh
    have he := flag_walk hL hr (x:=wf) (by simp) hh
    rw [ha] at he
    grind
  have hl : ¬tr.cell tt r wl=1 := by
    intro hh
    have he := flag_walk hL hr (x:=wl) (by simp) hh
    rw [ha] at he
    grind
  rw [key_row]
  simp only [keyRowMessages,if_neg hf,if_neg hl,ha]
  simp

/-- All physical key traffic is exactly the ordered concatenation of extracted
walks, with no parser or padding messages. -/
theorem key_physical (q : WalkChain tr tt) :
    (List.range (tr.height tt)).flatMap (fun r => rowTraffic interactions tr tt r pub B_KEYNIB true)=
    q.segs.flatMap (fun p => (List.range' p.1 p.2).flatMap (fun r => keyRowMessages tr tt r pub)) := by
  have he := flatMap_rows_segs (tr.height tt) q.segs
    (fun r => rowTraffic interactions tr tt r pub B_KEYNIB true) q.consecutive q.fits (by
      intro r hr hb
      exact key_inactive hL hb (zero_of_false hL hb (x:=walk) (by simp [walkBools]) (q.suffix r hr hb)))
  simpa only [key_row] using he

theorem key_segment_row {s len : Nat} (hfit : s+len≤tr.height tt)
    (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s len)
    (r : Nat) (hr : s≤r) (hb : r<s+len) :
    rowTraffic interactions tr tt r pub B_KEYNIB true=
      (if r=s then [[wid.eval tr tt s pub,0,(SYM_START:Nat),0]] else []) ++
      [[wid.eval tr tt s pub,2*((r-s:Nat):Fp)+1,(nibble 4).eval tr tt r pub,0],
       [wid.eval tr tt s pub,2*((r-s:Nat):Fp)+2,(nibble 0).eval tr tt r pub,0]] ++
      (if r+1=s+len then [[wid.eval tr tt s pub,2*((r-s:Nat):Fp)+3,(SYM_END:Nat),1]] else []) := by
  have ha : tr.cell tt r walk=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 r hr hb
  have hf : tr.cell tt r wf=1 ↔ r=s := by
    constructor
    · intro hf
      by_cases he : r=s
      · exact he
      · have hz := hs.2.2.2.2.1 r (by omega) hb
        simp [isOne,hf] at hz
    · intro he
      subst r
      simpa only [isOne,decide_eq_true_eq] using hs.2.1
  have hl : tr.cell tt r wl=1 ↔ r+1=s+len := by
    constructor
    · intro hl
      by_cases he : r+1=s+len
      · exact he
      · have hz := hs.2.2.2.2.2 r hr (by omega)
        simp [isOne,hl] at hz
    · intro he
      have he' : r=s+len-1 := by omega
      rw [he']
      simpa only [isOne,decide_eq_true_eq] using hs.2.2.1
  have ht := walk_metadata hL hfit hs (x:=Candidates.ValueTable.tau) (by simp) r hr hb
  have hslot := walk_metadata hL hfit hs (x:=slot) (by simp) r hr hb
  have hw : wid.eval tr tt r pub=wid.eval tr tt s pub := by
    simp only [wid,eval_sum_cons,eval_sum_nil,eval_k,eval_c,eval_smul,ht,hslot]
  rw [key_row]
  simp only [keyRowMessages,hf,hl,ha,ite_true,hw,walk_position hL hfit hs r hr hb]

end ZkFormal.NearV3.Qv.Extract
