import ZkFormal.NearV3.Qv.Extract.KeyTraffic

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable
open Candidates.ValueTable (vid tau users)

def counterMessage (tr : Trace Fp) (tt r : Nat) (sd : Bool) : List Fp :=
  [tr.cell tt r vid,tr.cell tt r tau,tr.cell tt r Candidates.ValueTable.len,
    if sd then tr.cell tt r users+1 else tr.cell tt r users]

theorem counter_walk_row (tr : Trace Fp) (tt r : Nat) (pub : List Fp)
    (ha : tr.cell tt r walk=1) (sd : Bool) :
    rowTraffic interactions tr tt r pub Candidates.ValueTable.B_QVC sd=
      if tr.cell tt r present=1 then [counterMessage tr tt r sd] else [] := by
  have hz : (1:Fp)-1=0 := by grind
  cases sd <;> by_cases hp : tr.cell tt r present=1 <;>
    simp [rowTraffic,interactions,send,recv,B_FINAL,B_KEYNIB,B_VBYTES,B_QSH,Candidates.ValueTable.B_QVC,
      Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,counterMessage,readMode,ha,hp,
      eval_c,eval_k,eval_add,eval_mul,eval_not,hz,Lean.Grind.Semiring.mul_zero,
      Lean.Grind.Semiring.natCast_zero,Lean.Grind.Semiring.natCast_one]

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
include hL

theorem present_iff {r : Nat} (hr : r<tr.height tt) :
    tr.cell tt r present=1 ↔ tr.cell tt r wl=1 ∧ tr.cell tt r absent=0 := by
  have hh := con hL hr (e:=sub (c present) (.mul (c wl) (Dsl.not (c absent)))) (by simp [constraints])
  simp only [eval_sub,eval_c,eval_mul,eval_not] at hh
  have hl := isBool hL hr (x:=wl) (by simp [walkBools])
  have ha := isBool hL hr (x:=absent) (by simp [walkBools])
  rcases hl with hl | hl <;> rcases ha with ha | ha <;> rw [hl,ha] at hh ⊢ <;> constructor <;> intro h <;> grind

theorem absent_vid_zero {r : Nat} (hr : r<tr.height tt) (hw : tr.cell tt r walk=1)
    (ha : tr.cell tt r absent=1) : tr.cell tt r vid=0 := by
  have hh := con hL hr (e:=.mul (c absent) (.mul (c walk) (c vid))) (by simp [constraints])
  simp only [eval_mul,eval_c,hw,ha] at hh
  grind

theorem counter_segment_row {s len : Nat} (hfit : s+len≤tr.height tt)
    (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s len)
    (r : Nat) (hr : s≤r) (hb : r<s+len) (sd : Bool) :
    rowTraffic interactions tr tt r pub Candidates.ValueTable.B_QVC sd=
      if r+1=s+len ∧ tr.cell tt s absent=0 then [counterMessage tr tt r sd] else [] := by
  have ha : tr.cell tt r walk=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 r hr hb
  have hab := walk_metadata hL hfit hs (x:=absent) (by simp) r hr hb
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
  rw [counter_walk_row tr tt r pub ha sd]
  simp only [present_iff hL (show r<tr.height tt by omega),hl,hab]

theorem walk_read_mode {r : Nat} (hr : r<tr.height tt) (ha : tr.cell tt r walk=1) :
    tr.cell tt r Candidates.ValueTable.len=
      tr.cell tt r main*(tr.cell tt r lo+tr.cell tt r lo*tr.cell tt r hi)+2*(1-tr.cell tt r main) := by
  have hh := gate_eq hL hr (g:=c walk) (a:=readMode)
    (b:=.add (.mul (c main) (.add (c lo) group)) (smul 2 (Dsl.not (c main))))
    (by simp [constraints]) ha
  simp only [readMode,eval_c,eval_add,eval_mul,group,eval_smul,eval_not] at hh
  grind

theorem counter_message_constant {s len : Nat} (hfit : s+len≤tr.height tt)
    (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s len)
    (r : Nat) (hr : s≤r) (hb : r<s+len) (sd : Bool) :
    counterMessage tr tt r sd=counterMessage tr tt s sd := by
  have hp := hs.1
  have ha : tr.cell tt r walk=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 r hr hb
  have has : tr.cell tt s walk=1 := by simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 s (by omega) (by omega)
  have hm := walk_metadata hL hfit hs (x:=main) (by simp) r hr hb
  have hl := walk_metadata hL hfit hs (x:=lo) (by simp) r hr hb
  have hh := walk_metadata hL hfit hs (x:=hi) (by simp) r hr hb
  have ht := walk_metadata hL hfit hs (x:=tau) (by simp) r hr hb
  have hv := walk_metadata hL hfit hs (x:=vid) (by simp) r hr hb
  have hu := walk_metadata hL hfit hs (x:=users) (by simp) r hr hb
  have hmode : tr.cell tt r Candidates.ValueTable.len=tr.cell tt s Candidates.ValueTable.len := by
    rw [walk_read_mode hL (by omega) ha,walk_read_mode hL (by omega) has,hm,hl,hh]
  simp only [counterMessage,ht,hv,hu,hmode]

end ZkFormal.NearV3.Qv.Extract
