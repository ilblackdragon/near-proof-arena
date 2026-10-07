import ZkFormal.NearV3.Qv.Extract.ParserStart

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal Candidates.CombinedTable.table tr tt pub) (q : WalkChain tr tt)
include hL

theorem parser_suffix_segFacts
    (hactive : tr.cell tt (segEnd 0 q.segs) act=1) :
    SegFacts (tr.height tt-segEnd 0 q.segs)
      (fun r => isOne tr tt act (segEnd 0 q.segs+r))
      (fun r => isOne tr tt vf (segEnd 0 q.segs+r))
      (fun r => isOne tr tt vl (segEnd 0 q.segs+r)) := by
  let S := segEnd 0 q.segs
  have hfit : S≤tr.height tt := q.fits
  have hw : ∀ r, r<tr.height tt-S → tr.cell tt (S+r) Candidates.CombinedTable.walk=0 := by
    intro r hr
    exact zero_of_false hL (by omega) (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix (S+r) (by dsimp [S]; omega) (by omega))
  have hz : ∀ r x, r<tr.height tt-S →
      x∈([act,vf,vl,vz,gb,cont] ++ modes ++ [header,shard,firstIndex,nextIndex] ++ selectors) →
      isOne tr tt x (S+r)=false → tr.cell tt (S+r) x=0 := by
    intro r x hr hx hh
    rcases Parser.isBool hL (show S+r<tr.height tt by omega) (hw r hr) hx with he | he
    · exact he
    · simp [isOne,he] at hh
  change SegFacts (tr.height tt-S) (fun r => isOne tr tt act (S+r))
    (fun r => isOne tr tt vf (S+r)) (fun r => isOne tr tt vl (S+r))
  constructor
  · intro r hr hf
    simp only [isOne,decide_eq_true_eq] at hf ⊢
    exact Parser.marker hL (by omega) (hw r hr) (Or.inl rfl) hf
  · intro r hr hl
    simp only [isOne,decide_eq_true_eq] at hl ⊢
    exact Parser.marker hL (by omega) (hw r hr) (Or.inr rfl) hl
  · intro r hr ha hl
    have hzero := hz r vl (by omega) (by simp) hl
    simp only [isOne,decide_eq_true_eq] at ha
    have hh := Parser.inside_next hL (show S+r<tr.height tt by omega) (hw r (by omega)) (by omega) ha hzero
    simp only [isOne,Nat.add_assoc,decide_eq_true_eq,decide_eq_false_iff_not]
    have hznext : tr.cell tt (S+(r+1)) vf=0 := by simpa only [Nat.add_assoc] using hh.2.1
    exact ⟨hh.1,by rw [hznext]; decide⟩
  · intro r hr hl ha
    simp only [isOne,decide_eq_true_eq,Nat.add_assoc] at hl ha ⊢
    have hha : tr.cell tt (S+r+1) act=1 := by simpa only [Nat.add_assoc] using ha
    have hh := Parser.next_record hL (show S+r<tr.height tt by omega) (hw r (by omega)) (by omega) hl hha
    simpa only [Nat.add_assoc] using hh
  · intro r hr ha
    have hzero := hz r act (by omega) (by simp) ha
    have hh := Parser.padding_next hL (show S+r<tr.height tt by omega) (hw r (by omega)) (by omega) hzero
    have he : tr.cell tt (S+(r+1)) act=0 := by simpa only [Nat.add_assoc] using hh
    change decide (tr.cell tt (S+(r+1)) act=1)=false
    simp [he]
  · intro hH
    simp only [Nat.add_zero,isOne,decide_eq_true_eq]
    exact parser_suffix_start hL q (by change S<tr.height tt; omega) hactive
  · intro hH ha
    simp only [isOne,decide_eq_true_eq] at ha ⊢
    exact Parser.physical_stop hL (by omega) (hw _ (by omega)) (by omega) ha

theorem parser_suffix_segments (hactive : tr.cell tt (segEnd 0 q.segs) act=1)
    (hfit : segEnd 0 q.segs<tr.height tt) :
    ∃ segs : List (Nat × Nat), Consec 0 segs ∧ segEnd 0 segs≤tr.height tt-segEnd 0 q.segs ∧
      (∀ p∈segs, IsSeg (fun r => isOne tr tt act (segEnd 0 q.segs+r))
        (fun r => isOne tr tt vf (segEnd 0 q.segs+r))
        (fun r => isOne tr tt vl (segEnd 0 q.segs+r)) p.1 p.2) ∧
      (∀ r, segEnd 0 segs≤r → r<tr.height tt-segEnd 0 q.segs →
        isOne tr tt act (segEnd 0 q.segs+r)=false) :=
  segments_of (parser_suffix_segFacts hL q hactive) (by omega)

theorem parser_suffix_inactive (hz : tr.cell tt (segEnd 0 q.segs) act=0) :
    ∀ d, segEnd 0 q.segs+d<tr.height tt → tr.cell tt (segEnd 0 q.segs+d) act=0 := by
  intro d
  induction d with
  | zero => intro _; simpa only [Nat.add_zero] using hz
  | succ d ih =>
    intro hd
    have hr : segEnd 0 q.segs+d<tr.height tt := by omega
    have hw := zero_of_false hL hr (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
      (q.suffix _ (by omega) hr)
    have hh := Parser.padding_next hL hr hw (by omega) (ih hr)
    simpa only [Nat.add_assoc] using hh

end ZkFormal.NearV3.Qv.Extract
