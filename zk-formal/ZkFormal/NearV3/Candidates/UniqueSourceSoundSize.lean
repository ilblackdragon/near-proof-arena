import ZkFormal.NearV3.Candidates.UniqueSourceSoundSemantic
import ZkFormal.NearV3.Rcpt.Candidates.DedupExtractSizeTraffic
namespace ZkFormal.NearV3.Candidates.UniqueSourceSoundSize
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Rcpt.Candidates
open SrcpV3 UniqueSourceSoundShadow

def rowSize (tr : Trace Fp) (tt r : Nat) : Nat :=
  (if tr.cell tt r rt=1 ∧ tr.cell tt r dup=0 then (tr.cell tt r L).toNat+44 else 0)+
  (if tr.cell tt r sf=1 ∧ tr.cell tt r sg=1 ∧ tr.cell tt r lf=0 then 33 else 0)

def prefixSize (tr : Trace Fp) (tt n : Nat) : Nat :=
  ((List.range n).map (rowSize tr tt)).sum

theorem flag {tr : Trace Fp} {tt cap r x : Nat} {pub : List Fp}
    (h : TableLocal (UniqueSourceCharge.table cap) tr tt pub) (hr : r<tr.height tt)
    (hx : x∈SrcpProof.bools) (hn : x≠sz) : tr.cell tt r x=0 ∨ tr.cell tt r x=1 := by
  have hh:=DedupProof.isBool (old_local h) hr (List.mem_append_left _ hx)
  simpa only [shadow,hn,ite_false] using hh

theorem row_field {tr : Trace Fp} {tt cap r : Nat} {pub : List Fp}
    (h : TableLocal (UniqueSourceCharge.table cap) tr tt pub) (hr : r<tr.height tt) :
    Fp.ofNat (rowSize tr tt r)=
      (tr.cell tt r rt-tr.cell tt r dup)*(tr.cell tt r L+44)+
      33*(tr.cell tt r sf*tr.cell tt r sg*(1-tr.cell tt r lf)) := by
  have hrt:=flag h hr (x:=rt) (by simp [SrcpProof.bools]) (by decide)
  have hdup:=flag h hr (x:=dup) (by simp [SrcpProof.bools]) (by decide)
  have hsf:=flag h hr (x:=sf) (by simp [SrcpProof.bools]) (by decide)
  have hsg:=flag h hr (x:=sg) (by simp [SrcpProof.bools]) (by decide)
  have hlf:=flag h hr (x:=lf) (by simp [SrcpProof.bools]) (by decide)
  have hd : tr.cell tt r dup=1→tr.cell tt r rt=1 := by
    intro hh
    have ht:=DedupProof.duplicate_root (old_local h) hr
    simpa [shadow,SrcpV3.dup,SrcpV3.rt,sz] using ht (by simpa [shadow,SrcpV3.dup,sz] using hh)
  rcases hrt with h1|h1 <;> rcases hdup with h2|h2 <;>
    rcases hsf with h3|h3 <;> rcases hsg with h4|h4 <;> rcases hlf with h5|h5
  all_goals simp [rowSize,h1,h2,h3,h4,h5,←ofNat_add',Fp.ofNat_toNat,show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 33=(33:Fp) from rfl,show Fp.ofNat 44=(44:Fp) from rfl] <;> grind

set_option maxRecDepth 32768 in
theorem initial_mem : UniqueSourceCharge.initial∈UniqueSourceCharge.constraints := by simp [UniqueSourceCharge.constraints]
set_option maxRecDepth 32768 in
theorem step_mem : UniqueSourceCharge.step∈UniqueSourceCharge.constraints := by simp [UniqueSourceCharge.constraints]

theorem step_field {tr : Trace Fp} {tt cap r : Nat} {pub : List Fp}
    (h : TableLocal (UniqueSourceCharge.table cap) tr tt pub) (hr : r+1<tr.height tt) :
    tr.cell tt (r+1) sz=tr.cell tt r sz+Fp.ofNat (rowSize tr tt (r+1)) := by
  have hh:=h.constr r (by omega) UniqueSourceCharge.step step_mem
  simp only [UniqueSourceCharge.step,eval_mul,eval_sub,eval_sum_cons,eval_sum_nil,
    eval_c,eval_n,eval_add,eval_k,eval_smul,eval_mul3,eval_not,eval_isTransition,
    Nat.mod_eq_of_lt hr,show r+1≠tr.height tt by omega,ite_false] at hh
  rw [row_field h hr]
  grind

theorem initial_field {tr : Trace Fp} {tt cap : Nat} {pub : List Fp}
    (h : TableLocal (UniqueSourceCharge.table cap) tr tt pub) :
    tr.cell tt 0 sz=Fp.ofNat (rowSize tr tt 0) := by
  have hr : 0<tr.height tt := Nat.two_pow_pos _
  have hh:=h.constr 0 hr UniqueSourceCharge.initial initial_mem
  have ho:=DedupProof.row0 (old_local h)
  have hd:=DedupProof.disjoint (old_local h) hr
  have hrt : tr.cell tt 0 rt=1 := by simpa [shadow,rt,sz] using ho.1
  have hsg : tr.cell tt 0 sg=0 := by
    have hd' : tr.cell tt 0 rt*tr.cell tt 0 sg=0 := by simpa [shadow,rt,sg,sz] using hd
    rw [hrt] at hd';grind
  simp only [UniqueSourceCharge.initial,eval_mul,eval_sub,eval_c,eval_add,eval_k,eval_isFirst,ite_true] at hh
  rw [row_field h hr,hsg]
  grind

theorem prefix_field {tr : Trace Fp} {tt cap r : Nat} {pub : List Fp}
    (h : TableLocal (UniqueSourceCharge.table cap) tr tt pub) (hr : r<tr.height tt) :
    tr.cell tt r sz=Fp.ofNat (prefixSize tr tt (r+1)) := by
  induction r with
  | zero => simpa [prefixSize] using initial_field h
  | succ r ih =>
    rw [step_field h hr,ih (by omega)]
    have he : prefixSize tr tt (r+1+1)=prefixSize tr tt (r+1)+rowSize tr tt (r+1) := by
      simp [prefixSize,List.range_succ,List.map_append,List.sum_append,Nat.add_assoc]
    rw [he,←ofNat_add']
end ZkFormal.NearV3.Candidates.UniqueSourceSoundSize
