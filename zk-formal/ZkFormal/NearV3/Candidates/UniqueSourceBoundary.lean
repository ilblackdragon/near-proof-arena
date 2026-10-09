import ZkFormal.NearV3.Candidates.UniqueSourceCounter
namespace ZkFormal.NearV3.Candidates.UniqueSourceBoundary
open ZkFormal.Near Rcpt.Candidates Render.SrcpGen

/-- First computed dictionary entry pays its complete serialized entry charge. -/
theorem first {bs : List SrcpB} {rep : Nat→Bool} (h : DedupRender.TableFacts bs rep) :
    UniqueSourceRender.counter bs 0=(bs.getD 0 default).L+44 := by
  rw [UniqueSourceCounter.active bs 0 (by have hh:=DedupRender.R_ge_33 h;omega),
    DedupRender.firstAt h]
  simp only [UniqueSourceCounter.amount,h.first_dup,Bool.false_eq_true,ite_false,
    List.take_zero,UniqueSourceCharge.size,List.map_nil,List.sum_nil,Nat.zero_add]

theorem padding (bs : List SrcpB) (r : Nat) (hr : DedupRender.R bs≤r) :
    UniqueSourceRender.counter bs r=UniqueSourceCharge.size bs := by
  simp [UniqueSourceRender.counter,show ¬r<DedupRender.R bs by omega]

/-- The final active row and its padding successor have exactly the same total. -/
theorem terminal (bs : List SrcpB) (hn : bs≠[]) :
    UniqueSourceRender.counter bs (DedupRender.R bs)=
      UniqueSourceRender.counter bs (DedupRender.R bs-1) := by
  rw [padding bs _ (by omega),UniqueSourceCounter.last_counter bs hn]

/-- Increment at a physical row, zero throughout padding. -/
def delta (bs : List SrcpB) (r : Nat) : Nat :=
  if r<DedupRender.R bs then
    let p:=(DedupRender.recs bs).getD r default
    UniqueSourceCounter.increment (bs.getD p.1 default) p.2
  else 0

theorem first_delta {bs : List SrcpB} {rep : Nat→Bool} (h : DedupRender.TableFacts bs rep) :
    UniqueSourceRender.counter bs 0=delta bs 0 := by
  rw [first h]
  have hr : 0<DedupRender.R bs := by have hh:=DedupRender.R_ge_33 h;omega
  simp only [delta,hr,ite_true,DedupRender.firstAt h,UniqueSourceCounter.increment,
    h.first_dup,Bool.false_eq_true,ite_false]

/-- All consecutive physical rows, including the active-to-padding boundary. -/
theorem step (bs : List SrcpB) (r : Nat) :
    UniqueSourceRender.counter bs (r+1)=UniqueSourceRender.counter bs r+delta bs (r+1) := by
  by_cases hn : r+1<DedupRender.R bs
  · simpa only [delta,hn,ite_true] using UniqueSourceCounter.active_step bs r hn
  · simp only [delta,hn,ite_false,Nat.add_zero]
    by_cases hc : r<DedupRender.R bs
    · have he : r=DedupRender.R bs-1 := by omega
      have hb : bs≠[] := by intro h;subst bs;simp [DedupRender.R,DedupRender.recs] at hc
      rw [padding bs (r+1) (by omega),he,UniqueSourceCounter.last_counter bs hb]
    · rw [padding bs (r+1) (by omega),padding bs r (by omega)]

end ZkFormal.NearV3.Candidates.UniqueSourceBoundary
