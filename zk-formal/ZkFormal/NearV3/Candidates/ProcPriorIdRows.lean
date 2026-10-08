import ZkFormal.NearV3.Candidates.ProcPriorIdCarryRead
namespace ZkFormal.NearV3.Candidates.ProcPriorIdRows
open NearSpec NearSpec.Bandwidth ProcPriorIds ProcPriorIdValue ProcPriorIdCarry

structure Row where
  event : Event
  before : Value
  deriving DecidableEq, Repr

/-- One linear pass computes every prior-memory row's incoming value. -/
def rowsFrom (s : ProcPriorIdCarry.State) : List Event→List Row
  | []=>[]
  | e::es=>⟨e,atKey s e.key⟩::rowsFrom (step s e) es

def rows (ids : List Nat) (rs : List LinkAllowance) : List Row :=
  rowsFrom ⟨none,zero⟩ (events ids rs)

theorem rowsFrom_length (s : ProcPriorIdCarry.State) (es : List Event) : (rowsFrom s es).length=es.length := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => simp [rowsFrom,ih]

theorem rowsFrom_events (s : ProcPriorIdCarry.State) (es : List Event) : (rowsFrom s es).map (·.event)=es := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => simp [rowsFrom,ih]

theorem row_source (s : ProcPriorIdCarry.State) (es : List Event) (r : Row) (hr:r∈rowsFrom s es) :
    ∃ pre post,es=pre++r.event::post ∧ r.before=atKey (pre.foldl step s) r.event.key := by
  induction es generalizing s with
  | nil => simp [rowsFrom] at hr
  | cons e es ih =>
    simp only [rowsFrom,List.mem_cons] at hr
    rcases hr with rfl|hr
    · exact ⟨[],es,rfl,rfl⟩
    · obtain ⟨pre,post,he,hb⟩:=ih (step s e) hr
      exact ⟨e::pre,post,by simp [he],by simpa only [List.foldl_cons] using hb⟩

/-- Every emitted query row satisfies its read equation by native semantics. -/
theorem query_row (ids : List Nat) (rs : List LinkAllowance) (r : Row)
    (hr:r∈rows ids rs) (hq:r.event.isPublic=false) : r.before=r.event.result := by
  obtain ⟨pre,post,he,hb⟩:=row_source ⟨none,zero⟩ (events ids rs) r hr
  rw [hb]
  exact ProcPriorIdCarryRead.query_carry ids rs pre post r.event he hq

theorem rows_length (ids : List Nat) (rs : List LinkAllowance) :
    (rows ids rs).length=ids.length+2*rs.length := by
  rw [rows,rowsFrom_length]
  exact events_length ids rs

end ZkFormal.NearV3.Candidates.ProcPriorIdRows
