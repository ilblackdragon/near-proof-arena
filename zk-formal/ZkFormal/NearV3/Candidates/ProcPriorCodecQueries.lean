import ZkFormal.NearV3.Candidates.ProcPriorEvents
import ZkFormal.NearV3.Candidates.ProcPriorCodecGen
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecQueries
open NearSpec.Bandwidth ProcPriorEvents ProcPriorSummary

/-- Semantic payload of the repaired Codec priorRead. Physical row enumeration
is a separate obligation; this inventory keeps every native grid query. -/
def queries (tau : Nat) (ids : List Nat) (st : State) : List (List Nat) :=
  (List.range (ids.length*ids.length)).map fun l =>
    let v := (ProcActualInput.allowances ids st)[l]!
    [tau,l,low v,if big v then 1 else 0]

def message (tau : Nat) (e : Event) : List Nat :=
  [tau,e.link,e.lo,if e.hi then 1 else 0]

/-- Exact native lookup agrees with the last-original-record memory inventory,
including unknown endpoint IDs and repeated original records. -/
theorem native_queries (tau : Nat) (ids : List Nat) (st : State) :
    queries tau ids st = (queryEvents ids st.links).map (message tau) := by
  unfold queries queryEvents
  rw [List.map_map]
  apply List.map_congr_left
  intro l hl
  have hk := List.mem_range.mp hl
  have hv := ProcPriorWinner.allowance_winner ids st l hk
  have hs : l < (ProcActualInput.allowances ids st).size := by
    rw [ProcActualInput.allowances_size]; exact hk
  rw [Array.getElem?_eq_getElem hs] at hv
  have he := Option.some.inj hv
  simp only [getElem!_pos (ProcActualInput.allowances ids st) l hs,he,
    Function.comp_apply,message]

theorem query_count (tau : Nat) (ids : List Nat) (st : State) :
    (queries tau ids st).length = ids.length*ids.length := by
  simp [queries]

/-- An absent original value uses the native empty link dictionary; it is not
required to contain a canonical square of zero records. -/
theorem empty_queries (tau : Nat) (ids : List Nat) (hash : List UInt8) :
    queries tau ids ⟨[],hash⟩ =
      (List.range (ids.length*ids.length)).map (fun l => [tau,l,0,0]) := by
  unfold queries
  apply List.map_congr_left
  intro l hl
  have hk := List.mem_range.mp hl
  simp [ProcActualInput.allowances,low,big,hk]

end ZkFormal.NearV3.Candidates.ProcPriorCodecQueries
