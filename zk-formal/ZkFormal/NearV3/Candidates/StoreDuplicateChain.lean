import ZkFormal.NearV3.Candidates.NativeByteFaithfulness
namespace ZkFormal.NearV3.Candidates.StoreDuplicateChain
open ZkFormal.Near StoreDuplicateMetadata

/-- One equal-byte class in UNIQ order. Only its first record is charged;
all later records refer to the preceding entity, and all but the last provide
bytes to their successor. This differs from a star around the first record. -/
structure Entry where
  eid : Nat
  dup : Bool
  hd : Bool
  repE : Nat
  deriving Repr, DecidableEq

def tailEntries (prev : Nat) : List Nat→List Entry
  | [] => []
  | e::es => ⟨e,true,!es.isEmpty,prev⟩::tailEntries e es

def entries : List Nat→List Entry
  | [] => []
  | e::es => ⟨e,false,!es.isEmpty,0⟩::tailEntries e es

def sends (xs : List Entry) (payload : List Msg) : List Msg :=
  xs.flatMap fun e=>if e.hd then payload.map (e.eid::·) else []
def recvs (xs : List Entry) (payload : List Msg) : List Msg :=
  xs.flatMap fun e=>if e.dup then payload.map (e.repE::·) else []

private theorem tail_balance (prev : Nat) (ids : List Nat) (payload : List Msg) :
    recvs (tailEntries prev ids) payload=
      (if ids.isEmpty then [] else payload.map (prev::·))++sends (tailEntries prev ids) payload := by
  induction ids generalizing prev with
  | nil => simp [tailEntries,sends,recvs]
  | cons e es ih =>
    simp only [tailEntries,recvs,sends,List.flatMap_cons,Bool.not_eq_true',Bool.true_eq,ite_true]
    have hh:=ih e
    cases es <;> simp_all [tailEntries,recvs,sends,List.append_assoc]

/-- Exact ENT conservation for a byte class of any multiplicity, including
singleton and empty classes. Payload may include the empty-value marker. -/
theorem ent_balance (ids : List Nat) (payload : List Msg) :
    sends (entries ids) payload=recvs (entries ids) payload := by
  cases ids with
  | nil => simp [entries,sends,recvs]
  | cons e es =>
    have hh:=tail_balance e es payload
    cases es <;> simpa [entries,sends,recvs,tailEntries] using hh.symm

private theorem tail_nondup (prev : Nat) (ids : List Nat) :
    (tailEntries prev ids).filter (fun e=>!e.dup)=[] := by
  induction ids generalizing prev with
  | nil => rfl
  | cons e es ih => simp [tailEntries,ih]

/-- Chain metadata retains exactly the same one-record-per-class charge. -/
theorem nondup_count (ids : List Nat) :
    ((entries ids).filter fun e=>!e.dup).length=if ids.isEmpty then 0 else 1 := by
  cases ids <;> simp [entries,tail_nondup]

private theorem tail_ids (prev : Nat) (ids : List Nat) :
    (tailEntries prev ids).map Entry.eid=ids := by
  induction ids generalizing prev with
  | nil => rfl
  | cons e es ih => simp [tailEntries,ih]

theorem entity_ids (ids : List Nat) : (entries ids).map Entry.eid=ids := by
  cases ids <;> simp [entries,tail_ids]

def links : List Nat→List Msg
  | a::b::rest => [b,a]::links (b::rest)
  | _ => []

private theorem tail_links (prev : Nat) (ids : List Nat) :
    ((tailEntries prev ids).filter (fun e=>e.dup)).map (fun e=>[e.eid,e.repE])=links (prev::ids) := by
  induction ids generalizing prev with
  | nil => rfl
  | cons e es ih => simp [tailEntries,links,ih]

/-- DUP receivers exactly follow UNIQ's immediate-predecessor convention. -/
theorem dup_links (ids : List Nat) :
    ((entries ids).filter (fun e=>e.dup)).map (fun e=>[e.eid,e.repE])=links ids := by
  cases ids <;> simp [entries,links,tail_links]
end ZkFormal.NearV3.Candidates.StoreDuplicateChain
