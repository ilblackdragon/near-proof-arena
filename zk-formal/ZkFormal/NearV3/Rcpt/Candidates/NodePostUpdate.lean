import ZkFormal.NearV3.Rcpt.Candidates.NativeShaJobs

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.Near NearSpec

/-- Concrete final byte payloads, indexed by existing global node/value IDs. -/
structure Inputs where
  child : Nat→Bytes
  value : Nat→Option Bytes

def digest (b : Bytes) : List Nat := (ArenaCore.sha256 b).map UInt8.toNat

def kid (u : Inputs) : NKid→NKid
  | .none => .none
  | .hash h => .hash h
  | .node c l r pre _ => .node c l r pre (digest (u.child c))

def slot (u : Inputs) : NSlot3→NSlot3
  | .ref l h => .ref l h
  | .val l i n pre po w => match u.value i with
    | none => .val l i n pre po w
    | some b => .val l i n pre (digest b) true

def node (u : Inputs) : NodeV3→NodeV3
  | .leaf k v m => .leaf k (slot u v) m
  | .ext k c m => .ext k (kid u c) m
  | .branch v cs m => .branch (v.map (slot u)) (cs.map (kid u)) m

def record (u : Inputs) (s : NodeS3) : NodeS3 := {s with v:=node u s.v}
def records (u : Inputs) (ss : List NodeS3) : List NodeS3 := ss.map (record u)

theorem digest_length (b : Bytes) : (digest b).length=32 := by
  simp [digest,ArenaCore.sha256_length]

theorem digest_byte (b : Bytes) (x : Nat) (h : x∈digest b) : x<256 := by
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp h
  exact v.toNat_lt

theorem kid_present (u : Inputs) (k : NKid) : (kid u k).present=k.present := by
  cases k <;> rfl

theorem kid_pre (u : Inputs) (k : NKid) : (kid u k).bytes false=k.bytes false := by
  cases k <;> rfl

theorem slot_pre (u : Inputs) (s : NSlot3) : (slot u s).bytes false=s.bytes false := by
  cases s with
  | ref l h => rfl
  | val l i n pre po w => simp only [slot]; split <;> rfl

theorem kid_wf (u : Inputs) (k : NKid) (h : k.wf) : (kid u k).wf := by
  cases k <;> simp_all [kid,NKid.wf,digest_length]

theorem slot_wf (u : Inputs) (s : NSlot3) (h : s.wf) : (slot u s).wf := by
  cases s with
  | ref l hh => exact h
  | val l i n pre po w =>
    cases hu : u.value i with
    | none => simpa [slot,hu] using h
    | some b =>
      simp only [slot,hu]
      exact ⟨h.1,h.2.1,digest_length b,by simp,h.2.2.2.2⟩

theorem bitmap (u : Inputs) (ks : List NKid) : kidBitmap (ks.map (kid u))=kidBitmap ks := by
  simp only [kidBitmap,List.length_map,List.zip_map_left,List.map_map,Function.comp_def,Prod.map,kid_present,id_eq]

theorem node_pre (u : Inputs) (v : NodeV3) : (node u v).ser false=v.ser false := by
  cases v with
  | leaf k v m => simp [node,NodeV3.ser,slot_pre]
  | ext k c m => simp [node,NodeV3.ser,kid_pre]
  | branch v cs m =>
    cases v <;> simp [node,NodeV3.ser,bitmap,List.flatMap_map,kid_pre,slot_pre]

theorem node_wf (u : Inputs) (v : NodeV3) (h : v.wf) : (node u v).wf := by
  cases v with
  | leaf k v m => exact ⟨h.1,slot_wf u v h.2.1,h.2.2⟩
  | ext k c m =>
    refine ⟨h.1,?_,kid_wf u c h.2.2.1,h.2.2.2⟩
    cases c <;> simp_all [kid,NodeV3.wf]
  | branch v cs m =>
    refine ⟨by simpa using h.1,?_,?_,h.2.2.2⟩
    · intro s hs
      cases hv : v with
      | none => simp [hv] at hs
      | some s' =>
        have he : slot u s'=s := by simpa [hv] using hs
        rw [←he]
        exact slot_wf u s' (h.2.1 s' hv)
    · intro c hc
      obtain ⟨c',hc',rfl⟩ := List.mem_map.mp hc
      exact kid_wf u c' (h.2.2.1 c' hc')

theorem records_pre (u : Inputs) (ss : List NodeS3) :
    (records u ss).map (fun s => s.v.ser false)=ss.map (fun s => s.v.ser false) := by
  simp [records,record,List.map_map,node_pre]

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
