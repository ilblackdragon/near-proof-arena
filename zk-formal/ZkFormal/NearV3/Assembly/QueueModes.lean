import ZkFormal.NearV3.Assembly.QueueProviders

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Qv

def QueueModesByKey (rs : List ReadRequest) : Prop :=
  ∀ r ∈ rs, ∀ s ∈ rs, r.key=s.key → r.mode=s.mode

theorem mainRequests_modes (pre : PTrie) (v : MainValues) : QueueModesByKey (mainRequests pre v) := by
  intro r hr s hs hk
  simp only [mainRequests,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_map] at hr hs
  rcases hr with (rfl | rfl | rfl) | ⟨a,ha,rfl⟩
  all_goals rcases hs with (rfl | rfl | rfl) | ⟨b,hb,rfl⟩
  all_goals first | rfl | (simp [keyDelayedIdx,keyBufferedIdx,keyYieldIdx,keyGroupsData,nibbles] at hk)

theorem missingRequest_modes (pre : PTrie) : QueueModesByKey [missingRequest pre] := by
  intro r hr s hs hk
  simp only [List.mem_singleton] at hr hs
  subst r
  subst s
  rfl

theorem queueRepresentative_mode {pre : PTrie} {rs : List ReadRequest}
    (hm : QueueModesByKey rs) {b : Bytes} {i : Nat} (hi : (b,i) ∈ queueSelected pre rs)
    {r : ReadRequest} (hr : r ∈ rs) (hv : valueIndex pre r.key = some i) :
    (queueRepresentative pre rs i).mode = r.mode := by
  obtain ⟨hs,hkey⟩ := queueRepresentative_spec hi
  exact hm _ hs r hr (valueIndex_key_unique pre _ _ i hkey hv)

theorem valueIndex_bytes {pre : PTrie} {key : List Nat} {i : Nat} {b : Bytes}
    (hi : valueIndex pre key = some i) (hb : (NearSpecV3.valsOf pre)[i]? = some b) :
    pre.find key = some (some b) := by
  obtain ⟨v,hv⟩ := valueIndex_defined pre key i hi
  obtain ⟨j,hj,hget⟩ := valueIndex_complete pre key v hv
  rw [hi] at hj
  cases hj
  rw [hb] at hget
  cases hget
  exact hv

theorem queueRepresentative_accepts {pre : PTrie} {rs : List ReadRequest}
    (hh : ∀ r ∈ rs, r.Holds pre) {b : Bytes} {i : Nat}
    (hi : (b,i) ∈ queueSelected pre rs) :
    (queueRepresentative pre rs i).mode.Accepts (some b) := by
  obtain ⟨hr,hidx⟩ := queueRepresentative_spec hi
  obtain ⟨hfind,hmode⟩ := hh _ hr
  have hb := valueIndex_bytes hidx (queueSelected_mem.mp hi).1
  rw [hb] at hfind
  have he := Option.some.inj hfind
  rw [← he] at hmode
  exact hmode

theorem queueProviders_accepts {pre : PTrie} {rs : List ReadRequest} {tau base : Nat}
    (hh : ∀ r ∈ rs, r.Holds pre) {p : QueueProvider} (hp : p ∈ queueProviders pre rs tau base) :
    p.mode.Accepts (some p.bytes) := by
  obtain ⟨⟨b,i⟩,hi,rfl⟩ := List.mem_map.mp hp
  exact queueRepresentative_accepts hh hi

end ZkFormal.NearV3.Assembly
