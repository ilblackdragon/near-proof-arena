import ZkFormal.NearV3.Candidates.NativeValueWf
namespace ZkFormal.NearV3.Candidates.NativeByteFaithfulness
open NearSpec NearSpecV3 ZkFormal.Near Assembly Render.UpsGen

def Canonical (xs : List Nat) : Prop := ∀x∈xs,x<256

theorem decode_encode (xs : List Nat) (h : Canonical xs) :
    (toBytes xs).map UInt8.toNat=xs := by
  unfold toBytes
  rw [List.map_map]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx:=UInt8.toNat_ofNat_of_lt' (h x (by simp))
    have hh:=ih (fun y hy=>h y (by simp [hy]))
    simp only [List.map_cons,Function.comp_apply,hx,hh]

/-- Tagged byte classes do not identify distinct canonical AIR byte strings. -/
theorem faithful (xs ys : List Nat) (hx : Canonical xs) (hy : Canonical ys)
    (he : toBytes xs=toBytes ys) : xs=ys := by
  rw [←decode_encode xs hx,←decode_encode ys hy,he]

theorem mapped_canonical (bs : Bytes) : Canonical (bs.map UInt8.toNat) := by
  intro x hx
  obtain ⟨b,_,rfl⟩:=List.mem_map.mp hx
  exact b.toNat_lt

theorem node_canonical (ts : List PTrie) (hw : ∀t∈ts,t.wf=true)
    (s : NodeS3) (hs : s∈forestNodes 0 0 0 ts) : Canonical (s.v.ser false) := by
  have hm : s.v.ser false∈(forestNodes 0 0 0 ts).map (fun s=>s.v.ser false) :=
    List.mem_map.mpr ⟨s,hs,rfl⟩
  rw [forestNodes_bytes false 0 0 0 ts hw] at hm
  obtain ⟨b,_,he⟩:=List.mem_map.mp hm
  rw [←he]
  exact mapped_canonical _

theorem value_canonical (bs : List Bytes) (e : ValE)
    (he : e∈seedValuesFrom 0 bs) : Canonical e.bytes := by
  rw [seedValuesFrom_zipIdx] at he
  obtain ⟨⟨b,i⟩,_,rfl⟩:=List.mem_map.mp he
  exact mapped_canonical b

/-- Cross-kind duplicate matches preserve the exact physical byte payload. -/
theorem node_value_match (ts : List PTrie) (hw : ∀t∈ts,t.wf=true)
    (s : NodeS3) (hs : s∈forestNodes 0 0 0 ts)
    (e : ValE) (he : e∈seedValuesFrom 0 (forestBytes ts))
    (hb : toBytes (s.v.ser false)=toBytes e.bytes) : s.v.ser false=e.bytes :=
  faithful _ _ (node_canonical ts hw s hs) (value_canonical _ e he) hb
end ZkFormal.NearV3.Candidates.NativeByteFaithfulness
