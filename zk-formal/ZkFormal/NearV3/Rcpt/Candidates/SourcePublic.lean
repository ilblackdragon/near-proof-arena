import ZkFormal.NearV3.Rcpt.Candidates.SourceRepetition

/-! Candidate SRC34 public descriptor only. Active SRC33 and protocol pins are
unchanged; candidate assembly must choose this schema explicitly. -/
namespace ZkFormal.NearV3.Rcpt.Candidates.SourcePublic
open ZkFormal.V2 ZkFormal.Algebra NearSpecV3 ZkFormal.NearV3.Public
def row (sources : List SrcList) (j : Nat) : ByteString :=
  [if Public.sourceDup sources j then 1 else 0, if sourceRepeated sources j then 1 else 0] ++ (sources.getD j ⟨[],0,[]⟩).root

def payload (sources : List SrcList) : Payload :=
  (List.range sources.length).map (row sources)

def plan : PubSeg :=
  { bus := B_SRC, send := true, width := 34, countAt := 0, start := 0, indexBase := some 0 }

theorem payload_length (sources : List SrcList) :
    (payload sources).length = sources.length := by simp [payload]

theorem payload_getD (sources : List SrcList) {j : Nat} (hj : j < sources.length) :
    (payload sources).getD j [] = row sources j := by
  rw [← List.getElem_eq_getD (h := (show j < (payload sources).length by
    rw [payload_length]; exact hj)) []]
  simp only [payload,List.getElem_map,List.getElem_range]

theorem payload_width (sources : List SrcList)
    (hr : ∀ s ∈ sources, s.root.length = 32) :
    ∀ row ∈ payload sources, row.length = plan.width := by
  intro row hrow
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hrow
  have hj := List.mem_range.mp hj
  have hroot := hr sources[j] (List.getElem_mem hj)
  unfold row
  rw [← List.getElem_eq_getD (h := hj) ⟨[],0,[]⟩]
  simpa [plan] using hroot

theorem record (sources : List SrcList) {j : Nat} (hj : j < sources.length) :
    recordValues plan j ((payload sources).getD j []) =
      [Fp.ofNat j, Fp.ofNat (if Public.sourceDup sources j then 1 else 0), Fp.ofNat (if sourceRepeated sources j then 1 else 0)] ++
        (sources.getD j ⟨[],0,[]⟩).root.map byteF := by
  rw [payload_getD sources hj]
  unfold recordValues plan row
  cases Public.sourceDup sources j <;> cases sourceRepeated sources j <;> simp only [Bool.false_eq_true,↓reduceIte,Nat.zero_add,List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append] <;> rfl

theorem descriptor_source_record (header : ByteString) (blocks : List Payload)
    (sources : List SrcList) {i j : Nat} (hi : i < blocks.length)
    (hb : blocks.getD i [] = payload sources) (hj : j < sources.length)
    (hr : ∀ s ∈ sources, s.root.length = 32)
    (ho : payloadOffset (dataStart header blocks) blocks i < 256^4) :
    (descriptor plan header.length i).record (ZkFormal.Udr.pubOf Fp (encode header blocks)) j =
      [Fp.ofNat j, Fp.ofNat (if Public.sourceDup sources j then 1 else 0), Fp.ofNat (if sourceRepeated sources j then 1 else 0)] ++
        (sources.getD j ⟨[],0,[]⟩).root.map byteF := by
  rw [Public.descriptor_record plan header blocks hi
    (by rw [hb,payload_length]; exact hj)
    (by rw [hb]; exact payload_width sources hr) ho,hb]
  exact record sources hj

end ZkFormal.NearV3.Rcpt.Candidates.SourcePublic
