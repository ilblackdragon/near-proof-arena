import ZkFormal.NearV3.Public.Records
import ZkFormal.NearV3.Rcpt.Ids
import NearSpecV3.PrepD0

/-! Claim-derived receipt source records, in applied order. Equal-key root
consistency is a separate semantic obligation of prepared-statement assembly. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra NearSpecV3

def sourceDup (sources : List SrcList) (j : Nat) : Bool :=
  (sources.take j).any (fun s => s.key == (sources.getD j ⟨[],0,[]⟩).key)

def sourceRow (sources : List SrcList) (j : Nat) : ByteString :=
  [if sourceDup sources j then 1 else 0] ++ (sources.getD j ⟨[],0,[]⟩).root

def sourcePayload (sources : List SrcList) : Payload :=
  (List.range sources.length).map (sourceRow sources)

def sourcePlan : PubSeg :=
  { bus := B_SRC, send := true, width := 33, countAt := 0, start := 0, indexBase := some 0 }

theorem sourcePayload_length (sources : List SrcList) :
    (sourcePayload sources).length = sources.length := by simp [sourcePayload]

theorem sourcePayload_getD (sources : List SrcList) {j : Nat} (hj : j < sources.length) :
    (sourcePayload sources).getD j [] = sourceRow sources j := by
  rw [← List.getElem_eq_getD (h := (show j < (sourcePayload sources).length by
    rw [sourcePayload_length]; exact hj)) []]
  simp only [sourcePayload,List.getElem_map,List.getElem_range]

theorem sourcePayload_width (sources : List SrcList)
    (hr : ∀ s ∈ sources, s.root.length = 32) :
    ∀ row ∈ sourcePayload sources, row.length = sourcePlan.width := by
  intro row hrow
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hrow
  have hj := List.mem_range.mp hj
  have hroot := hr sources[j] (List.getElem_mem hj)
  unfold sourceRow
  rw [← List.getElem_eq_getD (h := hj) ⟨[],0,[]⟩]
  simpa [sourcePlan] using hroot

theorem source_record (sources : List SrcList) {j : Nat} (hj : j < sources.length) :
    recordValues sourcePlan j ((sourcePayload sources).getD j []) =
      [Fp.ofNat j, Fp.ofNat (if sourceDup sources j then 1 else 0)] ++
        (sources.getD j ⟨[],0,[]⟩).root.map byteF := by
  rw [sourcePayload_getD sources hj]
  unfold recordValues sourcePlan sourceRow
  cases sourceDup sources j <;> simp only [Bool.false_eq_true,↓reduceIte,Nat.zero_add,List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append] <;> rfl

theorem descriptor_source_record (header : ByteString) (blocks : List Payload)
    (sources : List SrcList) {i j : Nat} (hi : i < blocks.length)
    (hb : blocks.getD i [] = sourcePayload sources) (hj : j < sources.length)
    (hr : ∀ s ∈ sources, s.root.length = 32)
    (ho : payloadOffset (dataStart header blocks) blocks i < 256^4) :
    (descriptor sourcePlan header.length i).record (ZkFormal.Udr.pubOf Fp (encode header blocks)) j =
      [Fp.ofNat j, Fp.ofNat (if sourceDup sources j then 1 else 0)] ++
        (sources.getD j ⟨[],0,[]⟩).root.map byteF := by
  rw [descriptor_record sourcePlan header blocks hi
    (by rw [hb,sourcePayload_length]; exact hj)
    (by rw [hb]; exact sourcePayload_width sources hr) ho,hb]
  exact source_record sources hj

end ZkFormal.NearV3.Public
