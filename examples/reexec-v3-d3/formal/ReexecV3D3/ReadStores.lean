import ReexecV3D3.ReadPools

/-! Serialized read-set witnesses realize the restricted recorded store. -/
namespace ReexecV3D3.Read
open NearSpec NearSpecV3 NearSpecV3.D2 Logged

/-- Canonical last-wins pools represent the decoded witness's exact lookups. -/
theorem poolStore_init (s : StateWitnessD2) (codes : List Bytes) :
    poolStore (initPools s codes) = storesOfW (mkHStore (s.main.values ++ codes))
      (s.implicit.map fun t => mkHStore t.values) := by
  funext key
  rcases key with ⟨tag, h⟩
  cases tag with
  | zero => exact hGet_poolOf _ h
  | succ k =>
    simp only [poolStore, initPools, storesOfW, List.getElem?_map]
    cases he : s.implicit[k]? with
    | none => rfl
    | some T => exact hGet_poolOf _ h

/-- Relate the pool representation to the actual serialized witness store. -/
theorem poolStore_decoded {w sw : Bytes} {codes : List Bytes} {s : StateWitnessD2}
    (hw : decodeWitnessFile w = .ok (sw, codes))
    (hs : decodeStateWitnessD2 sw = .ok s) :
    poolStore (initPools s codes) = storesOf w := by
  unfold storesOf storesData
  simp only [hw, hs]
  exact poolStore_init s codes

/-- The canonical byte encoder has exactly the store prescribed by its pools. -/
theorem storesOf_encP {cb w sw : Bytes} {codes : List Bytes} {s : StateWitnessD2} {X : Pools}
    (C : Ctx cb w sw codes s X) : storesOf (encP cb sw X) = poolStore X := by
  obtain ⟨sw1, codes1, hw1, s1, hs1, hp, -⟩ := encP_good C
  rw [← poolStore_decoded hw1 hs1, hp]

/-- The serialized normalizer represents precisely the old store restricted to
its supplied read keys, for any successful input and any key list. This does not
yet assert that the re-encoded checker follows the same control flow. -/
theorem storesOf_encodeReads {cb w : Bytes} (h : D3.RelD3 cb w)
    (keys : List (Nat × Bytes)) :
    storesOf (encodeReads cb w keys) = SM.restrict (storesOf w) keys := by
  obtain ⟨sw, codes, s, hw, hs⟩ := checkD3_decoded h
  have C0 := ctx_of hw hs h (SubP.refl (initPools s codes))
  have C := ctx_of hw hs h (restrictPools_sub keys (initPools s codes))
  unfold encodeReads
  simp only [hw, hs]
  rw [storesOf_encP C, poolStore_restrict keys _ C0.g1 C0.g2, poolStore_decoded hw hs]

/-- The normalizer serializes exactly the original execution's recorded store. -/
theorem canonW_store {cb w : Bytes} (h : D3.RelD3 cb w) :
    storesOf (canonW cb w) = SM.restrict (storesOf w) (d3Reads cb w) :=
  storesOf_encodeReads h (d3Reads cb w)

/-- Storage half of completeness: the old checker program keeps its verdict and
read list against the new bytes' store. Re-encoding control flow is a separate
obligation and is not hidden in this statement. -/
theorem canonW_fixedProgram {cb w : Bytes} (h : D3.RelD3 cb w) :
    SM.run (storesOf (canonW cb w)) (D3.checkD3L cb w) = .ok () ∧
      SM.reads (storesOf (canonW cb w)) (D3.checkD3L cb w) = d3Reads cb w := by
  rw [canonW_store h, reads_restrict_eq, reads_fixed]
  exact ⟨h, rfl⟩

/-- With a fixed read set, serialization itself is a byte-level fixed point. -/
theorem encodeReads_idempotent {cb w : Bytes} (h : D3.RelD3 cb w)
    (keys : List (Nat × Bytes)) :
    encodeReads cb (encodeReads cb w keys) keys = encodeReads cb w keys := by
  obtain ⟨sw, codes, s, hw, hs⟩ := checkD3_decoded h
  let X := restrictPools keys (initPools s codes)
  have C : Ctx cb w sw codes s X := ctx_of hw hs h (restrictPools_sub keys _)
  have henc : encodeReads cb w keys = encP cb sw X := by
    unfold encodeReads
    simp only [hw, hs, X]
  obtain ⟨sw1, codes1, hw1, s1, hs1, hp, hstable, -⟩ := encP_good C
  rw [henc]
  unfold encodeReads
  simp only [hw1, hs1]
  rw [hp]
  have hx : restrictPools keys X = X := restrictPools_idempotent keys _
  rw [hx, hstable]

end ReexecV3D3.Read
