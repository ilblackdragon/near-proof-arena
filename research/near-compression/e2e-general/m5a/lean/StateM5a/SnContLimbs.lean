import StateM5a.SnContMem
import StateM5a.SnLimbsAll

/-!
# StateM5a.SnContLimbs — `SnContMem` from `Holds`

`SnLimbsAll.SnContMem` (the 16-bit memory limbs of the continued-key `SN` rows) discharged:
the bytes behind the limbs are SHA-256 message bytes of the continued head's node
(`SnContMem.cont_old_mem` / `cont_new_mem`).  Premises: `SnRange`'s `hxB hxD hxK`, plus `hxR`
(extra tables do not send on `KCR`) and `hxRr` (extra tables have no `KCR` interaction).
-/

namespace StateM5a.SnContLimbs

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.KeyDecode StateM5a.SnRange StateM5a.SnContMem

/-- **`SnContMem` from `Holds`.** -/
theorem snContMem_of {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
    (hH : Holds (fullAir D extra nb np) pub tr)
    (hxB : XSbHi D extra nb np tr pub)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxR : ∀ T ∈ extra, sendsOn T.interactions B_KCR = false)
    (hxRr : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_KCR) :
    SnLimbsAll.SnContMem tr pub := by
  intro r hr hcont
  refine ⟨fun hg k hk => ?_, fun hg k hk => ?_⟩
  · rw [NM_get k hk]
    exact limbs_of_bytes (cont_new_mem hH hxB hxD hxK hxR hxRr hr hcont hg) k hk
  · rw [M_get k hk]
    exact limbs_of_bytes (cont_old_mem hH hxB hxD hxK hxR hxRr hr hcont hg) k hk

end StateM5a.SnContLimbs
