import ZkFormal.NearV3.Rcpt.Candidates.SizeCountTables
import ZkFormal.NearV3.Rcpt.Candidates.NativeDigestJobs
import ZkFormal.NearV3.Candidates.TrieCountHeight

namespace ZkFormal.NearV3.Rcpt.Candidates.EmptyValue
open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

/-- This constant is the specified SHA function applied to the empty byte list,
not an additional hash axiom or a free witness cell. -/
def emptyHash : List Nat := (NearSpec.sha256 []).map UInt8.toNat

def emptyInteraction : Interaction :=
  send B_DIGEST (c ValV3.vz) ([mid K_VPRE (c ValV3.vid),k 0]++emptyHash.map k)

/-- Isolated candidate repair. Empty values retain a single physical row and
one digest supplier per value occurrence. All previous constraints are identical. -/
def table : ZkFormal.Air.Table :=
  {SizeCount.valTable with interactions := SizeCount.valTable.interactions++[emptyInteraction]}

theorem constraints_eq : table.constraints=SizeCount.valTable.constraints := rfl

theorem local_iff (tr : Trace ZkFormal.Algebra.Fp) (t : Nat) (pub : List ZkFormal.Algebra.Fp) :
    TableLocal table tr t pub ↔ TableLocal SizeCount.valTable tr t pub := by
  constructor
  · intro h
    exact ⟨h.log_ge,h.log_le,h.constr,fun r hr i hi b hb=>
      h.bits r hr i (List.mem_append_left _ hi) b hb⟩
  · intro h
    refine ⟨h.log_ge,h.log_le,h.constr,?_⟩
    intro r hr i hi b hb
    rcases List.mem_append.mp hi with hi|hi
    · exact h.bits r hr i hi b hb
    · have hi' : i=emptyInteraction := by simpa using hi
      subst i
      have hb' : b=c ValV3.vz := by simpa [emptyInteraction,send] using hb
      subst b
      have he:=h.constr r hr (bool (c ValV3.vz)) (by
        simp [SizeCount.valTable,ValV3.constraints])
      have h1 : ((1 : Nat) : ZkFormal.Algebra.Fp)=(1 : ZkFormal.Algebra.Fp) := by decide +kernel
      exact bool_cases (by simpa [Dsl.bool,h1] using he)

theorem complete (es : List ValE) (h : Render.ValOk es) (t : Nat)
    (pub : List ZkFormal.Algebra.Fp) :
    TableLocal table (Candidates.TrieCountHeight.value es pub) t pub :=
  (local_iff _ _ _).mpr (Candidates.TrieCountHeight.value_local es h t pub)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem shape : ZkFormal.Size.shapeOf 2 table=ZkFormal.Size.V3.sh 16 4 5 4 22 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem wellformed : table.wf ⟨[table],65,202⟩ 4=true := by
  decide +kernel

theorem same_shape : ZkFormal.Size.shapeOf 2 table=ZkFormal.Size.shapeOf 2 SizeCount.valTable :=
  shape.trans SizeCount.candidate_shapes.2.1.symm

end ZkFormal.NearV3.Rcpt.Candidates.EmptyValue
