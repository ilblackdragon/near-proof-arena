import ZkFormal.NearV3.Candidates.MerkleRender.Trace
import ZkFormal.NearV3.Candidates.MerkleRender.Public

namespace ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.Near.Render ZkFormal.Near ZkFormal.Air ZkFormal.Algebra

theorem remapped_local (n : Nat) (lv : List (List MNode)) (pub : List Fp)
    (hn1 : 1≤n) (hn : n≤4481)
    (hp : ∀ i<4, pub.getD (PH_N+i) 0=Fp.ofNat (n/256^i%256)) :
    TableLocal MerklePublic.table (trace n lv) T_MRK pub := by
  apply MerklePublic.local_alias.mpr
  apply local19 n lv _ hn1 hn
  have he := MerklePublic.eval_alias (trace n lv) T_MRK 0 pub Mrk.nPubE (by decide +kernel)
  exact he.symm.trans (public_count _ _ _ n pub (by omega) hp)

/-- Both branches of the physical candidate's renderer. Other component traces
are assembled separately; nonempty lift preserves all their table cells. -/
def honestTrace (n : Nat) (lv : List (List MNode)) (pub : List Fp) : Trace Fp :=
  if n=0 then MerkleEmpty.emptyTrace else MerkleEmpty.liftTrace (trace n lv) T_MRK pub

theorem honest_local (n : Nat) (lv : List (List MNode)) (pub : List Fp)
    (hn : n≤4481)
    (hp : ∀ i<4, pub.getD (PH_N+i) 0=Fp.ofNat (n/256^i%256))
    (hz : n=0 → ∀ i<32, pub.getD (PH_OUT+i) 0=0) :
    TableLocal MerkleEmpty.table (honestTrace n lv pub) T_MRK pub := by
  by_cases he : n=0
  · rw [honestTrace,if_pos he]
    apply MerkleEmpty.empty_public_local
    · intro i hi
      rw [hp i hi,he,Nat.zero_div,Nat.zero_mod]
      rfl
    · exact hz he
  · rw [honestTrace,if_neg he]
    apply MerkleEmpty.lift_local (remapped_local n lv pub (by omega) hn hp)
    rw [public_count _ _ _ n pub (by omega) hp]
    exact native_count_nonzero (by omega) hn

/-- Successful native execution supplies the count bound, including the empty
case; no256-receipt restriction is inherited from the old renderer. -/
theorem native_execution_local {ctx : NearSpecV3.ApplyCtx} {t : NearSpec.PTrie}
    {rs : List NearSpec.Receipt} {out : NearSpecV3.MainOut}
    (hr : NearSpecV3.applyNewChunk NearSpecV3.prims ctx t rs=.ok out)
    (hg : ctx.gasLimit≤NearSpecV3.maxGasLimitD0)
    (lv : List (List MNode)) (pub : List Fp)
    (hp : ∀ i<4, pub.getD (PH_N+i) 0=Fp.ofNat (rs.length/256^i%256))
    (hz : rs.length=0 → ∀ i<32, pub.getD (PH_OUT+i) 0=0) :
    TableLocal MerkleEmpty.table (honestTrace rs.length lv pub) T_MRK pub :=
  honest_local rs.length lv pub
    (ZkFormal.NearV3.Assembly.applyNewChunk_receipt_bound hr hg) hp hz

end ZkFormal.NearV3.Candidates.MerkleRender
