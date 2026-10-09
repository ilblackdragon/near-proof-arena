import ZkFormal.NearV3.Public.SchedulerIndex
import ZkFormal.NearV3.Assembly.PrepFacts

/-! Root endpoints retain their exact instance indices under actual preparation. -/
namespace ZkFormal.NearV3.Public
open ZkFormal.V2 ZkFormal.Algebra NearSpec NearSpecV3

theorem prep_root_index_lt {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint = .ok p) : p.hdr.K+1 < 256 := by
  have hc := Assembly.prepD0_sched_count hp
  have hl := Sched.prepD0_len hp
  omega

theorem preparedOn_rootPre (p : Prep) :
    preparedOn p B_ROOT true = [[0] ++ p.hdr.prevStateRoot.map UInt8.toNat] := by
  change [(List.map UInt8.toNat ([UInt8.ofNat 0] ++ p.hdr.prevStateRoot))] ++ [] = _
  rw [List.append_nil,List.map_append,List.map_cons,List.map_nil]
  rfl

theorem preparedOn_rootPost (p : Prep) (hk : p.hdr.K+1 < 256) :
    preparedOn p B_ROOT false = [[p.hdr.K+1] ++ p.hdr.postStateRoot.map UInt8.toNat] := by
  change [(List.map UInt8.toNat ([UInt8.ofNat (p.hdr.K+1)] ++ p.hdr.postStateRoot))] ++ [] = _
  rw [List.append_nil,List.map_append,List.map_cons,List.map_nil,UInt8.toNat_ofNat',Nat.mod_eq_of_lt hk]

theorem prepared_root_records {cb : Bytes} {hint : Hint} {p : Prep}
    (hp : prepD0 cb hint = .ok p) :
    preparedOn p B_ROOT true = [[0] ++ p.hdr.prevStateRoot.map UInt8.toNat] ∧
    preparedOn p B_ROOT false = [[p.hdr.K+1] ++ p.hdr.postStateRoot.map UInt8.toNat] :=
  ⟨preparedOn_rootPre p,preparedOn_rootPost p (prep_root_index_lt hp)⟩

theorem prepared_root_index (AP : AirP) {cb : Bytes} {hint : Hint} {p : Prep}
    (witnessOverhead : Nat) (hseg : AP.pubSegs = preparedSegments)
    (hp : prepD0 cb hint = .ok p) (hs : ∀ s ∈ p.lists, s.root.length = 32)
    (hlen : (preparedBytes p witnessOverhead).length < 256^4) :
    let I := prepared_pubIdx AP p witnessOverhead hseg (Assembly.prepD0_roots hp) hs hlen
    I.recs B_ROOT true = [[0] ++ p.hdr.prevStateRoot.map UInt8.toNat] ∧
    I.recs B_ROOT false = [[p.hdr.K+1] ++ p.hdr.postStateRoot.map UInt8.toNat] := by
  dsimp only
  simp only [prepared_pubIdx_recs]
  exact prepared_root_records hp

end ZkFormal.NearV3.Public
