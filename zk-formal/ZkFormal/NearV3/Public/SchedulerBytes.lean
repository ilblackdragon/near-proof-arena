import ZkFormal.NearV3.Public.SchedulerWidth
import ZkFormal.NearV3.Sched.Link.InitBus
import ZkFormal.NearV3.Sched.Link.ScanPubIdx

/-! Byte range bounds for the scheduler's actual rendered public messages. -/
namespace ZkFormal.NearV3.Public
open Sched

def ByteRow (row : List Nat) : Prop := ∀ n ∈ row, n < 256

theorem byteRow_append (a b : List Nat) (ha : ByteRow a) (hb : ByteRow b) : ByteRow (a++b) := by
  intro n hn
  rcases List.mem_append.mp hn with hn | hn
  · exact ha n hn
  · exact hb n hn

theorem byteRow_b2 (n : Nat) : ByteRow (b2 n) := by
  intro x hx
  simp only [b2,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl <;> omega

theorem byteRow_b3 (n : Nat) : ByteRow (b3 n) := by
  intro x hx
  simp only [b3,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl <;> omega

theorem key_bytes (tau : Nat) (seed : ByteString) (ht : tau < 256) :
    ∀ row ∈ keyRecs tau seed, ByteRow row := by
  intro row hr
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
  have hk := List.mem_range.mp hk
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ht
  · decide
  · omega
  · exact UInt8.toNat_lt _
  · exact UInt8.toNat_lt _
  · decide
  · decide

theorem ash_bytes (tau : Nat) (ash : ByteString) (ht : tau < 256) :
    ∀ row ∈ ashRecs tau ash, ByteRow row := by
  intro row hr
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
  have hk := List.mem_range.mp hk
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ht
  · decide
  · omega
  · exact UInt8.toNat_lt _
  · decide
  · decide
  · decide

theorem fwd_bytes (P : InstPub) (fwd : List (Nat × Nat)) :
    ∀ row ∈ fwdRecs P fwd, ByteRow row := by
  intro row hr
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hr
  apply byteRow_append _ _ (byteRow_append _ _ ?_ (byteRow_b2 _)) (byteRow_b3 _)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl <;> decide

theorem dl_bytes (tau : Nat) (ids : List Nat) (ht : tau < 256) :
    ∀ row ∈ dlRecs tau ids, ByteRow row := by
  intro row hr
  obtain ⟨k,_,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hr
  have ho := List.mem_range.mp ho
  apply byteRow_append _ _ (byteRow_append _ _ ?_ (byteRow_b2 _)) ?_
  · intro x hx; obtain rfl := List.mem_singleton.mp hx; exact ht
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · omega
    · exact Nat.mod_lt _ (by decide)

theorem codec_bytes (tau : Nat) (P : InstPub) (ht : tau < 256) (hn : P.n ≤ 64) :
    ByteRow (parCodec tau P) := by
  unfold parCodec
  apply byteRow_append _ _ (byteRow_append _ _ (byteRow_append _ _ ?_ (byteRow_b2 _)) (byteRow_b3 _)) (byteRow_b3 _)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl <;> omega

theorem scan_bytes (tau : Nat) (P : InstPub) (ht : tau < 256) (hn : P.n ≤ 64) :
    ByteRow (parScan tau P) := by
  unfold parScan
  apply byteRow_append _ _ (byteRow_append _ _ (byteRow_append _ _ ?_ (byteRow_b3 _)) (byteRow_b3 _)) ?_
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact ht
    · decide
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega

theorem raw_bytes (tau : Nat) (P : InstPub) (ht : tau < 256) (hn : P.n ≤ 64) (hr : RawOk P) :
    ∀ row ∈ rawRecs tau P, ByteRow row := by
  intro row hrow
  obtain ⟨⟨q,cid⟩,hq,rfl⟩ := List.mem_map.mp hrow
  have hb := hr.raw q (List.of_mem_zip hq).1
  apply byteRow_append _ _ (byteRow_append _ _ (byteRow_append _ _ ?_ ?_) (byteRow_b2 _)) ?_
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact ht
    · decide
  · intro x hx
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hx
    exact UInt8.toNat_lt _
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> omega

theorem srcFields_bytes (ids : List Nat) (l : Nat) : ByteRow (srcFields ids l) := by
  unfold srcFields
  apply byteRow_append _ _ (byteRow_b2 _) ?_
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl <;> split <;> decide

theorem link_bytes (tau : Nat) (P : InstPub) (ht : tau < 256) :
    ∀ row ∈ linkRecs tau P, ByteRow row := by
  intro row hrow
  obtain ⟨l,_,rfl⟩ := List.mem_map.mp hrow
  apply byteRow_append _ _ (byteRow_append _ _ (byteRow_append _ _ (byteRow_append _ _ ?_ (srcFields_bytes _ _)) ?_) (byteRow_b2 _)) ?_
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    · exact ht
    · decide
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> decide
  · intro x hx
    obtain rfl := List.mem_singleton.mp hx
    unfold InstPub.al
    split <;> decide

theorem shard_bytes (tau : Nat) (P : InstPub) (ht : tau < 256) (hn : P.n ≤ 64) :
    ∀ row ∈ shardRecs tau P, ByteRow row := by
  intro row hrow
  obtain ⟨side,hside,hrow⟩ := List.mem_flatMap.mp hrow
  have hside : side=0 ∨ side=1 := by simpa using hside
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hrow
  have hx := List.mem_range.mp hx
  have hc := cnt_le P.n P.allowed side x
  apply byteRow_append _ _ (byteRow_append _ _ ?_ (byteRow_b3 _)) ?_
  · intro n hn'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn'
    rcases hn' with rfl | rfl | rfl | rfl | rfl
    · exact ht
    · decide
    · omega
    · omega
    · omega
  · intro n hn'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn'
    rcases hn' with rfl | rfl | rfl <;> omega

theorem render_pubb_bytes (Ps : List InstPub) (fwd : List (Nat × Nat))
    (ht : Ps.length ≤ 256) : ∀ row ∈ (render Ps fwd).pubb, ByteRow row := by
  intro row hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨tau,htau,hr⟩ := List.mem_flatMap.mp hr
    have htau := List.mem_range.mp htau
    rcases List.mem_append.mp hr with hr | hr
    · exact key_bytes _ _ (by omega) row hr
    · exact ash_bytes _ _ (by omega) row hr
  · exact fwd_bytes _ _ row hr

theorem render_par_bytes (Ps : List InstPub) (fwd : List (Nat × Nat))
    (ht : Ps.length ≤ 256)
    (hP : ∀ tau, tau < Ps.length → (Ps.getD tau instD).n ≤ 64 ∧ RawOk (Ps.getD tau instD)) :
    ∀ row ∈ (render Ps fwd).par, ByteRow row := by
  intro row hr
  obtain ⟨tau,htau,hr⟩ := List.mem_flatMap.mp hr
  have htau := List.mem_range.mp htau
  obtain ⟨hn,hraw⟩ := hP tau htau
  have htau' : tau < 256 := by omega
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · rcases List.mem_append.mp hr with hr | hr
        · obtain rfl := List.mem_singleton.mp hr
          exact codec_bytes _ _ htau' hn
        · split at hr
          · simp at hr
          · obtain rfl := List.mem_singleton.mp hr
            exact scan_bytes _ _ htau' hn
      · exact raw_bytes _ _ htau' hn hraw row hr
    · exact shard_bytes _ _ htau' hn row hr
  · exact link_bytes _ _ htau' row hr

end ZkFormal.NearV3.Public
