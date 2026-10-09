import ZkFormal.NearV3.Qv.Extract.WalkCountRequest
import ZkFormal.NearV3.Qv.Extract.NativeShardLookup

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl
open Candidates.CombinedTable

variable {tr : Trace Fp} {tt : Nat} {pub : List Fp}
variable (hL : TableLocal table tr tt pub)
include hL

/-- A shard byte request is never the key header. -/
theorem shard_request_not_first {r : Nat} (hr : r<tr.height tt)
    (hg : tr.cell tt r groupByte=1) : tr.cell tt r wf=0 := by
  have hh := con hL hr (e:=sub (c groupByte) (mul3 (c walk) group (Dsl.not (c wf))))
    (by simp [constraints])
  simp only [eval_sub,eval_c,eval_mul3,eval_not,hg] at hh
  rcases isBool hL hr (x:=wf) (by simp [walkBools]) with hw|hw
  · exact hw
  · rw [hw] at hh
    grind

/-- Every physical shard-byte request has a canonical byte position0..7. -/
theorem shard_request_position {s n r : Nat} (hfit : s+n≤tr.height tt)
    (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s n)
    (hr : s≤r) (hb : r<s+n) (hg : tr.cell tt r groupByte=1) :
    ∃ i : Nat, i<8 ∧ tr.cell tt r wp-1=(i:Fp) := by
  have hn := walk_length hL hfit hs
  have hf := shard_request_not_first hL (by omega) hg
  have hfirst : tr.cell tt s wf=1 := by
    simpa only [isOne,decide_eq_true_eq] using hs.2.1
  have hne : r≠s := by
    intro he
    rw [he,hfirst] at hf
    exact (by decide : (1:Fp)≠0) hf
  have hpos := walk_position hL hfit hs r hr hb
  have he : r-s=(r-s-1)+1 := by omega
  rw [he,natCast_add,Lean.Grind.Semiring.natCast_one] at hpos
  refine ⟨r-s-1,by omega,?_⟩
  grind

/-- The byte gate cannot supply the count-packet position8. -/
theorem shard_request_not_count {s n r : Nat} (hfit : s+n≤tr.height tt)
    (hs : IsSeg (isOne tr tt walk) (isOne tr tt wf) (isOne tr tt wl) s n)
    (hr : s≤r) (hb : r<s+n) (hg : tr.cell tt r groupByte=1) :
    tr.cell tt r wp-1≠8 := by
  obtain ⟨i,hi,he⟩ := shard_request_position hL hfit hs hr hb hg
  intro hx
  rw [he] at hx
  have hn := congrArg Fp.toNat hx
  change (Fp.ofNat i).toNat=(8:Fp).toNat at hn
  have hp : 8<P := by decide
  have h8 : (8:Fp).toNat=8 := by decide
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (show i<P by omega),h8] at hn
  omega

end ZkFormal.NearV3.Qv.Extract
