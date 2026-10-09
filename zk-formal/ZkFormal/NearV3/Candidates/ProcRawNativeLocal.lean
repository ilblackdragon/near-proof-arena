import ZkFormal.NearV3.Candidates.ProcRawConcatLocal
namespace ZkFormal.NearV3.Candidates.ProcRawNativeLocal
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Assembly.CodecDigest
open ProcRawConcatGeometry ProcRawConcatActive

theorem length_le (bs : List NativeBlock) (b : NativeBlock) (hb:b∈bs) :
    blockLength b≤(rows bs).length := by
  induction bs with
  | nil=>simp at hb
  | cons a bs ih=>
    simp only [rows,List.flatMap_cons,List.length_append,block_length]
    rcases List.mem_cons.mp hb with rfl|hb
    · omega
    · have:=ih hb; change blockLength b≤(bs.flatMap blockRows).length at this; omega

theorem good (bs : List NativeBlock) (hv:∀b∈bs,b.Valid)
    (hcap:(rows bs).length<2^22) : ∀b∈bs,Good b := by
  intro b hb
  have hl:=length_le bs b hb
  unfold blockLength ProcPriorRawSlots.length at hl
  refine ⟨by omega,?_⟩
  intro hp
  have hd:=(hv b hb).2.2.2.1
  cases he:b.prior with
  | none=>rw [he] at hd; exact (Option.some.inj hd).symm
  | some bytes=>simp [he] at hp

theorem table (bs : List NativeBlock) (hv:∀b∈bs,b.Valid)
    (ho:∀(i : Nat)(b : NativeBlock),bs[i]?=some b→b.run.tau=i)
    (hcap:(rows bs).length<2^22) (t pb lb bb sb rb : Nat) (pub : List Fp) :
    TableLocal (ProcPriorRawFrame.table pb lb bb sb rb) (trace bs) t pub := by
  apply ProcRawConcatLocal.table bs (good bs hv hcap) ?_ ?_ hcap
  · intro b rest he
    apply ho 0 b
    simp [he]
  · intro pre b c rest he
    have hb:bs[pre.length]?=some b := by simp [he]
    have hc:bs[pre.length+1]?=some c := by simp [he]
    rw [ho _ b hb,ho _ c hc]
end ZkFormal.NearV3.Candidates.ProcRawNativeLocal
