import ZkFormal.NearV3.Candidates.ProcPriorCodecActual
import ZkFormal.NearV3.Sched.View.CodecStep
import ZkFormal.Near.Extract.Common
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundRows
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec

abbrev CLocal (tr : Trace Fp) (t : Nat) (pub : List Fp) : Prop :=
  Local ProcPriorCodecActual.constraints tr t pub

theorem table_constraints {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h:ZkFormal.Near.TableLocal ProcPriorCodecActual.table tr t pub) : CLocal tr t pub := h.constr

theorem member_sender_byte : .mul (c fS) (sub (c bpost) (c (prbit 0)))∈ProcPriorCodecActual.constraints := by
  simp [ProcPriorCodecActual.constraints,ProcPriorCodecActual.additions,ProcPriorCodecActual.idByte]

theorem member_sender_shift (i : Nat) (hi:i<7) :
    mul3 (c fS) (notE (c e7)) (sub (n (prbit i)) (c (prbit (i+1))))∈ProcPriorCodecActual.constraints := by
  apply List.mem_append_right
  unfold ProcPriorCodecActual.additions
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩


/-- Arbitrary satisfying corrected traces, without a generator hypothesis,
identify the sender post-byte with the shifted sender-ID register head. -/
theorem sender_byte {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:CLocal tr t pub) {r : Nat} (hr:r<tr.height t) (hS:cv tr t r fS=1) :
    cv tr t r bpost=cv tr t r (prbit 0) := by
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr member_sender_byte
  zs hq [hS]
  have := Codec.lt (tr:=tr) (t:=t) r bpost
  have := Codec.lt (tr:=tr) (t:=t) r (prbit 0)
  omega

/-- The seven actual added shift equations extract native register equality,
not just equality modulo the field, on any nonterminal sender byte. -/
theorem sender_shift {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:CLocal tr t pub) {r : Nat} (hr:r<tr.height t) (hr1:r+1<tr.height t)
    (hS:cv tr t r fS=1) (h7:cv tr t r e7=0) (i : Nat) (hi:i<7) :
    cv tr t (r+1) (prbit i)=cv tr t r (prbit (i+1)) := by
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (member_sender_shift i hi)
  zs hq [hS,h7,nx hr1]
  have := Codec.lt (tr:=tr) (t:=t) (r+1) (prbit i)
  have := Codec.lt (tr:=tr) (t:=t) r (prbit (i+1))
  omega

/-- The repaired codec no longer re-encodes original allowance bytes: its
allowance pre-byte is zero, and original values must come from the prior bus. -/
theorem allowance_pre_zero {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:CLocal tr t pub) {r : Nat} (hr:r<tr.height t) (hA:cv tr t r fA=1) :
    cv tr t r bpre=0 := by
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (show .mul (c fA) (c bpre)∈ProcPriorCodecActual.constraints by simp [ProcPriorCodecActual.constraints,ProcPriorCodecActual.additions])
  zs hq [hA]
  have := Codec.lt (tr:=tr) (t:=t) r bpre
  omega
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundRows
