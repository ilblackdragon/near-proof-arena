import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundRecordBound
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecPublicBound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

/-- Actual corrected Codec records stay inside the authenticated square grid;
its public-ID ordinal therefore stays inside the row's shard count. -/
theorem ordinal_bound (hL:ProcPriorCodecSoundRows.CLocal tr t pub)
    (hh:tr.height t≤2^22)
    (hn:∀r,r<tr.height t→cv tr t r act=1→1≤cv tr t r nn ∧ cv tr t r nn≤64)
    {r : Nat} (hr:r<tr.height t)
    (hm:(Expr.mul (c rs) (c nzb)).eval tr t r pub=1) : cv tr t r srcC<cv tr t r nn := by
  have hgrid:∀q,q<tr.height t→cv tr t q act=1→1≤cv tr t q NN ∧ cv tr t q NN≤4096:=by
    intro q hq ha
    obtain ⟨h1,h64⟩:=hn q hq ha
    rw [ProcPriorCodecSoundRecordBound.active_square hL hq ha h64]
    have hlow:=Nat.mul_le_mul h1 h1
    have hhigh:=Nat.mul_le_mul h64 h64
    omega
  have hs:=ProcPriorCodecSoundGeometry.public_id_start hL hr hm
  have hS:=(ProcPriorCodecSoundGeometry.start hL hr hs).1
  obtain ⟨hR,hA,_⟩:=ProcPriorCodecSoundGeometry.sender_kind hL hr hS
  have hn64:=(hn r hr hA).2
  have hindex:=(ProcPriorCodecSoundIndex.live_index hL hr hh hn64 hm).2
  have hb:=ProcPriorCodecSoundRecordBound.record_bound hL hgrid r hr hR
  rw [ProcPriorCodecSoundRecordBound.active_square hL hr hA hn64,hindex] at hb
  exact Nat.lt_of_mul_lt_mul_right hb
end ZkFormal.NearV3.Candidates.ProcPriorCodecPublicBound
