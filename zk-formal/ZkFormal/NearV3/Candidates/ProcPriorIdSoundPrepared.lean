import ZkFormal.NearV3.Candidates.ProcPriorIdSoundResult
import ZkFormal.NearV3.Sched.Link.SoundPrep
namespace ZkFormal.NearV3.Candidates.ProcPriorIdSoundPrepared
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha
open ZkFormal.NearV3.Sched ProcPriorIdSoundBound ProcPriorIdSoundResult

/-- Every live public-ID supplier must be authenticated to an actual prepared
layout slot. Establishing this from the corrected Codec/public buses is a
separate soundness obligation; this is deliberately not a generation premise. -/
def Authenticated (AP : AirP) (tr : Trace Fp) (pub : List Fp) (p : NearSpecV3.Prep) : Prop :=
  ∀ts,ts<AP.tables.length→∀r,r<tr.height ts→∀i∈AP.tables[ts]!.interactions,
    i.bus=70→i.send=true→i.multNat tr ts r pub≠0→
    ∃sp∈p.sched,∃j,j<sp.ids.length ∧ (i.msgVal tr ts r pub)[1]! = Fp.ofNat j

theorem public64 {AP : AirP} {tr : Trace Fp} {pub : List Fp}
    {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p) (ha:Authenticated AP tr pub p) :
    PublicSendBound AP tr pub 64 := by
  intro ts ht r hr i hi hb hs hm
  obtain ⟨sp,hsp,j,hj,he⟩:=ha ts ht r hr i hi hb hs hm
  have hn:=(prepD0_sched hp sp hsp).n64
  have hP:64<P:=by decide +kernel
  have hjP:j<P:=by omega
  rw [he,Fp.toNat_ofNat,Nat.mod_eq_of_lt hjP]
  omega

theorem result64 {AP : AirP} {tr : Trace Fp} {pub : List Fp}
    (hH:HoldsP AP pub tr) {ti cmp : Nat} (own:Own AP ti cmp) (hcmp:cmp≠72)
    {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hp:NearSpecV3.prepD0 cb hint=.ok p) (ha:Authenticated AP tr pub p)
    (hpub70:∀msg,pubCount AP pub 70 true msg=0) (hpub72:∀msg,pubCount AP pub 72 true msg=0)
    {tc r : Nat} (ht:tc<AP.tables.length) (hr:r<tr.height tc) {i : Interaction}
    (hi:i∈AP.tables[tc]!.interactions) (hb:i.bus=72) (hs:i.send=false)
    (hm:i.multNat tr tc r pub≠0) (hf:(i.msgVal tr tc r pub)[2]! = Fp.ofNat 1) :
    ((i.msgVal tr tc r pub)[3]!).toNat<64 :=
  result_bound hH own hcmp 64 hpub70 (public64 hp ha) hpub72 ht hr hi hb hs hm hf
end ZkFormal.NearV3.Candidates.ProcPriorIdSoundPrepared
