import ZkFormal.NearV3.Candidates.ProcPriorIdSoundOrigin
namespace ZkFormal.NearV3.Candidates.ProcPriorIdSoundBound
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorIdTable

/-- Authentication contract for actual public-ID suppliers. It concerns live
physical sends only, not a generated expected inventory. -/
def PublicSendBound (AP : AirP) (tr : Trace Fp) (pub : List Fp) (n : Nat) : Prop :=
  ∀ts,ts<AP.tables.length→∀r,r<tr.height ts→∀i∈AP.tables[ts]!.interactions,
    i.bus=70→i.send=true→i.multNat tr ts r pub≠0→((i.msgVal tr ts r pub)[1]!).toNat<n

theorem public_bound {AP : AirP} {tr : Trace Fp} {pub : List Fp}
    (hH:HoldsP AP pub tr) {ti cmp : Nat} (ht:ti<AP.tables.length)
    (htab:AP.tables[ti]! = (table 70 71 72 cmp)) (n : Nat)
    (hpub:∀msg,pubCount AP pub 70 true msg=0) (hs:PublicSendBound AP tr pub n)
    {r : Nat} (hr:r<tr.height ti) (ha:cv tr ti r act=1) (hp:cv tr ti r isPublic=1) :
    cv tr ti r ordinal<n := by
  let i:Interaction:=(interactions 70 71 72 cmp)[0]!
  have hi:i∈AP.tables[ti]!.interactions:=by rw [htab];simp [i,table,interactions]
  have hm:i.multNat tr ti r pub=1:=Codec.mult_of rfl (by
    simp only [zev_mul,zev_c,cur_cv,ha,hp];rfl)
  have he:(i.msgVal tr ti r pub)[1]! = Fp.ofNat (cv tr ti r ordinal):=by
    simp [i,interactions,Interaction.msgVal,Codec.ev_c]
  rcases recv_src hH ht hr hi (by rfl : i.bus=70) (by rfl : i.send=false) (by omega : i.multNat tr ti r pub≠0) with hbad|hsrc
  · exact (hbad (hpub _)).elim
  · obtain ⟨ts,hts,q,hq,j,hj,hb,hdir,hmsg,hmj⟩:=hsrc
    have hbnd:=hs ts hts q hq j hj hb hdir hmj
    rw [hmsg,he,Fp.toNat_ofNat,Nat.mod_eq_of_lt (show cv tr ti r ordinal<P from cv_lt r ordinal)] at hbnd
    exact hbnd

/-- Arbitrary accepted ID found indices are bounded by the authenticated
public sender ordinals, independently of generated trace completeness. -/
theorem found_bound {AP : AirP} {tr : Trace Fp} {pub : List Fp}
    (hH:HoldsP AP pub tr) {ti cmp : Nat} (ht:ti<AP.tables.length)
    (htab:AP.tables[ti]! = (table 70 71 72 cmp)) (n : Nat)
    (hpub:∀msg,pubCount AP pub 70 true msg=0) (hs:PublicSendBound AP tr pub n)
    {r : Nat} (hr:r<tr.height ti) (ha:cv tr ti r act=1) (hf:cv tr ti r found=1) :
    cv tr ti r index<n := by
  have hL:=local_of_holdsP hH ht
  rw [htab] at hL
  exact ProcPriorIdSoundOrigin.index_bound hL n
    (fun q hq hqa hqp=>public_bound hH ht htab n hpub hs hq hqa hqp) hr ha hf
end ZkFormal.NearV3.Candidates.ProcPriorIdSoundBound
