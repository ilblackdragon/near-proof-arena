import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundGeometry
import ZkFormal.NearV3.Candidates.ProcPriorIdLimbs
import ZkFormal.NearV3.Sched.View.CodecEnc
import ZkFormal.NearV3.Sched.Link.SoundPrep
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundPublicId
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec

theorem packed_eval (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    ProcPriorCodecActual.idLo.eval tr t r pub=Fp.ofNat (cv tr t r (prbit 0)+256*cv tr t r (prbit 1)+65536*cv tr t r (prbit 2)) ∧
    ProcPriorCodecActual.idMid.eval tr t r pub=Fp.ofNat (cv tr t r (prbit 3)+256*cv tr t r (prbit 4)+65536*cv tr t r (prbit 5)) ∧
    ProcPriorCodecActual.idHi.eval tr t r pub=Fp.ofNat (cv tr t r (prbit 6)+256*cv tr t r (prbit 7)) := by
  refine ⟨?_,?_,?_⟩
  all_goals apply ev_of
  all_goals simp only [ProcPriorCodecActual.idLo,ProcPriorCodecActual.idMid,ProcPriorCodecActual.idHi,
    ProcPriorCodecActual.idByte,zev_add,zev_smul,zev_c,cur_cv,Int.natCast_add,Int.natCast_mul]
  all_goals omega

theorem nat_eq (a b : Nat) (ha:a<P) (hb:b<P) (h:Fp.ofNat a=Fp.ofNat b) : a=b := by
  have he:=congrArg Fp.toNat h
  simpa only [Fp.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using he

/-- A live publicID row whose three packed limbs match an explicit expected
64-bit ID has exactly that ID's eight little-endian post bytes. The payload
equality is the ownership/global-balance obligation, left explicit here. -/
theorem sender_bytes {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat} (hr:r<tr.height t)
    (hm:(Expr.mul (c rs) (c nzb)).eval tr t r pub=1)
    (id tauV sender : Nat) (hid:id<2^64)
    (hp:ProcPriorCodecActual.publicId.msg.map (fun e=>e.eval tr t r pub)=
      [Fp.ofNat tauV,Fp.ofNat sender,Fp.ofNat (ProcPriorIdLimbs.lo id),
       Fp.ofNat (ProcPriorIdLimbs.mid id),Fp.ofNat (ProcPriorIdLimbs.hi id)]) :
    r+7<tr.height t ∧ ∀i,i<8→cv tr t (r+i) bpost=((NearSpec.u64 id).getD i 0).toNat := by
  have hs:=ProcPriorCodecSoundGeometry.public_id_start hL hr hm
  obtain ⟨hr7,hbytes,hlo,hmid,hhi⟩:=ProcPriorCodecSoundGeometry.start_bytes hL hr hs
  obtain ⟨el,em,eh⟩:=packed_eval tr t r pub
  have pl:=congrArg (fun xs:List Fp=>xs[2]!) hp
  have pm:=congrArg (fun xs:List Fp=>xs[3]!) hp
  have ph:=congrArg (fun xs:List Fp=>xs[4]!) hp
  simp only [ProcPriorCodecActual.publicId,List.map_cons,List.map_nil,List.getElem!_cons_succ,List.getElem!_cons_zero] at pl pm ph
  rw [el] at pl
  rw [em] at pm
  rw [eh] at ph
  have ib:=ProcPriorIdLimbs.bounds id hid
  have hP:2^24<P := by decide +kernel
  have hl:=nat_eq _ _ (by omega) (by omega) pl
  have hmd:=nat_eq _ _ (by omega) (by omega) pm
  have hh:=nat_eq _ _ (by omega) (by omega) ph
  have hn:=ProcPriorIdLimbs.reconstruct id
  have h0:=(hbytes 0 (by decide)).2
  have h1:=(hbytes 1 (by decide)).2
  have h2:=(hbytes 2 (by decide)).2
  have h3:=(hbytes 3 (by decide)).2
  have h4:=(hbytes 4 (by decide)).2
  have h5:=(hbytes 5 (by decide)).2
  have h6:=(hbytes 6 (by decide)).2
  have h7:=(hbytes 7 (by decide)).2
  refine ⟨hr7,?_⟩
  intro i hi
  rw [←(hbytes i hi).1]
  unfold NearSpec.u64
  rw [leN_getD 8 id i hi]
  have hi':i=0∨i=1∨i=2∨i=3∨i=4∨i=5∨i=6∨i=7 := by omega
  rcases hi' with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals omega
/-- Instantiate the explicit payload match with the actual prepared layout.
The 64-bit ID bound follows from successful preparation, including duplicates. -/
theorem prepared_sender_bytes {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat} (hr:r<tr.height t)
    (hm:(Expr.mul (c rs) (c nzb)).eval tr t r pub=1)
    {cb : NearSpec.Bytes} {hint : NearSpecV3.Hint} {p : NearSpecV3.Prep}
    (hprep:NearSpecV3.prepD0 cb hint=.ok p) (sp : NearSpecV3.Scheduler.SchedPub) (hsp:sp∈p.sched)
    (tauV sender : Nat) (hsender:sender<sp.ids.length)
    (hp:ProcPriorCodecActual.publicId.msg.map (fun e=>e.eval tr t r pub)=
      [Fp.ofNat tauV,Fp.ofNat sender,Fp.ofNat (ProcPriorIdLimbs.lo sp.ids[sender]),
       Fp.ofNat (ProcPriorIdLimbs.mid sp.ids[sender]),Fp.ofNat (ProcPriorIdLimbs.hi sp.ids[sender])]) :
    r+7<tr.height t ∧ ∀i,i<8→cv tr t (r+i) bpost=((NearSpec.u64 sp.ids[sender]).getD i 0).toNat :=
  sender_bytes hL hr hm sp.ids[sender] tauV sender
    (prepD0_ids64 hprep sp hsp _ (List.getElem_mem hsender)) hp
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundPublicId
