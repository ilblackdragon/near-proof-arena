import ZkFormal.NearV3.Candidates.ProcessRepairIdGlobalOrder
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdPublicOrder
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorIdTable ProcessRepairIdOrder ProcessRepairIdLexOrder ProcessRepairIdComparisons
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem next_public {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    {r:Nat} (hr:r+1<tr.height 0) (ha:Live (memory tr) r) (hb:Live (memory tr) (r+1))
    (ht:keyTop (memory tr) r=keyTop (memory tr) (r+1))
    (hm:cv (memory tr) 0 r keyMid=cv (memory tr) 0 (r+1) keyMid)
    (hl:cv (memory tr) 0 r keyLo=cv (memory tr) 0 (r+1) keyLo)
    (hp:cv (memory tr) 0 r isPublic=1) (hn:cv (memory tr) 0 (r+1) isPublic=1)
    (hpa:cv (memory tr) 0 r ordinal<64) (hpb:cv (memory tr) 0 (r+1) ordinal<64) :
    cv (memory tr) 0 r ordinal<cv (memory tr) 0 (r+1) ordinal := by
  have hrm:r+1<(memory tr).height 0:=hr
  have hv:=ProcessRepairRawBytes.overlay_local view
  have hlast:=ProcPriorIdInterval.last_zero hv hr ha.1 hb.1
  have hrow:=ProcPriorVerticalIdRows.row_local hv hr ha.1 hlast
  change ProcPriorIdSoundRows.At (memory tr) 0 r pub at hrow
  have hpack:ProcPriorIdKeyOrigin.packed (memory tr) 0 (r+1)=ProcPriorIdKeyOrigin.packed (memory tr) 0 r:=by
    rw [packed_value,packed_value,ht]
  have hg:=ProcPriorIdSameKey.group hrow hr ha.2 hb.2 hpack hm.symm hl.symm
  obtain ⟨q,hq⟩:=ProcPriorIdSoundRows.zdvd hrow
    (e:=sub (c gPublic) (.mul (.mul (c gAll) (c isPublic)) (n isPublic))) (by simp [constraints])
  simp only [zev_sub,zev_mul,zev_c,zev_n,cur_cv,Codec.nx hrm,hg,hp,hn] at hq
  have hbit:=ProcPriorIdSoundRows.flag hrow (x:=gPublic) (by simp)
  have hgp:cv (memory tr) 0 r gPublic=1:=by omega
  have hmult:(request 6).multNat tr 0 r pub=1:=by
    rw [request_mult]
    apply Codec.mult_of rfl
    change zev (tenv (memory tr) 0 r pub) (.mul (c (ProcPriorVertical4Linear.stage 1)) (c gPublic))=1
    simp only [zev_mul,zev_c,cur_cv,ha.1,hgp]
    rfl
  have hcur:(.add (c ordinal) (k 1):Expr).eval (memory tr) 0 r pub=Fp.ofNat (cv (memory tr) 0 r ordinal+1):=
    Codec.ev_of (by simp only [zev_add,zev_c,zev_k,cur_cv,Int.natCast_add,Int.natCast_one])
  have hnext:(n ordinal).eval (memory tr) 0 r pub=Fp.ofNat (cv (memory tr) 0 (r+1) ordinal):=
    Codec.ev_of (by simp only [zev_n,Codec.nx hrm])
  have hmsg:(request 6).msgVal tr 0 r pub=[Fp.ofNat (cv (memory tr) 0 (r+1) ordinal),Fp.ofNat (cv (memory tr) 0 r ordinal+1),1]:=by
    rw [request_message]
    change [(n ordinal).eval (memory tr) 0 r pub,(.add (c ordinal) (k 1):Expr).eval (memory tr) 0 r pub,Fp.ofNat 1]=_
    rw [hcur,hnext];rfl
  have hpv:P=2013265921:=P_val
  have hto (n:Nat) (h:n<P):(Fp.ofNat n).toNat=n:=by simp only [Fp.toNat_ofNat,Nat.mod_eq_of_lt h]
  have hbnd:=compare view hpub 6 (by simp) (by omega) (by rw [hmult];decide) hmsg
    (by rw [hto _ (by omega)];omega) (by rw [hto _ (by omega)];omega)
  rw [hto _ (by omega),hto _ (by omega)] at hbnd
  omega
end ZkFormal.NearV3.Candidates.ProcessRepairIdPublicOrder
