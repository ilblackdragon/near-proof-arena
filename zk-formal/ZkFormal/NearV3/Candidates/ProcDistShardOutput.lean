import ZkFormal.NearV3.Candidates.ProcDistShardOutputCells
import ZkFormal.NearV3.Candidates.ProcScanParamLocal
namespace ZkFormal.NearV3.Candidates.ProcDistShardOutput
open ZkFormal.Air ZkFormal.Near ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistShardRow
attribute [local irreducible] ProcDistShardRow.row
set_option maxRecDepth 32768

theorem physical (tv n sd i x count left budget kpV:Nat)(hsd:sd=0∨sd=1)(hbudget:budget<256^3)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row tv n sd i x count left budget kpV)[col]!) :
    (∀e∈(Dist.cShard.drop 5).take 3,e.eval tr t r pub=0) ∧
    (∀e∈(Dist.cShard.drop 10).take 11,e.eval tr t r pub=0) := by
  rcases ProcDistShardOutputCells.fields tv n sd i x count left budget kpV with
    ⟨hcx,hcy,hcb,hkp,hside,ha,hr,hda,hdb,hsL,hal,hshd,hlnk,hllo,hnn,hadr,hbv,hby0,hby1,hby2,hb,hs⟩
  have hav:=ProcDistShardAverageCells.fields tv n sd i x count left budget kpV
  have hq:=ProcDistShardScalarCells.quotients tv n sd i x count left budget kpV
  have sk:tr.cell t r Dist.kSh=1:=by rw [hrow,hav.1];rfl
  have sq:tr.cell t r Dist.q2=Fp.ofNat (average count left):=by rw [hrow,hq.2.2.1]
  have sl:tr.cell t r Dist.L2=Fp.ofNat left:=by rw [hrow,hav.2.2.1]
  have sn:tr.cell t r Dist.N2=Fp.ofNat count:=by rw [hrow,hav.2.1]
  have scx:tr.cell t r Dist.cx=Fp.ofNat (average count left*64+x):=by rw [hrow,hcx]
  have scy:tr.cell t r Dist.cy=Fp.ofNat (kpV):=by rw [hrow,hcy]
  have scb:tr.cell t r Dist.cb=Fp.ofNat (1):=by rw [hrow,hcb]
  have skp:tr.cell t r Dist.kp=Fp.ofNat (kpV):=by rw [hrow,hkp]
  have sside:tr.cell t r Dist.side=Fp.ofNat (sd):=by rw [hrow,hside]
  have sa:tr.cell t r Dist.a=Fp.ofNat (i):=by rw [hrow,ha]
  have sr:tr.cell t r Dist.r=Fp.ofNat (x):=by rw [hrow,hr]
  have sda:tr.cell t r Dist.da=Fp.ofNat (if sd=0 then i else 0):=by rw [hrow,hda]
  have sdb:tr.cell t r Dist.db=Fp.ofNat (if sd=0 then 255 else i):=by rw [hrow,hdb]
  have ssL:tr.cell t r Dist.sL=Fp.ofNat (left):=by rw [hrow,hsL]
  have sal:tr.cell t r Dist.al=Fp.ofNat (0):=by rw [hrow,hal]
  have sshd:tr.cell t r Dist.shd=Fp.ofNat (x):=by rw [hrow,hshd]
  have slnk:tr.cell t r Dist.lnk=Fp.ofNat (count):=by rw [hrow,hlnk]
  have sllo:tr.cell t r Dist.llo=Fp.ofNat (n):=by rw [hrow,hllo]
  have snn:tr.cell t r Dist.nn=Fp.ofNat (n):=by rw [hrow,hnn]
  have sadr:tr.cell t r Dist.adr=Fp.ofNat (4096*(sd+1)+x):=by rw [hrow,hadr]
  have sbv:tr.cell t r Dist.bv=Fp.ofNat (budget):=by rw [hrow,hbv]
  have sby0:tr.cell t r Dist.by0=Fp.ofNat (budget%256):=by rw [hrow,hby0]
  have sby1:tr.cell t r Dist.by1=Fp.ofNat (budget/256%256):=by rw [hrow,hby1]
  have sby2:tr.cell t r Dist.by2=Fp.ofNat (budget/65536%256):=by rw [hrow,hby2]
  have sb:tr.cell t r Dist.b=Fp.ofNat (0):=by rw [hrow,hb]
  have ss:tr.cell t r Dist.s=Fp.ofNat (0):=by rw [hrow,hs]
  have hbytes:=ProcScanParamLocal.byte3 budget hbudget
  simp only [Scan.byteOf] at hbytes
  have hbytesF:=congrArg Fp.ofNat hbytes
  clear hrow hav hq hcx hcy hcb hkp hside ha hr hda hdb hsL hal hshd hlnk hllo hnn hadr hbv hby0 hby1 hby2 hb hs
  simp only [Dist.cShard,List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,
    List.take_succ_cons,List.take_zero,List.forall_mem_cons,List.forall_mem_nil]
  constructor
  · refine ⟨?_,?_,?_,by simp⟩
    · change tr.cell t r Dist.kSh*(tr.cell t r Dist.cx + -((64:Fp)*tr.cell t r Dist.q2+tr.cell t r Dist.r))=0
      rw [sk,scx,sq,sr]
      simp only [←ofNat_add',←ofNat_mul']
      change (1:Fp)*((Fp.ofNat (average count left)*64+Fp.ofNat x)+-(64*Fp.ofNat (average count left)+Fp.ofNat x))=0
      grind only
    · change tr.cell t r Dist.kSh*(tr.cell t r Dist.cy + -tr.cell t r Dist.kp)=0
      rw [sk,scy,skp];grind only
    · change tr.cell t r Dist.kSh*(tr.cell t r Dist.cb + -(1:Fp))=0
      rw [sk,scb];change (1:Fp)*(1+-1)=0;grind only
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,by simp⟩
    · change tr.cell t r Dist.kSh*(tr.cell t r Dist.da + -((1 + -tr.cell t r Dist.side)*tr.cell t r Dist.a))=0
      rw [sk,sda,sside,sa]
      rcases hsd with hsd|hsd <;> subst sd <;> simp only [ite_true,ite_false,Nat.one_ne_zero]
      all_goals change (1:Fp)*_ =0; simp only [show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl];grind only
    · change tr.cell t r Dist.kSh*(tr.cell t r Dist.db + -(tr.cell t r Dist.side*tr.cell t r Dist.a+(255:Fp)*(1 + -tr.cell t r Dist.side)))=0
      rw [sk,sdb,sside,sa]
      rcases hsd with hsd|hsd <;> subst sd <;> simp only [ite_true,ite_false,Nat.one_ne_zero]
      all_goals simp only [show Fp.ofNat 0=(0:Fp) from rfl,show Fp.ofNat 1=(1:Fp) from rfl,show Fp.ofNat 255=(255:Fp) from rfl];grind only
    · change tr.cell t r Dist.kSh*(tr.cell t r Dist.sL + -tr.cell t r Dist.L2)=0
      rw [sk,ssL,sl];grind only
    · change tr.cell t r Dist.kSh*tr.cell t r Dist.al=0
      rw [sk,sal];change (1:Fp)*0=0;grind only
    · change tr.cell t r Dist.kSh*(tr.cell t r Dist.shd + -tr.cell t r Dist.r)=0
      rw [sk,sshd,sr];grind only
    · change tr.cell t r Dist.kSh*(tr.cell t r Dist.lnk + -tr.cell t r Dist.N2)=0
      rw [sk,slnk,sn];grind only
    · change tr.cell t r Dist.kSh*(tr.cell t r Dist.llo + -tr.cell t r Dist.nn)=0
      rw [sk,sllo,snn];grind only
    · change tr.cell t r Dist.kSh*(tr.cell t r Dist.adr + -((4096:Fp)*(tr.cell t r Dist.side+1)+tr.cell t r Dist.r))=0
      rw [sk,sadr,sside,sr]
      simp only [←ofNat_add',←ofNat_mul']
      change (1:Fp)*((4096*(Fp.ofNat sd+1)+Fp.ofNat x)+-(4096*(Fp.ofNat sd+1)+Fp.ofNat x))=0
      grind only
    · change tr.cell t r Dist.kSh*(tr.cell t r Dist.bv + -(tr.cell t r Dist.by0+((256:Fp)*tr.cell t r Dist.by1+(65536:Fp)*tr.cell t r Dist.by2)))=0
      rw [sk,sbv,sby0,sby1,sby2]
      simp only [Nat.pow_zero,Nat.pow_one,Nat.reducePow,Nat.div_one] at hbytesF
      simp only [←ofNat_add',←ofNat_mul'] at hbytesF
      change Fp.ofNat budget=Fp.ofNat (budget%256)+256*Fp.ofNat (budget/256%256)+65536*Fp.ofNat (budget/65536%256) at hbytesF
      grind only
    · change tr.cell t r Dist.kSh*tr.cell t r Dist.b=0
      rw [sk,sb];change (1:Fp)*0=0;grind only
    · change tr.cell t r Dist.kSh*tr.cell t r Dist.s=0
      rw [sk,ss];change (1:Fp)*0=0;grind only
end ZkFormal.NearV3.Candidates.ProcDistShardOutput
