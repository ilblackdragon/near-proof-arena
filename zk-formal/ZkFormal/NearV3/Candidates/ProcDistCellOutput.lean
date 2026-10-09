import ZkFormal.NearV3.Candidates.ProcDistCellOutputCells
namespace ZkFormal.NearV3.Candidates.ProcDistCellOutput
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ProcDistCellRow
attribute [local irreducible] ProcDistCellRow.row
set_option maxRecDepth 32768

theorem physical (ids:List Nat)(tv n i j sv rr n1 l1 n2 l2:Nat)(allowed:Bool)
    (tr:Trace Fp)(t r:Nat)(pub:List Fp)
    (hrow:∀col,tr.cell t r col=Fp.ofNat (row ids tv n i j sv rr n1 l1 n2 l2 allowed)[col]!) :
    (∀e∈(Dist.cGrid.drop 9).take 3,e.eval tr t r pub=0) ∧
    (∀e∈(Dist.cGrid.drop 16).take 10,e.eval tr t r pub=0) := by
  rcases ProcDistCellOutputCells.fields ids tv n i j sv rr n1 l1 n2 l2 allowed with
    ⟨hkSh,hkGH,hkC,hs,hnn,hr,hllo,hlhi,halc,hal,hcx,hcy,hq1,hq2,hgb,hcb,hcg,ha,hb,hda,hdb,hsL,hL2,he2,hdlsg,hdlrg⟩
  have skSh:tr.cell t r Dist.kSh=Fp.ofNat (0):=by rw [hrow,hkSh]
  have skGH:tr.cell t r Dist.kGH=Fp.ofNat (0):=by rw [hrow,hkGH]
  have skC:tr.cell t r Dist.kC=Fp.ofNat (1):=by rw [hrow,hkC]
  have ss:tr.cell t r Dist.s=Fp.ofNat (sv):=by rw [hrow,hs]
  have snn:tr.cell t r Dist.nn=Fp.ofNat (n):=by rw [hrow,hnn]
  have sr:tr.cell t r Dist.r=Fp.ofNat (rr):=by rw [hrow,hr]
  have sllo:tr.cell t r Dist.llo=Fp.ofNat ((sv*n+rr)%256):=by rw [hrow,hllo]
  have slhi:tr.cell t r Dist.lhi=Fp.ofNat ((sv*n+rr)/256):=by rw [hrow,hlhi]
  have salc:tr.cell t r Dist.alc=Fp.ofNat (b2n allowed):=by rw [hrow,halc]
  have sal:tr.cell t r Dist.al=Fp.ofNat (b2n allowed):=by rw [hrow,hal]
  have scx:tr.cell t r Dist.cx=Fp.ofNat (quot allowed n1 l1):=by rw [hrow,hcx]
  have scy:tr.cell t r Dist.cy=Fp.ofNat (quot allowed n2 l2):=by rw [hrow,hcy]
  have sq1:tr.cell t r Dist.q1=Fp.ofNat (quot allowed n1 l1):=by rw [hrow,hq1]
  have sq2:tr.cell t r Dist.q2=Fp.ofNat (quot allowed n2 l2):=by rw [hrow,hq2]
  have sgb:tr.cell t r Dist.gb=Fp.ofNat (grant allowed n1 l1 n2 l2):=by rw [hrow,hgb]
  have scb:tr.cell t r Dist.cb=Fp.ofNat (if allowed && quot allowed n2 l2≤quot allowed n1 l1 then 1 else 0):=by rw [hrow,hcb]
  have scg:tr.cell t r Dist.cg=Fp.ofNat (b2n allowed):=by rw [hrow,hcg]
  have sa:tr.cell t r Dist.a=Fp.ofNat (i):=by rw [hrow,ha]
  have sb:tr.cell t r Dist.b=Fp.ofNat (j):=by rw [hrow,hb]
  have sda:tr.cell t r Dist.da=Fp.ofNat (i+1):=by rw [hrow,hda]
  have sdb:tr.cell t r Dist.db=Fp.ofNat (j):=by rw [hrow,hdb]
  have ssL:tr.cell t r Dist.sL=Fp.ofNat (l2-grant allowed n1 l1 n2 l2):=by rw [hrow,hsL]
  have sL2:tr.cell t r Dist.L2=Fp.ofNat (l2):=by rw [hrow,hL2]
  have se2:tr.cell t r Dist.e2=Fp.ofNat (if i+1=n then 1 else 0):=by rw [hrow,he2]
  have sdlsg:tr.cell t r Dist.dlsg=Fp.ofNat (1-(if i+1=n then 1 else 0)):=by rw [hrow,hdlsg]
  have sdlrg:tr.cell t r Dist.dlrg=Fp.ofNat (1):=by rw [hrow,hdlrg]
  clear hrow hkSh hkGH hkC hs hnn hr hllo hlhi halc hal hcx hcy hq1 hq2 hgb hcb hcg ha hb hda hdb hsL hL2 he2 hdlsg hdlrg
  have hlink:Fp.ofNat ((sv*n+rr)%256)+256*Fp.ofNat ((sv*n+rr)/256)=Fp.ofNat sv*Fp.ofNat n+Fp.ofNat rr := by
    change Fp.ofNat ((sv*n+rr)%256)+Fp.ofNat 256*Fp.ofNat ((sv*n+rr)/256)=Fp.ofNat sv*Fp.ofNat n+Fp.ofNat rr
    rw [ofNat_mul',ofNat_add',ofNat_mul',ofNat_add']
    exact congrArg Fp.ofNat (Nat.mod_add_div _ _)
  have hgrant:=ProcDistCellArithmetic.grant_selector allowed n1 l1 n2 l2
  have hleft:=ProcDistCellArithmetic.remaining allowed n1 l1 n2 l2
  simp only [Dist.cGrid,Dist.instCols,List.cons_append,List.nil_append,List.map_cons,List.map_nil,
    List.drop_succ_cons,List.drop_zero,List.take_succ_cons,List.take_zero,List.forall_mem_cons]
  constructor
  · refine ⟨?_,?_,?_,by simp⟩
    · change tr.cell t r Dist.kC*((tr.cell t r Dist.llo+(256:Fp)*tr.cell t r Dist.lhi)+-(tr.cell t r Dist.s*tr.cell t r Dist.nn+tr.cell t r Dist.r))=0
      rw [skC,sllo,slhi,ss,snn,sr,hlink];grind only
    · change tr.cell t r Dist.kC*(tr.cell t r Dist.alc + -tr.cell t r Dist.al)=0
      rw [skC,salc,sal];grind only
    · change tr.cell t r Dist.al*(1 + -tr.cell t r Dist.kC)=0
      rw [skC];change _*((1:Fp)+-1)=0;grind only
  · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,by simp⟩
    · change tr.cell t r Dist.kC*(tr.cell t r Dist.cx + -tr.cell t r Dist.q1)=0
      rw [skC,scx,sq1];grind only
    · change tr.cell t r Dist.kC*(tr.cell t r Dist.cy + -tr.cell t r Dist.q2)=0
      rw [skC,scy,sq2];grind only
    · change tr.cell t r Dist.al*(tr.cell t r Dist.gb + -(tr.cell t r Dist.cb*tr.cell t r Dist.q2+(1 + -tr.cell t r Dist.cb)*tr.cell t r Dist.q1))=0
      rw [sal,sgb,scb,sq2,sq1]
      grind only
    · change tr.cell t r Dist.kC*((1 + -tr.cell t r Dist.al)*tr.cell t r Dist.gb)=0
      rw [skC,sal,sgb]
      cases allowed
      · change (1:Fp)*((1+-0)*0)=0;grind only
      · change (1:Fp)*((1+-1)*_)=0;grind only
    · change tr.cell t r Dist.cg + -(tr.cell t r Dist.kSh+tr.cell t r Dist.kC*tr.cell t r Dist.al)=0
      rw [scg,skSh,skC,sal]
      change Fp.ofNat (b2n allowed)+-((0:Fp)+1*Fp.ofNat (b2n allowed))=0;grind only
    · change tr.cell t r Dist.kC*(tr.cell t r Dist.da + -(tr.cell t r Dist.a+1))=0
      rw [skC,sda,sa,←ofNat_add']
      change (1:Fp)*((Fp.ofNat i+1)+-(Fp.ofNat i+1))=0;grind only
    · change tr.cell t r Dist.kC*(tr.cell t r Dist.db + -tr.cell t r Dist.b)=0
      rw [skC,sdb,sb];grind only
    · change tr.cell t r Dist.kC*(tr.cell t r Dist.sL + -(tr.cell t r Dist.L2 + -tr.cell t r Dist.gb))=0
      rw [skC,ssL,sL2,sgb]
      grind only
    · change tr.cell t r Dist.dlsg + -(tr.cell t r Dist.kSh+tr.cell t r Dist.kC*(1 + -tr.cell t r Dist.e2))=0
      rw [sdlsg,skSh,skC,se2]
      by_cases he:i+1=n
      · rw [if_pos he];change (0:Fp)+-(0+1*(1+-1))=0;grind only
      · rw [if_neg he];change (1:Fp)+-(0+1*(1+-0))=0;grind only
    · change tr.cell t r Dist.dlrg + -(tr.cell t r Dist.kGH+tr.cell t r Dist.kC)=0
      rw [sdlrg,skGH,skC];change (1:Fp)+-(0+1)=0;grind only
end ZkFormal.NearV3.Candidates.ProcDistCellOutput
