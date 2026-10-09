import ZkFormal.NearV3.Candidates.ProcessRepairIdLimbOrder
namespace ZkFormal.NearV3.Candidates.ProcessRepairIdLexOrder
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ProcPriorIdTable ProcessRepairIdOrder
open ProcPriorCodecFamilyLastWrite (memory)
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768

def Bounded (tr:Trace Fp) (r:Nat):Prop :=cv tr 0 r tau<33 ∧ cv tr 0 r keyLo<16777216 ∧ cv tr 0 r keyMid<16777216 ∧ cv tr 0 r keyHi<65536
def Lex (tr:Trace Fp) (a b:Nat):Prop :=keyTop tr a<keyTop tr b ∨ keyTop tr a=keyTop tr b ∧
  (cv tr 0 a keyMid<cv tr 0 b keyMid ∨ cv tr 0 a keyMid=cv tr 0 b keyMid ∧ cv tr 0 a keyLo≤cv tr 0 b keyLo)

theorem packed_value (tr:Trace Fp) (r:Nat) :
    ProcPriorIdKeyOrigin.packed tr 0 r=Fp.ofNat (keyTop tr r) := by
  change (.add (.mul (k 65536) (c tau)) (c keyHi):Expr).eval tr 0 r []=_
  exact Codec.ev_of (by simp only [keyTop,zev_add,zev_mul,zev_k,zev_c,cur_cv,Int.natCast_add,Int.natCast_mul])

theorem adjacent {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (view:ProcessRepairInterface.View AP pub tr)
    (hpub:∀seg∈AP.pubSegs,seg.bus≠40)
    {r:Nat} (hr:r+1<tr.height 0) (ha:Live (memory tr) r) (hb:Live (memory tr) (r+1))
    (hca:Bounded (memory tr) r) (hcb:Bounded (memory tr) (r+1)) :Lex (memory tr) r (r+1) := by
  have htop:=top_order view hpub hr ha hb (by have h1:=hca.1;have h2:=hca.2.2.2;unfold keyTop;omega) (by have h1:=hcb.1;have h2:=hcb.2.2.2;unfold keyTop;omega)
  by_cases he:keyTop (memory tr) r=keyTop (memory tr) (r+1)
  · right;refine ⟨he,?_⟩
    have hL:=ProcessRepairRawBytes.overlay_local view
    have hlast:=ProcPriorIdInterval.last_zero hL hr ha.1 hb.1
    have hl:=ProcPriorVerticalIdRows.row_local hL hr ha.1 hlast
    have hp:ProcPriorIdKeyOrigin.packed (memory tr) 0 (r+1)=ProcPriorIdKeyOrigin.packed (memory tr) 0 r :=by
      rw [packed_value,packed_value,he]
    have hg:=ProcPriorIdPrefixGates.top_gate hl hr ha.2 hb.2 hp
    have hm:=ProcessRepairIdLimbOrder.middle_order view hpub hr ha hb hg (by exact Nat.lt_trans hca.2.2.1 (by decide))
      (by exact Nat.lt_trans hcb.2.2.1 (by decide))
    by_cases hem:cv (memory tr) 0 r keyMid=cv (memory tr) 0 (r+1) keyMid
    · right;refine ⟨hem,?_⟩
      have hgm:=ProcPriorIdPrefixGates.mid_gate hl hr ha.2 hb.2 hg hem.symm
      exact ProcessRepairIdLimbOrder.lower_order view hpub hr ha hb hgm
        (Nat.lt_trans hca.2.1 (by decide)) (Nat.lt_trans hcb.2.1 (by decide))
    · left;omega
  · left;omega

theorem trans {tr:Trace Fp} {a b c:Nat} (hab:Lex tr a b) (hbc:Lex tr b c) :Lex tr a c := by
  unfold Lex at *
  omega

theorem refl (tr:Trace Fp) (a:Nat):Lex tr a a := by
  exact Or.inr ⟨rfl,Or.inr ⟨rfl,Nat.le_refl _⟩⟩
end ZkFormal.NearV3.Candidates.ProcessRepairIdLexOrder
