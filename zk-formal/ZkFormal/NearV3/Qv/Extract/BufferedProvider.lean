import ZkFormal.NearV3.Qv.Extract.UniqueShardLookup
import ZkFormal.NearV3.Qv.Extract.ProviderLink

namespace ZkFormal.NearV3.Qv.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open Candidates.ValueTable

/-- QVC conservation supplies a real buffered parser record for every present
buffered queue read; its ID and transition match the physical request. -/
theorem physical_buffered_provider_exists {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (hL : TableLocal Candidates.CombinedTable.table tr tt pub)
    (q : WalkChain tr tt) (v : ParserChain tr tt (segEnd 0 q.segs))
    (hbalance : ∀ m, tableBusCount Candidates.CombinedTable.interactions tr tt pub B_QVC true m=
      tableBusCount Candidates.CombinedTable.interactions tr tt pub B_QVC false m)
    (w : Nat × Nat) (hw : w∈q.segs)
    (ha : tr.cell tt w.1 Candidates.CombinedTable.absent=0)
    (hm : cv tr tt w.1 len=1) :
    ∃ p∈v.segs, tr.cell tt p.1 mBuffer=1 ∧
      cv tr tt p.1 vid=cv tr tt w.1 vid ∧ cv tr tt p.1 tau=cv tr tt w.1 tau := by
  obtain ⟨p,hp,hkey⟩ := physical_provider_exists hL q v hbalance w hw ha
  simp only [providerKey,requestKey,List.cons.injEq] at hkey
  have htag : mode.eval tr tt p.1 pub=1 := by
    have hn := hkey.2.2.1
    rw [hm] at hn
    have he := congrArg Fp.ofNat hn
    simpa only [Fp.ofNat_toNat,show Fp.ofNat 1=(1:Fp) from rfl] using he
  have hend := seg_le_end v.segs (segEnd 0 q.segs) v.consecutive p hp
  have hs := v.valid p hp
  have hfit := Nat.le_trans hend.2 v.fits
  have hpos := hs.1
  have hb : p.1<tr.height tt := by omega
  have hwalk := zero_of_false hL hb (x:=Candidates.CombinedTable.walk) (by simp [walkBools])
    (q.suffix p.1 hend.1 hb)
  have hactive : tr.cell tt p.1 act=1 := by
    simpa only [isOne,decide_eq_true_eq] using hs.2.2.2.1 p.1 (by omega) (by omega)
  have hbuf := (Parser.mode_tag hL hb hwalk hactive).2.1.mp htag
  exact ⟨p,hp,hbuf,hkey.1,hkey.2.1⟩

end ZkFormal.NearV3.Qv.Extract
