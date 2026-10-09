import ZkFormal.NearV3.Candidates.ProcPriorAccountByteTag
import ZkFormal.NearV3.Candidates.MerkleBranches
namespace ZkFormal.NearV3.Candidates.ProcPriorMerkleView
open ZkFormal.Chacha
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
set_option maxRecDepth 32768

def mirror (tr:Trace Fp):Trace Fp:=⟨fun _=>tr.log 10,fun _=>tr.cell 10⟩

theorem local_empty {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    TableLocal MerkleEmpty.table (mirror tr) T_MRK pub := by
  have ht:10<AP.tables.length:=by rw [htables];decide +kernel
  have he:AP.tables[10]! =(InteractionTriples.table MerkleEmpty.table):=by rw [htables];rfl
  have h:TableLocal (InteractionTriples.table MerkleEmpty.table) tr 10 pub := by
    refine ⟨(hH.logBound 10 ht).1,?_,?_,?_⟩
    · have hh:tr.log 10≤AP.tables[10]!.maxLog := by
        rw [getElem!_pos AP.tables 10 ht]
        exact (hH.logBound 10 ht).2
      rwa [he] at hh
    · intro r hr e hem
      have hh:=local_of_holdsP hH ht r hr e
      rw [he] at hh
      exact hh hem
    · intro r hr i hi b hb
      rw [←he,getElem!_pos AP.tables 10 ht] at hi
      exact hH.bits 10 ht r hr i hi b hb
  have hbase:=(InteractionTriples.local_iff MerkleEmpty.table tr 10 pub).mp h
  exact ⟨hbase.log_ge,hbase.log_le,hbase.constr,hbase.bits⟩

theorem count {tr:Trace Fp} (pub msg:List Fp) (b:Nat) (sd:Bool) :
    tableBusCount (ProcPriorComparatorRoutedFamily.tables[10]!).interactions tr 10 pub b sd msg=
      tableBusCount MerkleEmpty.table.interactions (mirror tr) T_MRK pub b sd msg := by
  exact InteractionTriples.count MerkleEmpty.table.interactions tr 10 pub b sd msg

theorem node_bound {tr:Trace Fp} {pub:List Fp} {v:MrkV}
    (hl:tr.log T_MRK≤19)
    (hT:TableTraffic MerkleEmpty.table.interactions tr T_MRK pub
      (mrkTraffic (MerklePublic.aliasPublic pub) v)) :v.nodes.length≤2^19 := by
  let rows:List (List Fp):=(List.range (tr.height T_MRK)).flatMap
    (fun r=>ZkFormal.Near.rowTraffic MerkleEmpty.table.interactions tr T_MRK r pub B_MPOS true)
  have hp:rows.Perm ((mrkSends (MerklePublic.aliasPublic pub) v B_MPOS).map Msg.toFp) := by
    apply List.perm_iff_count.mpr
    intro msg
    have h:=(hT B_MPOS msg).1
    rw [ZkFormal.Near.tableBusCount_eq] at h
    exact h
  have hr:∀r,(ZkFormal.Near.rowTraffic MerkleEmpty.table.interactions tr T_MRK r pub B_MPOS true).length≤1 := by
    intro r
    simp only [MerkleEmpty.table,MerklePublic.table,List.map_map,Function.comp_def,
      Mrk.interactions,List.map_cons,List.map_nil,ZkFormal.Near.rowTraffic,List.flatMap_cons,List.flatMap_nil,
      MerkleEmpty.interaction,MerklePublic.interaction,Dsl.send,Dsl.recv]
    simp only [B_MPOS,B_BYTES,B_DIGEST,Interaction.multNat,Interaction.multNat.go]
    simp
    split <;> omega
  have hflat:∀rs:List Nat,(rs.flatMap (fun r=>ZkFormal.Near.rowTraffic MerkleEmpty.table.interactions tr T_MRK r pub B_MPOS true)).length≤rs.length := by
    intro rs
    induction rs with
    | nil=>simp
    | cons r rs ih=>simp only [List.flatMap_cons,List.length_append,List.length_cons];have:=hr r;omega
  have hrows:=hflat (List.range (tr.height T_MRK))
  have he:=hp.length_eq
  simp only [mrkSends,show B_MPOS≠B_BYTES by decide,ite_false,ite_true,List.length_map,List.length_zip,List.length_range,Nat.min_self] at he
  simp only [List.length_range] at hrows
  have hh:tr.height T_MRK≤2^19:=Nat.pow_le_pow_right (by decide) hl
  change rows.length≤tr.height T_MRK at hrows
  omega
end ZkFormal.NearV3.Candidates.ProcPriorMerkleView
