import ZkFormal.NearV3.Candidates.ProcPriorRoutedDigest
namespace ZkFormal.NearV3.Candidates.ProcPriorRoutedDigestFacts
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near
open ProcPriorRoutedDigest

theorem empty_message (tr:Trace Fp) (pub:List Fp) (r:Nat) :
    ∃id:Fp,empty.msgVal tr 0 r pub=[id,Fp.ofNat 0]++
      (NearSpec.sha256 []).map (fun x=>Fp.ofNat x.toNat) := by
  refine ⟨Fp.ofNat K_VPRE+16*(ProcPriorRoutedRawBytes.value tr).cell 0 r ValV3.vid,?_⟩
  simp only [empty,HorizontalTables.interaction,Interaction.msgVal,List.map_map,Function.comp_def,
    HorizontalTrace.expression_eval,Rcpt.Candidates.EmptyValue.emptyInteraction,
    ZkFormal.Near.Dsl.send,List.map_append,List.map_cons,List.map_nil,
    Rcpt.Candidates.EmptyValue.emptyHash]
  simp only [ZkFormal.Near.Dsl.k,Expr.eval,Expr.evalWith,rowEnv,List.map_map,Function.comp_def]
  rfl

theorem empty_digest (tr:Trace Fp) (pub msg:List Fp) (hm:0<emptyCount tr pub msg) :
    ∃id:Fp,msg=[id,Fp.ofNat 0]++(NearSpec.sha256 []).map (fun x=>Fp.ofNat x.toNat) := by
  unfold emptyCount at hm
  rw [tableBusCount_eq] at hm
  have hmem:=List.count_pos_iff.mp hm
  simp only [List.mem_flatMap,List.mem_range,rowTraffic,List.flatMap_cons,List.flatMap_nil,
    List.append_nil] at hmem
  obtain ⟨r,hr,hm⟩:=hmem
  have he:empty.bus=B_DIGEST ∧ empty.send=true:=by exact ⟨rfl,rfl⟩
  rw [if_pos he] at hm
  obtain ⟨_,heq⟩:=List.mem_replicate.mp hm
  rw [heq]
  exact empty_message tr pub r

def sends (tr:Trace Fp) (pub:List Fp) (b:Nat) (msg:List Fp):Nat:=
  ProcPriorRoutedShaFacts.sumCount tr pub [0,1,2,3] true b msg+
    if b=B_DIGEST then emptyCount tr pub msg else 0

/-- Exact installed digest suppliers include the specified SHA of the empty
value, whose byte obligation is vacuous. -/
theorem facts {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables) :
    ShaFacts (sends tr pub) (ProcPriorRoutedShaFacts.sumCount tr pub [0,1,2,3] false) := by
  have h:=ProcPriorRoutedShaFacts.four hH htables
  refine ⟨?_,h.recvs_only_bytes,?_⟩
  · intro b msg hb
    simp [sends,h.sends_only_digest b msg hb,hb]
  · intro msg hm
    by_cases hp:0<ProcPriorRoutedShaFacts.sumCount tr pub [0,1,2,3] true B_DIGEST msg
    · exact h.digest msg hp
    · have he:0<emptyCount tr pub msg:=by
        simp only [sends,ite_true] at hm
        omega
      obtain ⟨id,heq⟩:=empty_digest tr pub msg he
      exact ⟨id,[],heq,fun i hi=>by cases hi⟩
/-- Every live installed DIGEST consumer has a checked SHA preimage supplied
by the actual four SHA components or by the specified empty-value digest. -/
theorem consumer {AP:AirP} {pub:List Fp} {tr:Trace Fp}
    (hH:HoldsP AP pub tr) (htables:AP.tables=ProcPriorComparatorRoutedFamily.tables)
    (hpub:∀msg,pubCount AP pub B_DIGEST true msg=0)
    {t r:Nat} (ht:t<AP.tables.length) (hr:r<tr.height t) {i:Interaction}
    (hi:i∈AP.tables[t]!.interactions) (hb:i.bus=B_DIGEST) (hs:i.send=false)
    (hm:i.multNat tr t r pub≠0) :
    ∃(id:Fp) (bs:NearSpec.Bytes),i.msgVal tr t r pub=
      [id,Fp.ofNat bs.length]++(NearSpec.sha256 bs).map (fun x=>Fp.ofNat x.toNat) ∧
      ∀j,j<bs.length→0<ProcPriorRoutedShaFacts.sumCount tr pub [0,1,2,3] false B_BYTES
        [id,Fp.ofNat j,Fp.ofNat (bs.getD j 0).toNat] := by
  have hp:=ZkFormal.Chacha.tableBusCount_pos hr hi hm
  rw [hb,hs] at hp
  have hle:=ZkFormal.Chacha.busCount_go_ge tr pub B_DIGEST false (i.msgVal tr t r pub) AP.tables 0 t ht
  simp only [Nat.zero_add] at hle
  have hh:=hH.balance B_DIGEST (i.msgVal tr t r pub)
  rw [hpub,ProcPriorRoutedDigest.global_count htables] at hh
  have hpos:0<sends tr pub B_DIGEST (i.msgVal tr t r pub) := by
    simp only [sends,ite_true]
    change _≤busCount AP.toAir tr pub B_DIGEST false (i.msgVal tr t r pub) at hle
    omega
  exact (facts hH htables).digest _ hpos
end ZkFormal.NearV3.Candidates.ProcPriorRoutedDigestFacts
