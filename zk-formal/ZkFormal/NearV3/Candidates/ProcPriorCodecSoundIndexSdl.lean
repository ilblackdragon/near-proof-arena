import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundIndex
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundIndexSdl
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec

theorem dl_index {ids : List Nat} (hn:ids.length≤64) {M : List Fp}
    (hM:M∈(dlRecs 0 ids).map (·.map Fp.ofNat)) {τ klo khi o b k : Nat}
    (hlo:klo<P) (hhi:khi<P) (hk:(klo+256*khi)%P=k)
    (e:M=[τ,klo,khi,o,b].map Fp.ofNat) : k<ids.length*ids.length := by
  obtain ⟨R,hR,rfl⟩:=List.mem_map.mp hM
  simp only [dlRecs,List.mem_flatMap,List.mem_range,List.mem_map] at hR
  obtain ⟨k',hk',o',_,rfl⟩:=hR
  have hnn:k'<4096 := by have :=Nat.mul_le_mul hn hn;omega
  simp only [b2,List.cons_append,List.nil_append,List.map_cons,List.map_nil,List.cons.injEq] at e
  obtain ⟨_,e2,e3,_,_⟩:=e
  have h2:=ofNat_inj' (by omega) hlo e2
  have h3:=ofNat_inj' (by omega) hhi e3
  have hkk:k=k' := by
    rw [←hk,←h2,←h3]
    rw [Nat.mod_eq_of_lt (by simp only [P];omega)]
    omega
  omega

theorem sender_index_bound {AP : AirP} {pub : List Fp} {tr : Trace Fp}
    (hH:HoldsP AP pub tr) (tc : Nat) (ht:tc<AP.tables.length)
    (htab:AP.tables[tc]! =ProcPriorCodecActual.table) (own:SdlOwn AP tc)
    (I:PubIdx AP pub Fp.ofNat) (ids : List Nat) (hn:ids.length≤64)
    (hrec:I.recs B_SDL true=dlRecs 0 ids)
    (r : Nat) (hr:r<tr.height tc) (hS:cv tr tc r fS=1) :
    cv tr tc r kidx<ids.length*ids.length := by
  have hL:=local_of_holdsP hH ht
  rw [htab] at hL
  have hrow:=ProcPriorCodecSoundSdlRows.sender_row hL hr hS
  obtain ⟨seed,_,hpublic⟩:=ProcPriorCodecSoundSdlFinite.public_origin hH tc ht htab own r hr
    (by rw [hrow.1];decide)
  rw [I.count,hrec] at hpublic
  have hmem:=List.count_pos_iff.mp (Nat.pos_of_ne_zero hpublic)
  have hR:=(ProcPriorCodecSoundGeometry.sender_kind hL hr hS).1
  have hk:=ProcPriorCodecSoundSdlIds.record_index hL hr hR
  have ho:oE.eval tr tc r pub=Fp.ofNat (cv tr tc r g) := by
    have he:=hrow.2.2.1
    rw [(ProcPriorCodecSoundSdlDescent.messages tr tc r pub).1] at he
    have hh:=congrArg (fun xs:List Fp=>xs[3]!) he
    simpa only [ProcPriorCodecSoundSdlDescent.payload,List.map_cons,List.map_nil,
      List.getElem!_cons_succ,List.getElem!_cons_zero] using hh
  exact dl_index (τ:=seed) (o:=cv tr tc r g) (b:=cv tr tc r bpost) hn hmem (cv_lt r klo) (cv_lt r khi) hk
    (by simp only [ProcPriorCodecSoundSdlDescent.payload,List.map_cons,List.map_nil,ho])
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundIndexSdl
