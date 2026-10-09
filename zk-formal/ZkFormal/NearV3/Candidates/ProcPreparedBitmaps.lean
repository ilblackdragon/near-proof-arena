import ZkFormal.NearV3.Candidates.ProcBitmapShape
namespace ZkFormal.NearV3.Candidates.ProcPreparedBitmaps
open NearSpec NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched ProcBitmapShape

def PubBits (sp : SchedPub) : Prop := ∀e∈sp.raw,∀q∈e.2,q.bitmap.length=5

theorem schedPub_bits (L : Layout) (own g gp : Nat) (M : Blk) (hb : BlockBits M)
    (sp : SchedPub) (h : schedPub (blockCtx L own g M gp)=some sp) : PubBits sp := by
  unfold schedPub pubOf at h
  simp only [blockCtx] at h
  by_cases hn : L.shardIds.length=0
  · simp [hn] at h
  · cases hp : Params.calculate Config.pv86 L.shardIds.length with
    | none => simp [hn,hp] at h
    | some p =>
      simp only [hn,hp,ite_false,Option.bind,bind,Option.some.injEq] at h
      subst sp
      intro e he q hq
      have he := toBTreeMap_mem _ e he
      simp only [blockCtx,List.map_map,List.mem_map,Function.comp] at he
      rcases he with ⟨⟨slot,ci⟩,hc,rfl⟩
      rcases List.mem_map.mp hq with ⟨r,hr,rfl⟩
      exact hb (slot,ci) hc r hr

theorem decoded_blocks {recs : List BlockRec} {blks : List Blk}
    (h : List.mapM decodeBlk recs=.ok blks) : ∀b∈blks,BlockBits b := by
  intro b hb
  obtain ⟨r,hr,he⟩ := mapM_ok _ _ _ h b hb
  exact block_decode he

theorem sched_close {L : Layout} {blks : List Blk} {i : Nat} {b B2 : Blk} {own g gp : Nat}
    {sched : List SchedPub} {recs : List BlockRec} {f : ApplyCtx → Except String SchedPub}
    (hm : List.mapM f (blockCtx L own g B2 gp ::
      List.map (fun M=>blockCtx L own g M M.hdr.nextGasPrice) (List.take i blks).reverse)=.ok sched)
    (hb : blks[i]?=some b) (hpb : (pure b : Except String Blk)=.ok B2)
    (hd : List.mapM decodeBlk recs=.ok blks)
    (hf : ∀ctx sp,f ctx=.ok sp → schedPub ctx=some sp) : ∀sp∈sched,PubBits sp := by
  simp only [pure,Except.pure,Except.ok.injEq] at hpb
  subst B2
  have hall := decoded_blocks hd
  intro sp hsp
  obtain ⟨ctx,hctx,hfc⟩ := mapM_ok f _ _ hm sp hsp
  have hs := hf ctx sp hfc
  rcases List.mem_cons.mp hctx with rfl|hctx
  · exact schedPub_bits L own g gp b (hall b (List.mem_of_getElem? hb)) sp hs
  · rcases List.mem_map.mp hctx with ⟨M,hM,rfl⟩
    exact schedPub_bits L own g _ M (hall M (List.mem_of_mem_take (List.mem_reverse.mp hM))) sp hs

set_option maxHeartbeats 1000000 in
theorem prepClaim_bits {cb : Bytes} {pc : PrepC} (h : prepClaim cb=.ok pc) :
    ∀sp∈pc.sched,PubBits sp := by
  unfold prepClaim at h
  repeat' (first
    | (obtain ⟨_,_,h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    simp only [pure,Except.pure,Except.ok.injEq] at h
    subst h
    exact sched_close (by assumption) (by assumption) (by assumption) (by assumption)
      (fun ctx sp hc=>by
        split at hc
        · simp only [pure,Except.pure,Except.ok.injEq] at hc; subst hc; assumption
        · cases hc)

theorem prepD0_bits {cb : Bytes} {hint : Hint} {p : Prep} (h : prepD0 cb hint=.ok p) :
    ∀sp∈p.sched,PubBits sp := by
  unfold prepD0 at h
  obtain ⟨pc,hpc,hb⟩ := bind_ok h
  rw [prepBody_sched hb]
  exact prepClaim_bits hpc
end ZkFormal.NearV3.Candidates.ProcPreparedBitmaps
