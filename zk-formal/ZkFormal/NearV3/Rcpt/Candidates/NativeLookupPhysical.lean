import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupQueryBounds

namespace ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra Render.UpsGen Assembly Qv Qv.Candidates.CombinedWalkGen

abbrev NativeWalk22 := ZkFormal.NearV3.Candidates.Walk22Render.WalkOk

/-- All honest lookup consumers use a single physical log22 Walk table. -/
def nativeWalkTrace (ws : List WalkR) : Trace Fp :=
  ⟨fun _=>22,fun _ r c=>Fp.ofNat (ZkFormal.NearV3.Candidates.Walk22Render.WalkGen.cell ws (2^22) r c)⟩

theorem allLookupQueries_pos (rs : List Receipt) (pre : PTrie) (v : MainValues)
    (pres : List PTrie) (resolve : Resolve) : 0<(allLookupQueries rs pre v pres resolve).length := by
  simp [allLookupQueries,queueLookupQueries,plan,mainPlan]
  omega

theorem native_all_walk_ok (pairs : List (PTrie×PTrie)) (rs : List Receipt) (pre : PTrie)
    (v : MainValues) (pres : List PTrie) (resolve : Resolve) (ws : List WalkR)
    (h : nativeQueryWalks pairs (allLookupQueries rs pre v pres resolve)=some ws)
    (hw : ∀t∈pairs.map Prod.fst,t.wf=true) (hb : preBytes (pairs.map Prod.fst)≤2000000)
    (hts : pairs.length≤Algebra.P) (hr : ∀r∈rs,r.wf=true) (hn : rs.length≤4481)
    (hg : 24*v.shards.length≤2000000) (hk : pres.length≤32) : NativeWalk22 (rankWalks [] ws) := by
  have hrows:=allLookupQueries_rows rs pre v pres resolve hr hn hg hk
  have hf:=nativeQueryWalks_wf pairs _ ws h hw hb hts
    (allLookupQueries_wid rs pre v pres resolve hn hg hk)
    (allLookupQueries_nibbles rs pre v pres resolve) (by omega)
  refine ⟨rankWalks_wf ws hf,?_,?_⟩
  · have hp:=allLookupQueries_pos rs pre v pres resolve
    rw [←nativeQueryWalks_length pairs _ ws h] at hp
    cases ws with
    | nil=>simp at hp
    | cons w ws=>simp [rankWalks]
  · have hh:=nativeQueryWalks_rows pairs _ ws h
    have hlen:=rankWalks_rows ws []
    change (List.map (fun w : WalkR=>w.steps.length) (rankWalks [] ws)).sum≤2^22
    rw [←List.length_flatMap]
    rw [hlen,hh]
    omega

theorem native_all_walk_physical (pairs : List (PTrie×PTrie)) (rs : List Receipt) (pre : PTrie)
    (v : MainValues) (pres : List PTrie) (resolve : Resolve) (ws : List WalkR)
    (h : nativeQueryWalks pairs (allLookupQueries rs pre v pres resolve)=some ws)
    (hw : ∀t∈pairs.map Prod.fst,t.wf=true) (hb : preBytes (pairs.map Prod.fst)≤2000000)
    (hts : pairs.length≤Algebra.P) (hr : ∀r∈rs,r.wf=true) (hn : rs.length≤4481)
    (hg : 24*v.shards.length≤2000000) (hk : pres.length≤32) (t : Nat) (pub : List Fp) :
    TableLocal {WalkV3.table with maxLog:=22} (nativeWalkTrace (rankWalks [] ws)) t pub ∧
    TableTraffic WalkV3.interactions (nativeWalkTrace (rankWalks [] ws)) t pub (walkTraffic3 (rankWalks [] ws)) := by
  have hok:=native_all_walk_ok pairs rs pre v pres resolve ws h hw hb hts hr hn hg hk
  exact ⟨ZkFormal.NearV3.Candidates.Walk22Render.walk_render_local_at _ hok _ t pub 22
      ⟨by change 1≤22;decide,by change 22≤22;decide⟩ hok.cap (by intros;rfl),
    ZkFormal.NearV3.Candidates.Walk22Render.walk_render_traffic_at _ hok _ t pub hok.cap (by intros;rfl)⟩

end ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
