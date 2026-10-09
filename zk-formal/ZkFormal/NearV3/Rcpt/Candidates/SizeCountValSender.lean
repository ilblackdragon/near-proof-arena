import ZkFormal.NearV3.Rcpt.Candidates.SizeCountDecorate
import ZkFormal.NearV3.Rcpt.Candidates.SizeCountViews

namespace ZkFormal.NearV3.Rcpt.Candidates.SizeCount
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ValProof

def valPayload (es : List ValE) : Nat :=
  ((es.filter fun e => !e.vz && !e.dup).map ValE.len).sum

/-- Same-segmentation sender extraction, following the active ValProof control
and payload proof. Empty values contribute count one and payload zero. -/
theorem val_size_sender {tr : Trace Fp} {tt : Nat} {pub : List Fp}
    (h : TableLocal valTable tr tt pub) (segs : List (Nat×Nat))
    (hc : Consec 0 segs) (hend : segEnd 0 segs≤tr.height tt)
    (hall : ∀ p∈segs, IsSeg (isOne tr tt ValV3.act)
      (isOne tr tt ValV3.vf) (isOne tr tt ValV3.vl) p.1 p.2)
    (hpad : ∀ r,segEnd 0 segs≤r → r<tr.height tt → isOne tr tt ValV3.act r=false) :
    (List.range (tr.height tt)).flatMap (fun r =>
      rowTraffic valTable.interactions tr tt r pub B_SIZE true) =
      [[1,(valPayload (segs.map (ValProof.valOf tr tt)):Fp),
        (((segs.map (ValProof.valOf tr tt)).filter fun v => !v.dup).length:Fp)]] := by
  have hL := val_local_base h
  have hpos : 0<tr.height tt := Nat.two_pow_pos _
  have hP : tr.height tt<P := by have := height_le hL; unfold P; omega
  have hH : ∀ p ∈ segs, p.1 + p.2 ≤ tr.height tt := fun p hp => by
    have := seg_le_end segs 0 hc p hp; omega
  have hinact : ∀ r, segEnd 0 segs ≤ r → r < tr.height tt → tr.cell tt r ValV3.act = 0 := fun r h1 h2 =>
    zero_of_not_one hL h2 (by simp [bools]) (hpad r h1 h2)
  obtain ⟨A, hA⟩ : ∃ A, A = segEnd 0 segs := ⟨_, rfl⟩
  have hlastSeg : segs ≠ [] → ∃ q ∈ segs, q.1 + q.2 = A := by
    intro hne
    obtain ⟨p, rest, rfl⟩ : ∃ p rest, segs = p :: rest := by
      cases segs with
      | nil => exact absurd rfl hne
      | cons p rest => exact ⟨p, rest, rfl⟩
    exact ⟨(p :: rest)[(p :: rest).length - 1]'(by simp), List.getElem_mem _,
      by rw [hA, segEnd_last (p :: rest) 0 hc (by simp)]⟩
  -- the SUM row is row A
  have hAlt : A < tr.height tt := by
    rcases Nat.lt_or_ge A (tr.height tt) with h | h
    · exact h
    · exfalso
      have hlast := lastRow hL hpos
      by_cases hne : segs = []
      · subst hne; simp [segEnd] at hA; omega
      · obtain ⟨q, hq, hqe⟩ := hlastSeg hne
        have hqa := (hall q hq).2.2.2.1 (q.1 + q.2 - 1) (by have := (hall q hq).1; omega)
          (by have := (hall q hq).1; omega)
        simp only [isOne, decide_eq_true_eq] at hqa
        have : q.1 + q.2 - 1 = tr.height tt - 1 := by have := hH q hq; have := (hall q hq).1; omega
        rw [this, hlast] at hqa; exact absurd hqa (by decide)
  have hsumA : tr.cell tt A ValV3.sumr = 1 := by
    have ha := hinact A (by omega) hAlt
    by_cases hne : segs = []
    · subst hne
      have h0 : A = 0 := by simp [segEnd] at hA; exact hA
      subst h0
      have := (row0 hL hpos).1
      rw [ha] at this; grind
    · obtain ⟨q, hq, hqe⟩ := hlastSeg hne
      have hvl : tr.cell tt (q.1 + q.2 - 1) ValV3.vl = 1 := by
        have := (hall q hq).2.2.1; simpa [isOne] using this
      have e : q.1 + q.2 - 1 + 1 = A := by have := (hall q hq).1; omega
      have := (afterSeg hL (r := q.1 + q.2 - 1) (by omega) hvl).1
      rw [e, ha] at this; grind
  have hsumAfter : ∀ r, A < r → r < tr.height tt → tr.cell tt r ValV3.sumr = 0 := by
    intro r h1 h2
    induction r with
    | zero => omega
    | succ r ih =>
      by_cases hr : r = A
      · subst hr; exact (padFacts hL h2 (hinact _ (by omega) (by omega))).2.2 hsumA
      · exact (padFacts hL h2 (hinact _ (by omega) (by omega))).2.1 (ih (by omega) (by omega))
  -- rows other than the segments and the SUM row carry nothing
  have hrow0 : ∀ bb sd r, A ≤ r → r < tr.height tt → bb ≠ B_SIZE ∨ r ≠ A →
      rowTraffic ValV3.interactions tr tt r pub bb sd = [] := by
    intro bb sd r h1 h2 h3
    have ha := hinact r (by omega) h2
    obtain ⟨hgb, hgdu, hz, -⟩ := rowFacts hL h2
    obtain ⟨hdu, hhd, hvf, -⟩ := hz ha
    have hs : bb ≠ B_SIZE ∨ tr.cell tt r ValV3.sumr = 0 := by
      rcases h3 with h | h
      · exact Or.inl h
      · exact Or.inr (hsumAfter r (by omega) h2)
    rw [rowT, hgb, hgdu, ha, hdu, hhd, hvf]
    have z1 : ∀ x : Fp, ¬ (0 : Fp) * x = 1 := fun x e => by grind
    rcases hs with h | h <;> simp [h, z1]
  -- sums over the segments
  have hsumℓ : (segs.map fun p => p.2).sum = A := by
    have := congrArg List.length (range'_segs segs 0 hc)
    simp only [List.length_range', Nat.sub_zero, List.length_flatMap] at this
    rw [hA, this]
  have hP2 : A < P := by omega
  have hsplit : List.range (tr.height tt) = (segs.flatMap fun p => List.range' p.1 p.2) ++
      ([A] ++ List.range' (A + 1) (tr.height tt - A - 1)) := by
    rw [List.range_eq_range', range'_split A _ (by omega), hA, ← range'_segs segs 0 hc, Nat.sub_zero, ← hA]
    congr 1
    rw [show tr.height tt - A = 1 + (tr.height tt - A - 1) by omega, ← List.range'_append_1]
    simp
  have hrest : ∀ bb sd, (List.range' (A + 1) (tr.height tt - A - 1)).flatMap
      (fun q => rowTraffic ValV3.interactions tr tt q pub bb sd) = [] :=
    fun bb sd => flatMap_nil' _ _ (fun q hq => by
      have := List.mem_range'.1 hq
      exact hrow0 bb sd q (by omega) (by omega) (Or.inr (by omega)))
  have hsegs : ∀ bb sd, (segs.flatMap fun p => List.range' p.1 p.2).flatMap
      (fun q => rowTraffic ValV3.interactions tr tt q pub bb sd) =
      segs.flatMap fun p => if bb = B_SIZE then [] else
        ((if sd then valSends [ValProof.valOf tr tt p] bb else valRecvs [ValProof.valOf tr tt p] bb)).map Msg.toFp := by
    intro bb sd
    rw [List.flatMap_assoc]
    exact flatMap_congr' (fun p hp => segTraffic hL (hall p hp) (hH p hp) bb sd)
  -- the SUM value
  have hgw : ∀ p ∈ segs, ((List.range' p.1 p.2).map (gw tr tt)).sum =
      if tr.cell tt p.1 ValV3.vz = 0 ∧ tr.cell tt p.1 ValV3.dup = 0 then p.2 else 0 := by
    intro p hp
    obtain ⟨hrow, -⟩ := segInfo hL (hall p hp) (hH p hp)
    rw [List.range'_eq_map_range, List.map_map]
    have : ∀ j ∈ List.range p.2, (gw tr tt ∘ fun j => p.1 + j) j =
        if tr.cell tt p.1 ValV3.vz = 0 ∧ tr.cell tt p.1 ValV3.dup = 0 then 1 else 0 := by
      intro j hj
      obtain ⟨ha, -, hk, -⟩ := hrow j (List.mem_range.1 hj)
      simp [gw, ha, hk ValV3.vz (by simp [ValV3.valConst]), hk ValV3.dup (by simp [ValV3.valConst])]
    rw [List.map_congr_left this]
    by_cases hcnd : tr.cell tt p.1 ValV3.vz = 0 ∧ tr.cell tt p.1 ValV3.dup = 0
    · simp only [hcnd, and_self, if_true]
      rw [sum_map_one]; simp
    · simp only [hcnd, if_false]; exact sum_map_zero' _
  have hszA : tr.cell tt A ValV3.sz =
      ((((segs.map (ValProof.valOf tr tt)).filter fun e => !e.vz && !e.dup).map ValE.len).sum : Nat) := by
    rw [sz_sum hL hpos A hAlt, List.range_eq_range', hA, ← Nat.sub_zero (segEnd 0 segs),
      range'_segs segs 0 hc, sum_flatMap]
    congr 1
    rw [List.map_congr_left hgw]
    apply sum_filter_map
    intro p hp
    obtain ⟨-, hz⟩ := segInfo hL (hall p hp) (hH p hp)
    have hvzb := isBool hL (r := p.1) (by have := (hall p hp).1; have := hH p hp; omega) (x := ValV3.vz) (by simp [bools])
    have hdub := isBool hL (r := p.1) (by have := (hall p hp).1; have := hH p hp; omega) (x := ValV3.dup) (by simp [bools])
    rcases hvzb with h1 | h1 <;> rcases hdub with h2 | h2
    · rcases hz with ⟨h, -⟩ | ⟨-, hl⟩
      · rw [h1] at h; exact absurd h (by decide)
      · simp [ValProof.valOf, h1, h2, hl, toNat_natCast, Nat.mod_eq_of_lt (show p.2 < P by have := hH p hp; omega)]
    all_goals simp [ValProof.valOf, h1, h2]
  have hA0 : tr.cell tt A ValV3.act = 0 := hinact A (by omega) hAlt
  obtain ⟨hgbA, hgduA, hzA, -⟩ := rowFacts hL hAlt
  obtain ⟨hduA, hhdA, hvfA, -⟩ := hzA hA0
  have hgbA0 : tr.cell tt A ValV3.gb = 0 := by rw [hgbA, hA0]; grind
  have hgduA0 : tr.cell tt A ValV3.gdu = 0 := by rw [hgduA, hvfA]; grind

  have hone : rowTraffic ValV3.interactions tr tt A pub B_SIZE true=
      [[1,(valPayload (segs.map (ValProof.valOf tr tt)):Fp)]] := by
    rw [rowT]
    simp only [hgbA0,hgduA0,hvfA,hhdA,hduA,hsumA]
    simp [valPayload,hszA,B_SIZE,B_BYTES,B_VBYTES,B_VPARENT,B_DUP,B_ENT]
  have hrows : (List.range (tr.height tt)).flatMap
      (fun r => rowTraffic ValV3.interactions tr tt r pub B_SIZE true)=
      [[1,(valPayload (segs.map (ValProof.valOf tr tt)):Fp)]] := by
    rw [hsplit,List.flatMap_append,List.flatMap_append,hrest,hsegs,List.append_nil,
      List.flatMap_singleton,hone]
    simp [flatMap_nil_fun]
  have hcount := val_count_view h segs hc (by omega) hall
  have hcf : tr.cell tt A valCount=
      (((segs.map (ValProof.valOf tr tt)).filter fun v => !v.dup).length:Fp) := by
    rw [hA,←hcount]; exact (Fp.ofNat_toNat _).symm
  have hx := decorate_singleton (List.range (tr.height tt))
    (fun r => rowTraffic ValV3.interactions tr tt r pub B_SIZE true)
    (fun r msg => msg++[tr.cell tt r valCount]) A
    [1,(valPayload (segs.map (ValProof.valOf tr tt)):Fp)] (List.mem_range.mpr hAlt) hone hrows
  simp only [valTable,rowTraffic_withCount,ite_true,eval_c]
  rw [hx,hcf]
  rfl

/-- A candidate-local value table supplies a concrete complete segmented view
and its exact arity-three SIZE message; no renderer premise is required. -/
theorem val_size_sender_exists {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h : TableLocal valTable tr t pub) :
    ∃ segs : List (Nat×Nat), Consec 0 segs ∧
      (∀ p∈segs, IsSeg (ValProof.isOne tr t ValV3.act)
        (ValProof.isOne tr t ValV3.vf) (ValProof.isOne tr t ValV3.vl) p.1 p.2) ∧
      (List.range (tr.height t)).flatMap (fun r =>
        rowTraffic valTable.interactions tr t r pub B_SIZE true) =
        [[1,(valPayload (segs.map (ValProof.valOf tr t)):Fp),
          (((segs.map (ValProof.valOf tr t)).filter fun v => !v.dup).length:Fp)]] := by
  have hl := val_local_base h
  have hpos : 0<tr.height t := Nat.two_pow_pos _
  obtain ⟨segs,hc,he,hs,hpad⟩ : ∃ segs : List (Nat×Nat), Consec 0 segs ∧
      segEnd 0 segs≤tr.height t ∧
      (∀ p∈segs, IsSeg (ValProof.isOne tr t ValV3.act)
        (ValProof.isOne tr t ValV3.vf) (ValProof.isOne tr t ValV3.vl) p.1 p.2) ∧
      (∀ r,segEnd 0 segs≤r → r<tr.height t → ValProof.isOne tr t ValV3.act r=false) := by
    by_cases ha : tr.cell t 0 ValV3.act=1
    · exact segments_of (ValProof.segFacts hl ha) hpos
    · refine ⟨[],trivial,by simp [segEnd],by simp,?_⟩
      have hz : ∀ r,r<tr.height t → tr.cell t r ValV3.act=0 := by
        intro r
        induction r with
        | zero => intro _; exact (ValProof.isBool hl hpos (x := ValV3.act) (by simp [ValProof.bools])).resolve_right ha
        | succ r ih => intro hr; exact (ValProof.padFacts hl hr (ih (by omega))).1
      intro r _ hr
      simp [ValProof.isOne,hz r hr]
  exact ⟨segs,hc,hs,val_size_sender h segs hc he hs hpad⟩

end ZkFormal.NearV3.Rcpt.Candidates.SizeCount
