import ZkFormal.Near.Extract.ShaFacts

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Sha NearSpec

/-- An arbitrary physical SHA table, using the existing shared bus IDs. -/
def shaCountAt (tr : Trace Fp) (pub : List Fp) (t : Nat) (send : Bool)
    (b : Nat) (m : List Fp) : Nat :=
  tableBusCount (Sha.Table.interactions B_BYTES B_DIGEST) tr t pub b send m

/-- Existing closed SHA extraction generalized from table zero to any index.
The proof follows Near.Extract.ShaFacts.shaFacts with the index explicit. -/
theorem shaFactsAt (tr : Trace Fp) (pub : List Fp) (t : Nat)
    (hL : Sha.ShaLocal tr t pub) :
    ShaFacts (shaCountAt tr pub t true) (shaCountAt tr pub t false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b m hb
    simp only [shaCountAt, tableBusCount_eq]
    apply List.count_eq_zero_of_not_mem
    intro hm
    simp only [List.mem_flatMap, rowTraffic, List.mem_range] at hm
    obtain ⟨r, -, i, hi, hm⟩ := hm
    rcases sha_mem hi with ⟨-, hs⟩ | rfl
    · simp [hs] at hm
    · simp [shaDigestI_bus.1, Ne.symm hb] at hm
  · intro b m hb
    simp only [shaCountAt, tableBusCount_eq]
    apply List.count_eq_zero_of_not_mem
    intro hm
    simp only [List.mem_flatMap, rowTraffic, List.mem_range] at hm
    obtain ⟨r, -, i, hi, hm⟩ := hm
    rcases sha_mem hi with ⟨hbb, -⟩ | rfl
    · simp [hbb, Ne.symm hb] at hm
    · simp [shaDigestI_bus.2] at hm
  · intro m hm
    simp only [shaCountAt, tableBusCount_eq] at hm
    have hm := mem_of_count_pos hm
    simp only [List.mem_flatMap, rowTraffic, List.mem_range] at hm
    obtain ⟨d, hd, i, hi, hmi⟩ := hm
    by_cases hbs : i.bus = B_DIGEST ∧ i.send = true
    · rw [if_pos hbs] at hmi
      obtain ⟨hpos, rfl⟩ := List.mem_replicate.mp hmi
      -- the active send is the digest interaction, so its bit is 1
      have hi16 : i = shaDigestI := by
        rcases sha_mem hi with ⟨-, hs⟩ | h
        · rw [hbs.2] at hs; cases hs
        · exact h
      subst hi16
      have hmult : tr.cell t d Layout.colDmult = 1 := by
        refine Classical.byContradiction fun hne => hpos ?_
        simp [shaDigestI, Interaction.multNat, Interaction.multNat.go, Sha.Table.interactions,
          Expr.eval, Expr.evalWith, rowEnv, Sha.Table.E.c, hne]
      obtain ⟨m', dg, -, hdg, hmsg, hbytes⟩ :=
        sha_digest_contract_closed hL B_BYTES B_DIGEST hd hmult
      refine ⟨tr.cell t d Layout.colId, m', ?_, ?_⟩
      · rw [show shaDigestI = (Sha.Table.interactions B_BYTES B_DIGEST)[16]! from rfl, hmsg, hdg]
      · intro j hj
        obtain ⟨r, hr, q, hq, hfq, hmq⟩ := hbytes j hj
        simp only [shaCountAt, tableBusCount_eq]
        apply count_pos_of_mem
        simp only [List.mem_flatMap, rowTraffic, List.mem_range]
        obtain ⟨hmem, hbus, hsend, hmul⟩ := sha_is_bytes q hq
        refine ⟨r, hr, _, hmem, ?_⟩
        rw [if_pos ⟨hbus, hsend⟩]
        have hgd : (m'.getD j 0) = m'[j]! := by
          rw [List.getD_eq_getElem?_getD, getElem!_def]; cases m'[j]? <;> rfl
        rw [hgd, ← hmq]
        apply List.mem_replicate.mpr
        refine ⟨?_, rfl⟩
        rw [Interaction.multNat, hmul]
        simp [Interaction.multNat.go, Expr.eval, Expr.evalWith, rowEnv, hfq]
    · rw [if_neg hbs] at hmi; simp at hmi


/-- Sum over an explicitly chosen list of physical SHA tables. Callers retain
ownership and global bus balance obligations; no sole-DIGEST-sender axiom is used. -/
def shaUnionCount (tr : Trace Fp) (pub : List Fp) : List Nat → Bool → Nat → List Fp → Nat
  | [],_,_,_ => 0
  | t::ts,sd,b,m => shaCountAt tr pub t sd b m+shaUnionCount tr pub ts sd b m

theorem shaUnionFacts (tr : Trace Fp) (pub : List Fp) (ts : List Nat)
    (hlocal : ∀t∈ts,Sha.ShaLocal tr t pub) :
    ShaFacts (shaUnionCount tr pub ts true) (shaUnionCount tr pub ts false) := by
  induction ts with
  | nil =>
    refine ⟨fun _ _ _ => rfl,fun _ _ _ => rfl,?_⟩
    intro m hm; simp [shaUnionCount] at hm
  | cons t ts ih =>
    have hh := shaFactsAt tr pub t (hlocal t (by simp))
    have ht := ih (fun u hu=>hlocal u (by simp [hu]))
    refine ⟨?_,?_,?_⟩
    · intro b m hb
      simp only [shaUnionCount,hh.sends_only_digest b m hb,ht.sends_only_digest b m hb]
    · intro b m hb
      simp only [shaUnionCount,hh.recvs_only_bytes b m hb,ht.recvs_only_bytes b m hb]
    · intro m hm
      by_cases hp : 0<shaCountAt tr pub t true B_DIGEST m
      · obtain ⟨id,bs,he,hbytes⟩ := hh.digest m hp
        refine ⟨id,bs,he,?_⟩
        intro i hi
        have hb := hbytes i hi
        simp only [shaUnionCount]
        omega
      · have hp' : 0<shaUnionCount tr pub ts true B_DIGEST m := by
          simp only [shaUnionCount] at hm;omega
        obtain ⟨id,bs,he,hbytes⟩ := ht.digest m hp'
        refine ⟨id,bs,he,?_⟩
        intro i hi
        have hb := hbytes i hi
        simp only [shaUnionCount]
        omega

end ZkFormal.NearV3.Assembly
