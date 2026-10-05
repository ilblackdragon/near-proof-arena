import ZkFormal.Prover.BcsMulti

/-!
# ZkFormal.Prover.BcsPrefix — the commit phase: parse and hash chain agree

For one honest message `m` (fitting its parts, every header part `= hdr`, 64-byte
roots): `parseParts` reads back `withRoots m roots` from `msgBytes m roots`
(`parseParts_msg`).  Then (`ev_commitLoop`) the whole commit loop: the verifier's
`parseSlots` reads the prover's raw bytes back slot by slot, its `chain`
recomputes the prover's final state with the same entries up to erasure, and the
roots it reads are the roots of the prover's trees.
-/

set_option linter.unusedSectionVars false

namespace ZkFormal.Prover

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal.Stark

/-- The oracle payloads of a list of entries (as `PT.oracles`). -/
def entOracles {K O : Type} (es : List (Entry K O)) : List O := (PT.mk [] es).oracles

theorem oracles_eq {K O : Type} (cb : Bytes) (es : List (Entry K O)) :
    (PT.mk cb es).oracles = entOracles es := rfl

theorem entOracles_append {K O : Type} (a b : List (Entry K O)) :
    entOracles (a ++ b) = entOracles a ++ entOracles b := by
  simp [entOracles, PT.oracles, List.flatMap_append]

theorem entOracles_chal {K O : Type} (c : K) : entOracles ([.chal c] : List (Entry K O)) = [] := rfl

theorem entOracles_nil {K O : Type} : entOracles ([] : List (Entry K O)) = [] := rfl

/-- Oracle payloads of a message. -/
def partsOracles {K O : Type} (ps : List (PartV K O)) : List O := entOracles [.msg ps]

theorem entOracles_msg {K O : Type} (ps : List (PartV K O)) :
    entOracles [.msg ps] = partsOracles ps := rfl

theorem partsOracles_cons {K O : Type} (p : PartV K O) (ps : List (PartV K O)) :
    partsOracles (p :: ps) = (match p with | .oracle o => [o] | _ => []) ++ partsOracles ps := by
  cases p <;> simp [partsOracles, entOracles, PT.oracles]

section
variable {F K : Type} [Field F] [Field K] [StarkField F K] [StarkFieldLaws F K] [DecidableEq F]

theorem partsOracles_eq_msgOracles : ∀ m : List (PartV K (Oracle F)),
    partsOracles m = msgOracles m
  | [] => rfl
  | p :: ps => by
    rw [partsOracles_cons, partsOracles_eq_msgOracles ps]
    cases p <;> rfl

theorem withRoots_erase : ∀ (m : List (PartV K (Oracle F))) (roots : List Bytes),
    (withRoots (F := F) m roots).map PT.PartV.erase = m.map PT.PartV.erase
  | [], _ => rfl
  | .oracle _ :: ps, r :: rs => by simp [withRoots, PT.PartV.erase, withRoots_erase ps rs]
  | .oracle _ :: ps, [] => by simp [withRoots, PT.PartV.erase, withRoots_erase ps []]
  | .header _ :: ps, rs => by simp [withRoots, PT.PartV.erase, withRoots_erase ps rs]
  | .elems _ :: ps, rs => by simp [withRoots, PT.PartV.erase, withRoots_erase ps rs]

theorem withRoots_oracles : ∀ (m : List (PartV K (Oracle F))) (roots : List Bytes),
    roots.length = (msgOracles m).length → partsOracles (withRoots (F := F) m roots) = roots
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [msgOracles] at h
  | .oracle o :: ps, [], h => by simp [msgOracles] at h
  | .oracle o :: ps, r :: rs, h => by
    have h' : rs.length = (msgOracles ps).length := by
      rw [← partsOracles_eq_msgOracles] at h ⊢; simp [partsOracles_cons] at h; exact h
    simp only [withRoots]; rw [partsOracles_cons, withRoots_oracles ps rs h']; rfl
  | .header l :: ps, rs, h => by
    have h' : rs.length = (msgOracles ps).length := by
      rw [← partsOracles_eq_msgOracles] at h ⊢; simpa [partsOracles_cons] using h
    simp only [withRoots]; rw [partsOracles_cons, withRoots_oracles ps rs h']; rfl
  | .elems xs :: ps, rs, h => by
    have h' : rs.length = (msgOracles ps).length := by
      rw [← partsOracles_eq_msgOracles] at h ⊢; simpa [partsOracles_cons] using h
    simp only [withRoots]; rw [partsOracles_cons, withRoots_oracles ps rs h']; rfl

theorem rootsOf_eq (vs : List (PartV K Bytes)) : rootsOf vs = partsOracles vs := by
  induction vs with
  | nil => rfl
  | cons p ps ih => rw [partsOracles_cons, ← ih]; cases p <;> rfl

/-- **One honest message parses back.** -/
theorem parseParts_msg (hdr : List Nat) (hlen : hdr.length < 2 ^ 32) (hsmall : ∀ h ∈ hdr, h < 256) :
    ∀ {m : List (PartV K (Oracle F))} {parts : List Part}, Fits2 m parts →
    (∀ l, PartV.header l ∈ m → l = hdr) → ∀ roots : List Bytes,
    roots.length = (msgOracles m).length → (∀ r ∈ roots, r.length = 64) → ∀ rest : Bytes,
    parseParts (F := F) hdr parts (msgBytes (F := F) m roots ++ rest) =
      some (withRoots (F := F) m roots, rest)
  | [], [], .nil, _, roots, hl, _, rest => by
    have : roots = [] := by simpa [msgOracles] using hl
    subst this; rfl
  | p :: ps, q :: qs, .cons hpq hs, hh, roots, hl, hr64, rest => by
    have hh' : ∀ l, PartV.header l ∈ ps → l = hdr := fun l hm => hh l (List.mem_cons_of_mem _ hm)
    cases p with
    | header l =>
      cases q with
      | header n =>
        have hl' : roots.length = (msgOracles ps).length := by
          rw [← partsOracles_eq_msgOracles] at hl ⊢; simpa [partsOracles_cons] using hl
        have hlh := hh l (by simp); subst hlh
        have hfit : l.length = n := hpq
        subst hfit
        have ih := parseParts_msg l hlen hsmall hs hh' roots hl' hr64 rest
        simp only [msgBytes, partBytes, withRoots, parseParts, List.append_assoc,
          readHeader_encHeader l _ hlen hsmall, beq_self_eq_true, ite_true, ih]
      | oracle _ => exact (hpq : False).elim
      | elems _ => exact (hpq : False).elim
    | oracle o =>
      cases q with
      | oracle mats =>
        match roots, hl, hr64 with
        | [], hl, _ => simp [msgOracles] at hl
        | r :: rs, hl, hr64 =>
          have hl' : rs.length = (msgOracles ps).length := by
            rw [← partsOracles_eq_msgOracles] at hl ⊢; simpa [partsOracles_cons] using hl
          have ih := parseParts_msg hdr hlen hsmall hs hh' rs hl'
            (fun r' h' => hr64 r' (List.mem_cons_of_mem _ h')) rest
          have ht : take? 64 (r ++ (msgBytes (F := F) ps rs ++ rest)) =
              some (r, msgBytes (F := F) ps rs ++ rest) := by
            rw [← hr64 r (by simp)]; exact take?_append _ _
          simp only [msgBytes, partBytes, withRoots, parseParts, List.append_assoc, ht, ih]
      | header _ => exact (hpq : False).elim
      | elems _ => exact (hpq : False).elim
    | elems xs =>
      cases q with
      | elems n =>
        have hl' : roots.length = (msgOracles ps).length := by
          rw [← partsOracles_eq_msgOracles] at hl ⊢; simpa [partsOracles_cons] using hl
        have hfit : xs.length = n := hpq
        subst hfit
        have ih := parseParts_msg hdr hlen hsmall hs hh' roots hl' hr64 rest
        simp only [msgBytes, partBytes, withRoots, parseParts, List.append_assoc,
          readKs_enc, ih]
      | header _ => exact (hpq : False).elim
      | oracle _ => exact (hpq : False).elim

theorem rowsOk_of_fits {o : Oracle F} {mats : List (Nat × Nat)}
    (h : Udr.PartV.Fits (K := K) (.oracle o) (.oracle mats)) : RowsOk o := by
  intro M hM i hi
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hM
  obtain ⟨_, _, _, _, hrow⟩ := h.2 k hk
  exact hrow i hi

theorem rowsOk_msg : ∀ {m : List (PartV K (Oracle F))} {parts : List Part}, Fits2 m parts →
    ∀ o ∈ msgOracles m, RowsOk o
  | [], [], .nil => fun _ h => by cases h
  | p :: ps, q :: qs, .cons hpq hs => by
    intro o ho
    rw [← partsOracles_eq_msgOracles, partsOracles_cons, partsOracles_eq_msgOracles] at ho
    rcases List.mem_append.mp ho with h | h
    · cases p with
      | oracle o' =>
        simp only [List.mem_singleton] at h; subst h
        cases q with
        | oracle mats => exact rowsOk_of_fits hpq
        | header _ => exact (hpq : False).elim
        | elems _ => exact (hpq : False).elim
      | header _ => cases h
      | elems _ => cases h
    · exact rowsOk_msg hs o h

theorem zip_self_map {α β : Type} (f : α → β) : ∀ l : List α, l.zip (l.map f) = l.map fun a => (a, f a)
  | [] => rfl
  | a :: l => by simp [zip_self_map f l]

variable (H : Bytes → Bytes)

theorem ev_commitMsg (st : CState F K) (m : List (PartV K (Oracle F))) :
    ev H (commitMsg st m) =
      ⟨whp H tagAbs (absBody st.d ((msgOracles m).map fun o => rootOf (ev H (buildTree (K := K) o)))
          (clearOf (withRoots (F := F) m ((msgOracles m).map fun o => rootOf (ev H (buildTree (K := K) o))))
            (msgBytes (F := F) m ((msgOracles m).map fun o => rootOf (ev H (buildTree (K := K) o)))))),
        st.τ.push m,
        st.raw ++ msgBytes (F := F) m ((msgOracles m).map fun o => rootOf (ev H (buildTree (K := K) o))),
        st.trees ++ (msgOracles m).map fun o => (o, ev H (buildTree (K := K) o))⟩ := by
  simp only [commitMsg, ev_bind, ev_mapOC, ev_WH, ev_pure, List.map_map, Function.comp_def,
    zip_self_map]

variable {V : IopSpec F K} {pr : IopProver F K} {cb : Bytes}

/-- **The commit loop, evaluated** against the verifier's parser and hash chain. -/
theorem ev_commitLoop (hw : ProverWf V pr cb) (hH : ∀ m, (H m).length = 32) :
    ∀ (ss : List Slot) (st : CState F K), Inv V pr cb ss st.τ →
    ∃ (R : Bytes) (ps : List (PSlot K)) (ents : List (Entry K (Oracle F)))
      (entsV : List (Entry K Bytes)) (ts : List (Oracle F × List (List Bytes))),
      (ev H (commitLoop pr ss st)).τ = ⟨st.τ.cb, st.τ.entries ++ ents⟩ ∧
      (ev H (commitLoop pr ss st)).raw = st.raw ++ R ∧
      (ev H (commitLoop pr ss st)).trees = st.trees ++ ts ∧
      Inv V pr cb [] (ev H (commitLoop pr ss st)).τ ∧
      (∀ rest, parseSlots (F := F) pr.hdr ss (R ++ rest) = some (ps, rest)) ∧
      ev H (chain (F := F) st.d ps) = (entsV, (ev H (commitLoop pr ss st)).d) ∧
      entsV.map PT.Entry.erase = ents.map PT.Entry.erase ∧
      entOracles entsV = ts.map (fun t => rootOf t.2) ∧
      entOracles ents = ts.map Prod.fst ∧
      ts.map (fun t => shapesOf t.1) = schedOracles ss ∧
      ∀ t ∈ ts, t.2 = ev H (buildTree (K := K) t.1) ∧ RowsOk t.1
  | [], st, hi => by
    refine ⟨[], [], [], [], [], ?_, ?_, ?_, hi, fun rest => rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ h => by cases h⟩ <;> simp [commitLoop, ev_pure]
  | .msg parts :: ss, st, hi => by
    obtain ⟨hi1, hf⟩ := inv_msg hw hi
    have hnext := inv_next hw hi
    have hreach := hi.1
    generalize hm : pr.next st.τ = m at hi1 hf
    generalize hroots : (msgOracles m).map (fun o => rootOf (ev H (buildTree (K := K) o))) = roots
    have hst1 := ev_commitMsg H st m
    rw [hroots] at hst1
    generalize hs1 : ev H (commitMsg st m) = st1 at hst1
    have hτ1 : st1.τ = st.τ.push m := by rw [hst1]
    obtain ⟨R, ps, ents, entsV, ts, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
      ev_commitLoop hw hH ss st1 (hτ1 ▸ hi1)
    have hloop : ev H (commitLoop pr (.msg parts :: ss) st) = ev H (commitLoop pr ss st1) := by
      simp only [commitLoop, ev_bind, hm, hs1]
    rw [hloop]
    subst hst1
    have hlen : roots.length = (msgOracles m).length := by rw [← hroots]; simp
    have h64 : ∀ r ∈ roots, r.length = 64 := by
      intro r hr; rw [← hroots] at hr
      obtain ⟨o, _, rfl⟩ := List.mem_map.mp hr
      rw [buildTree_root]; exact node_length H o hH _ _ _
    have hhdr : ∀ l, PartV.header l ∈ m → l = pr.hdr := fun l hl =>
      hw.hdrParts st.τ hreach hnext l (hm ▸ hl)
    have hP := parseParts_msg (F := F) pr.hdr (by rw [hw.hdrLen]; exact hw.tablesSmall) hw.hdrSmall
      hf hhdr roots hlen h64
    refine ⟨msgBytes (F := F) m roots ++ R, .msg (withRoots (F := F) m roots) (msgBytes (F := F) m roots) :: ps,
      .msg m :: ents, .msg (withRoots (F := F) m roots) :: entsV,
      ((msgOracles m).map fun o => (o, ev H (buildTree (K := K) o))) ++ ts, ?_, ?_, ?_, h4, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [h1]; simp [PT.push]
    · rw [h2]; simp
    · rw [h3]; simp
    · intro rest
      simp only [parseSlots, List.append_assoc, hP, h5, take_consumed]
    · simp only [chain, ev_bind, ev_WH, rootsOf_eq, withRoots_oracles m roots hlen, h6, ev_pure]
    · simp only [List.map_cons, PT.Entry.erase, withRoots_erase, h7]
    · rw [show (Entry.msg (withRoots (F := F) m roots) :: entsV) = [.msg (withRoots (F := F) m roots)] ++ entsV
        from rfl, entOracles_append, entOracles_msg, withRoots_oracles m roots hlen, h8, ← hroots]
      simp
    · rw [show (Entry.msg m :: ents) = [.msg m] ++ ents from rfl, entOracles_append, entOracles_msg,
        partsOracles_eq_msgOracles, h9]
      simp [Function.comp_def]
    · rw [schedOracles_msg, ← msgShapes hf, ← h10]; simp
    · intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp ht
        exact ⟨rfl, rowsOk_msg hf o ho⟩
      · exact h11 t ht
  | .chal ood :: ss, st, hi => by
    have hi1 := inv_chal hw hi ((whp H tagChal st.d).take 32)
    obtain ⟨R, ps, ents, entsV, ts, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
      ev_commitLoop hw hH ss ⟨whp H tagChal st.d,
        st.τ.pushChal (Bcs.Transport.decChal (F := F) ood ((whp H tagChal st.d).take 32)),
        st.raw, st.trees⟩ hi1
    have hloop : ev H (commitLoop pr (.chal ood :: ss) st) = ev H (commitLoop pr ss ⟨whp H tagChal st.d,
        st.τ.pushChal (Bcs.Transport.decChal (F := F) ood ((whp H tagChal st.d).take 32)),
        st.raw, st.trees⟩) := by
      simp only [commitLoop, ev_bind_WH]
    rw [hloop]
    refine ⟨R, .chal ood :: ps, .chal (Bcs.Transport.decChal (F := F) ood ((whp H tagChal st.d).take 32)) :: ents,
      .chal (Bcs.Transport.decChal (F := F) ood ((whp H tagChal st.d).take 32)) :: entsV, ts,
      ?_, h2, h3, h4, ?_, ?_, ?_, ?_, ?_, ?_, h11⟩
    · rw [h1]; simp [PT.pushChal]
    · intro rest; simp only [parseSlots, h5]
    · simp only [chain, ev_bind, ev_WH, h6, ev_pure]
      cases ood <;> rfl
    · simp only [List.map_cons, PT.Entry.erase, h7]
    · rw [show (Entry.chal (Bcs.Transport.decChal (F := F) ood ((whp H tagChal st.d).take 32)) :: entsV) =
        [.chal _] ++ entsV from rfl, entOracles_append, entOracles_chal, h8]; rfl
    · rw [show (Entry.chal (Bcs.Transport.decChal (F := F) ood ((whp H tagChal st.d).take 32)) :: ents) =
        [.chal _] ++ ents from rfl, entOracles_append, entOracles_chal, h9]; rfl
    · rw [schedOracles_chal, h10]

end

end ZkFormal.Prover
