/-!
# Lane F, F-7: the STATE engine half's step contract `SeStep` from the opening rows and lane E's
M14 interface (`join/RestI.lean`)

Appended (by `join-check/run.sh`) to lane E's `join/StViewE.lean`, `join/StateW.lean`,
`join/RestI.lean` and lane F's `StateSE.lean`, elaborated in lane F's package environment.

The view's state parameters at the M14 cuts are lane E's `stViewParams_BI` (`PI`: lane B's with
the incremental remainder `encRestI`; `StateW`'s `stSem` still uses lane B's `PB`, whose `metaOf`
carries `encRestB`: finding **F7-1**, a lane E item — `stSemI` below is `stSem` with `PI`).

* **`open_in`** — from the opening rows (`SeOpen.SeOpenOK`, part of the leaf predicate `SeHoldsC`)
  and the input record being the view of `eng I c`: the received meta is the input's
  (`metaInS = metaOf PI v`), `v` is in the circuit form, and the opened remainder digests are
  `v`'s (`d_static`, `d_queue`, `d_move`) — lane E's `rest_open` over lane B's `StCommit.ser`
  (`open_ser`, a byte form of `tag_sound`) — or there is a SHA-384 collision.
* **`SeMove`** — the residual step contract (named, lane F): for the opened configuration, the
  step to `c'` (lane E's `Meaning .state`, `StatePreW`), the leaf's `SREQ`/`HB` change list, the
  output counters / accumulators (`FreeOut`), and **the closed moving part**: `tag_out = tagOf v'`,
  `d_move' = dMove (restOfB v')`, `d_queue' = dQueue (restOfB v')`, the static part unchanged.
  It no longer carries the input meta, the output meta, the `rest` encodings or the static digest:
  those are the rows' (`open_in`, `close_out`).
* **`seStep_of_move`** — F-5's named `SeC.SeStep` for the working-set mode is a theorem:
  circuit (`SeHoldsC`) + `SeMove` ⇒ `SeStep V (stSemI V) (StatePreW V) …`.
* **`stateSeg_relC8_I`** — the STATE working-set leaf is relatively, canonically sound with
  `V.stD = stD PI` (the M14 chain's state commitment): `SeC.se_engHalf` ∘ `seStep_of_move` ∧ lane
  B's `HoldsSt PI` (`stHalf_inst`) ∧ `reqsRel_stateI` (lane E's `reqsRel_state` with `PI`'s meta).
-/

namespace LaneF.SeStepI

open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd NearSpecV3.E2E.SB NearSpecV3.E2E.M8
open NearSpecV3.E2E.Glue StateM5a.StateView StateM5a.StateViewParams StateM5a.StHalfC LaneE.StateW
open LaneE.RestI M5T1.SeC M5T1.SeOpen NearSpecV3.E2E.T1 NearSpecV3.E2E.Enc

abbrev PI : StViewParams := stViewParams_BI

/-! ## 1. Opening `stRoot` from its serialization -/

/-- **`tag_sound` on bytes**: a 1-byte tag `t < 255` followed by `r` that hashes to `stD P v` is
`v`'s circuit-form commitment, or there is a collision. -/
theorem open_ser (P : StViewParams) (v : StV) (t : Nat) (ht : t < 255) (r : NearSpec.Bytes)
    (h : bdigest (UInt8.ofNat t :: r) = stD P v) :
    Sha384Coll ∨ (P.fits v = true ∧ UInt8.ofNat t :: r = (commitOf P v).ser) := by
  classical
  cases hf : P.fits v
  · simp only [stD, hf, Bool.false_eq_true, ite_false] at h
    rcases coll_or_eq h with c | e
    · exact .inl c
    · simp only [List.cons.injEq] at e
      exfalso
      have := congrArg UInt8.toNat e.1
      simp at this
      omega
  · simp only [stD, hf, ite_true] at h
    rcases coll_or_eq h with c | e
    · exact .inl c
    · exact .inr ⟨rfl, e⟩

theorem cb_len (tr : ZkFormal.Air.Trace ZkFormal.Algebra.Fp) (s : String) : (cb tr s).length = digestLen := by
  simp [cb, digestLen]

theorem serIn_cons (tr : ZkFormal.Air.Trace ZkFormal.Algebra.Fp) :
    serIn tr = UInt8.ofNat (col tr "tgi") ::
      (cb tr "wsi" 48 ++ cb tr "wli" 8 ++ cb tr "tri" 32 ++ cb tr "ixi" 8 ++ cb tr "rsi") := by
  simp [serIn]

/-- **What the opening rows give about the input** (module doc). -/
theorem open_in (tr : ZkFormal.Air.Trace ZkFormal.Algebra.Fp) (pub : List ZkFormal.Algebra.Fp) (v : StV)
    (hO : SeOpenOK pub tr) (hst : M5T1.SegRt.bytesOf pub (M5T1.BndLay.engF.off "stRoot") 42 = stD PI v) :
    Sha384Coll ∨ (PI.fits v = true ∧ metaInS tr = metaOf PI v ∧ cb tr "dS" = dStatic (restOfB v) ∧
      cb tr "dQ" = dQueue (restOfB v) ∧ cb tr "dM" = dMove (restOfB v)) := by
  obtain ⟨h0, htg, h1, -, -, -, -, -⟩ := hO
  rw [hst, serIn_cons] at h0
  rcases open_ser PI v _ htg _ h0 with c | ⟨hf, he⟩
  · exact .inl c
  rw [ser_cons] at he
  simp only [List.cons.injEq] at he
  obtain ⟨et, er⟩ := he
  -- the tag
  have htag : col tr "tgi" = tagOf v := by
    have := congrArg UInt8.toNat et
    have h9 := tagOf_le v
    simp at this
    have ht' : (commitOf PI v).tag = tagOf v := rfl
    rw [ht'] at this
    omega
  -- the received rest is the commitment's
  obtain ⟨-, hr⟩ := List.append_inj' er (by
    rw [cb_len]; exact ((commitOf_wf PI v hf).2.2.2.2.2).symm)
  have hrest : cb tr "rsi" = bdigest (encRestI (restOfB v)) := hr
  rcases rest_open (restOfB v) _ _ _ (cb_len tr "dS") (cb_len tr "dQ")
    (by rw [← List.append_assoc, h1, hrest]) with c | ⟨e1, e2, e3⟩
  · exact .inl c
  refine .inr ⟨hf, ?_, e1, e2, e3⟩
  show (⟨M5T1.SeC.seCol tr "tgi", M5T1.SeC.seBytes tr "rsi"⟩ : StMeta) = ⟨tagOf v, bdigest (encRestI (restOfB v))⟩
  rw [← hrest, ← htag]
  rfl

/-- **The closed meta**: with the stepped moving part's digest, queue digest and the static digest,
the sent meta is `metaOf PI v'`. -/
theorem close_out (tr : ZkFormal.Air.Trace ZkFormal.Algebra.Fp) (pub : List ZkFormal.Algebra.Fp) (v' : StV)
    (hO : SeOpenOK pub tr) (ht : M5T1.SeC.seCol tr "tgo" = tagOf v')
    (hS : cb tr "dSo" = dStatic (restOfB v')) (hQ : cb tr "dQo" = dQueue (restOfB v'))
    (hM : cb tr "dMo" = dMove (restOfB v')) : metaOutS tr = metaOf PI v' := by
  obtain ⟨-, -, -, h2, -, -, -, -⟩ := hO
  show (⟨M5T1.SeC.seCol tr "tgo", M5T1.SeC.seBytes tr "rso"⟩ : StMeta) = ⟨tagOf v', bdigest (encRestI (restOfB v'))⟩
  rw [ht]
  congr 1
  show cb tr "rso" = _
  rw [← h2, hS, hQ, hM]
  simp only [encRestI, List.append_assoc]

/-- `d_static` depends only on the static part. -/
theorem dStatic_of (r r' : RestB) (h : restStatic r' = restStatic r) : dStatic r' = dStatic r := by
  simp only [restStatic, Prod.mk.injEq] at h
  simp only [dStatic, dKeys, dShape, restKeys, restShape, h.1, h.2]

/-! ## 2. The STATE split with `PI` (finding F7-1) -/

/-- `StateW.stSem` with lane E's incremental remainder in the meta. -/
def stSemI (V : ViewImpl) {A : Airs8} {HoldsE HoldsS joint} :
    SplitSem (stAir (A := A) HoldsE HoldsS joint) where
  wIn x := V.stD (stV V x)
  wOut x := V.stD (stV V x)
  qOf x x' := ⟨netW x x', metaOf PI (stV V x), metaOf PI (stV V x')⟩
  apply _ r := r

/-- **Lane E's `reqsRel_state` with `PI`'s meta** (the other parts of `StepRel` do not see `encRest`). -/
theorem reqsRel_stateI (V : ViewImpl) {A : Airs8} {HoldsE HoldsS joint} :
    ReqsRelOn (stSemI V (A := A) (HoldsE := HoldsE) (HoldsS := HoldsS) (joint := joint))
      (fun q x x' => stRel PI V q x x') (StatePreW V) := by
  intro x x' hm hp
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := reqsRel_state V (A := A) (HoldsE := HoldsE) (HoldsS := HoldsS)
    (joint := joint) x x' hm hp
  exact ⟨h1, h2, h3, h4, h5, rfl⟩

/-! ## 3. The residual contract and `SeStep` -/

/-- **The residual step contract** (named, lane F; module doc). Hypotheses: what the opening rows
established about the input (`open_in`). -/
def SeMove (V : ViewImpl) (xtape : Tp) : Prop :=
  ∀ (d d' : NearSpec.Bytes) (w : SeW) (I : Intake) (c : EConf), SeHoldsC xtape d d' w →
    (V.bnd (.base (.eng I c))).encode = M5T1.SegRt.bytesOf w.1 0 450 →
    metaInS w.2.1 = metaOf PI (stV V (.base (.eng I c))) →
    cb w.2.1 "dS" = dStatic (restOfB (stV V (.base (.eng I c)))) →
    cb w.2.1 "dQ" = dQueue (restOfB (stV V (.base (.eng I c)))) →
    cb w.2.1 "dM" = dMove (restOfB (stV V (.base (.eng I c)))) →
    Sha384Coll ∨ ∃ c', Meaning .state (.base (.eng I c)) (.base (.eng I c')) ∧
      StatePreW V (.base (.eng I c)) (.base (.eng I c')) ∧
      (qOfS w).w = netW (.base (.eng I c)) (.base (.eng I c')) ∧ FreeOut V (.base (.eng I c')) w.1 ∧
      M5T1.SeC.seCol w.2.1 "tgo" = tagOf (stV V (.base (.eng I c'))) ∧
      cb w.2.1 "dMo" = dMove (restOfB (stV V (.base (.eng I c')))) ∧
      cb w.2.1 "dQo" = dQueue (restOfB (stV V (.base (.eng I c')))) ∧
      restStatic (restOfB (stV V (.base (.eng I c')))) = restStatic (restOfB (stV V (.base (.eng I c))))

/-- **F-5's `SeStep` (working-set mode) from the circuit and `SeMove`.** -/
theorem seStep_of_move {V : ViewImpl} (hV : M5T1.ResumeC.RsView V) (hVst : V.stD = stD PI) (xtape : Tp)
    {A : Airs8} {HoldsE HoldsS joint} (hM : SeMove V xtape) :
    SeStep V (stSemI V (A := A) (HoldsE := HoldsE) (HoldsS := HoldsS) (joint := joint)) (StatePreW V) xtape
      (fun w r' => r' = rOutS w.1) qOfS := by
  intro d d' w r' I c hh hro he
  obtain ⟨pub, tr, gh⟩ := w
  obtain ⟨H, hb, hd, hd', hO⟩ := hh
  -- the input record's `stRoot` is the view's
  have hin := M5T1.SeSem.fields_eng (hV.wf _) (eng_wasm hV I c) (eng_out hV I c) he
  have hst : M5T1.SegRt.bytesOf pub (M5T1.BndLay.engF.off "stRoot") 42 = stD PI (stV V (.base (.eng I c))) := by
    rw [← hVst]; exact ((hin ("stRoot", 42) (by decide)) : (V.bnd (.base (.eng I c))).stRoot = _).symm
  rcases open_in tr pub _ hO hst with hc | ⟨-, hmi, hS, hQ, hMv⟩
  · exact .inl hc
  rcases hM d d' ⟨pub, tr, gh⟩ I c ⟨H, hb, hd, hd', hO⟩ he hmi hS hQ hMv with hc |
    ⟨c', hm, hp, hw, hfree, htg, hMo, hQo, hstat⟩
  · exact .inl hc
  -- the working-set mode closes a non-`done` state: `fin = 0`, the static digest is copied
  have hfin : col tr "fin" ≠ 1 := by
    intro hf
    obtain ⟨-, h3, -⟩ := hO.2.2.2.2.2.2.1 hf
    have h3' : tagOf (stV V (.base (.eng I c'))) = 3 := by rw [← htg]; exact h3
    rw [show stV V (.base (.eng I c')) = stOfI V.keys I c' from rfl, tagOf_stOfI] at h3'
    obtain ⟨out, hout⟩ := posTag_eq3 h3'
    exact hp.2.2 I c' out rfl hout
  have hSo' : cb tr "dSo" = dStatic (restOfB (stV V (.base (.eng I c')))) := by
    rw [hO.2.2.2.2.2.2.2 hfin, hS, dStatic_of _ _ hstat]
  have hmo := close_out tr pub _ hO htg hSo' hQo hMo
  refine .inr ⟨c', hm, hp, ?_, fun hw' => hw'.trans hro, hfree⟩
  show (⟨(qOfS (pub, tr, gh)).w, metaInS tr, metaOutS tr⟩ : StQ) = _
  rw [hw, hmi, hmo]; rfl

/-- **Lane F's engine half for the working-set mode at M14** (`EngHalfRCOn` on `StatePreW`). -/
theorem state_engHalfI {sf : Intake → NearSpecV3.Wasm.TTN.Store} {V : ViewImpl}
    (hV : M5T1.ResumeC.RsView V) (hVst : V.stD = stD PI) (xtape : Tp) {HoldsS joint}
    (hM : SeMove V xtape) :
    EngHalfRCOn sf V (stSemI V (A := seAirs xtape) (HoldsE := LaneF.StateSE.segHoldsE xtape)
      (HoldsS := HoldsS) (joint := joint)) (StatePreW V) Sha384Coll :=
  se_engHalf hV _ _ xtape _ qOfS id (fun _ => rfl)
    (fun _ _ _ _ _ _ ⟨w, h, hq, hr, hr'⟩ => ⟨w, h, hq, hr, hr'⟩) (seStep_of_move hV hVst xtape hM)

/-- **The STATE working-set leaf is relatively, canonically sound at M14** (`SE` with the opening
rows ∧ lane B's `HoldsSt PI` ∧ `SeMove`). -/
theorem stateSeg_relC8_I {sf : Intake → NearSpecV3.Wasm.TTN.Store} {V : ViewImpl}
    (hV : M5T1.ResumeC.RsView V) (hVst : V.stD = stD PI) (xtape : Tp)
    {HoldsS : StQ → NearSpec.Bytes → NearSpec.Bytes → Prop}
    {joint : ∀ ctx b b' (tr : (seAirs xtape).Tr (.tmpl .state)), (seAirs xtape).Holds (.tmpl .state) ctx b b' tr →
      ∃ q r r', LaneF.StateSE.segHoldsE xtape ctx b b' q r r' ∧ HoldsS q r r'}
    (hM : SeMove V xtape) (hB : ∀ q r r', HoldsS q r r' → HoldsSt PI q r r') :
    TmplSoundRel8C sf V (seAirs xtape) Sha384Coll .state := by
  have hSt := stHalf_inst PI (stAir (A := seAirs xtape) (LaneF.StateSE.segHoldsE xtape) HoldsS joint) V hVst
    (stSemI V (A := seAirs xtape) (HoldsE := LaneF.StateSE.segHoldsE xtape) (HoldsS := HoldsS) (joint := joint))
    rfl rfl (fun _ => rfl) (fun _ => rfl) (fun q r r' h => hB q r r' h)
  exact split_sound_relC_relOn sf V _ _ (fun q x x' => stRel PI V q x x') (StatePreW V) Sha384Coll
    (state_engHalfI hV hVst xtape hM) (fun q r r' h => hSt q r r' h) (reqsRel_stateI V)

/-! ## 4. The finalize mode (`fin = 1`): what the rows add -/

theorem restKeys_stOfI (κ : Intake → List NearSpec.Bytes) (I : Intake) (c : EConf) :
    restKeys (restOfB (stOfI κ I c)) = κ I := by
  obtain ⟨p, st⟩ := c
  cases p <;> rfl

theorem restShape_done (κ : Intake → List NearSpec.Bytes) (I : Intake) (c : EConf) (out : MainOutD2)
    (h : c.pos = .done out) : restShape (restOfB (stOfI κ I c)) = none := by
  obtain ⟨p, st⟩ := c
  simp only at h; subst h; rfl

theorem dQueue_yields (κ : Intake → List NearSpec.Bytes) (I : Intake) (c : EConf) {yf yn i k : Nat} {rs : RS}
    (h : c.pos = .yields yf yn 0 i k rs) : dQueue (restOfB (stOfI κ I c)) = bdigest [] := by
  obtain ⟨p, st⟩ := c
  simp only at h; subst h; rfl

theorem dQueue_done (κ : Intake → List NearSpec.Bytes) (I : Intake) (c : EConf) (out : MainOutD2)
    (h : c.pos = .done out) : dQueue (restOfB (stOfI κ I c)) = bdigest [] := by
  obtain ⟨p, st⟩ := c
  simp only at h; subst h; rfl

theorem enc_none : Ser.enc (none : Option PTrie) = [0] := rfl

/-- **The finalize step's position from one byte**: an opened `tag_in = 8` (`fin = 1`) makes the input
configuration `yields _ _ 0` (`GlueFin.FinPre`'s position, lane E's `finPos_of_tag`). -/
theorem fin_pos (tr : ZkFormal.Air.Trace ZkFormal.Algebra.Fp) (pub : List ZkFormal.Algebra.Fp) (κ : Intake → List NearSpec.Bytes) (I : Intake)
    (c : EConf) (hO : SeOpenOK pub tr) (hf : col tr "fin" = 1)
    (hmi : metaInS tr = metaOf PI (stOfI κ I c)) :
    ∃ yf yn i k rs, c.pos = .yields yf yn 0 i k rs := by
  have h8 := (hO.2.2.2.2.2.2.1 hf).1
  have := congrArg StMeta.tag hmi
  change col tr "tgi" = tagOf (stOfI κ I c) at this
  rw [tagOf_stOfI, h8] at this
  exact posTag_eq8 this.symm

/-- **The finalize step's closed meta from the rows**: in the finalize mode the static digest is
swapped in-circuit (`d_keys` copied, `d_shape' = bdigest (Ser.enc none)`) and the queue copied, so
for a `done` output whose moving part's digest is `d_move'`, the sent meta is `metaOf PI v'` (tag 3
in-circuit), or there is a collision. -/
theorem fin_meta_out (tr : ZkFormal.Air.Trace ZkFormal.Algebra.Fp) (pub : List ZkFormal.Algebra.Fp) (κ : Intake → List NearSpec.Bytes)
    (I : Intake) (c c' : EConf) (hO : SeOpenOK pub tr) (hf : col tr "fin" = 1)
    (hy : ∃ yf yn i k rs, c.pos = .yields yf yn 0 i k rs) (out : MainOutD2) (hd : c'.pos = .done out)
    (hS : cb tr "dS" = dStatic (restOfB (stOfI κ I c))) (hQ : cb tr "dQ" = dQueue (restOfB (stOfI κ I c)))
    (hM : cb tr "dMo" = dMove (restOfB (stOfI κ I c'))) :
    Sha384Coll ∨ metaOutS tr = metaOf PI (stOfI κ I c') := by
  obtain ⟨-, h3, hQo, hK, hKo, hN⟩ := hO.2.2.2.2.2.2.1 hf
  rcases static_open (restOfB (stOfI κ I c)) _ _ (cb_len tr "dK") (by rw [hK, hS]) with hc | ⟨eK, -⟩
  · exact .inl hc
  obtain ⟨yf, yn, i, k, rs, hy⟩ := hy
  refine .inr (close_out tr pub _ hO ?_ ?_ ?_ hM)
  · show col tr "tgo" = _
    rw [h3, tagOf_stOfI, hd]; rfl
  · rw [← hKo, eK, ← hN]
    simp only [dStatic, dKeys, dShape, restKeys_stOfI, restShape_done κ I c' out hd, enc_none]
  · rw [hQo, hQ, dQueue_yields κ I c hy, dQueue_done κ I c' out hd]

/-! ## 5. The resume edge (`RsStep`) with lane E's interface: what the composition gives -/

/-- **The resume's receipt pop and close** (item 2): if the resume leaf's rows opened the input
state component `v` (its meta is `metaOf PI v`, as `open_in` gives from an `SH`-style opening of
`r_in`), opened `rest_in` into `(dS, dQ, dM)`, popped `dQ` into `(dT, a)` with `a = Ser.enc r`, and
closed `rest_out` from `dS`, `dT` and the stepped moving part's digest, then (modulo `Sha384Coll`)
the input position is `incoming (r :: rest) rs` — **`r` is the receipt the step executes** — the
remaining queue is `rest`, and the sent meta is `metaOf PI v'` for any `v'` with the stepped moving
part, queue `rest` and the static part unchanged. -/
theorem resume_pop_close (v v' : StV) (mi mo : StMeta) (hmi : metaOf PI v = mi)
    (dS dQ dM dT : NearSpec.Bytes) (x : StV × Option (List NearSpec.Bytes × List (NearSpec.Bytes × Option NearSpec.Bytes) × Nat))
    (r : Rcpt) (h1 : dS.length = digestLen) (h2 : dQ.length = digestLen) (hT : dT.length = digestLen)
    (hr : bdigest (dS ++ (dQ ++ dM)) = mi.rest) (hm : bdigest (Ser.enc x) = dM)
    (hp : bdigest (dT ++ Ser.enc r) = dQ) (h7 : mi.tag = 7)
    (hS' : restStatic (restOfB v') = restStatic (restOfB v)) (hQ' : dQueue (restOfB v') = dT)
    (ht' : mo.tag = tagOf v')
    (hmo : mo.rest = bdigest (dS ++ (dT ++ dMove (restOfB v')))) :
    Sha384Coll ∨ ((∃ p st rest rs, v = .eng p st ∧ p = .incoming (r :: rest) rs) ∧
      x = restMove (restOfB v) ∧ metaOf PI v' = mo) := by
  rcases open_pop v mi hmi dS dQ dM dT (Ser.enc r) x h1 h2 hT hr hm hp with hc | ⟨htag, eS, ex, tl, hq, -⟩
  · exact .inl hc
  refine .inr ⟨?_, ex, ?_⟩
  · cases v with
    | eng p st =>
      have hp7 : posTag p = 7 := by rw [← h7, htag]; rfl
      obtain ⟨r', rest, rs, rfl, er, -⟩ := incoming_head hq hp7
      exact ⟨_, st, rest, rs, rfl, by rw [Ser.pf.inj er]⟩
    | none => simp [pendQ] at hq
    | fin o => simp [pendQ] at hq
  · show (⟨tagOf v', bdigest (encRestI (restOfB v'))⟩ : StMeta) = mo
    obtain ⟨t, rr⟩ := mo
    simp only at ht' hmo
    rw [ht', hmo, eS, ← dStatic_of _ _ hS', ← hQ']
    rfl

end LaneF.SeStepI

#print axioms LaneF.SeStepI.open_ser
#print axioms LaneF.SeStepI.open_in
#print axioms LaneF.SeStepI.close_out
#print axioms LaneF.SeStepI.reqsRel_stateI
#print axioms LaneF.SeStepI.seStep_of_move
#print axioms LaneF.SeStepI.state_engHalfI
#print axioms LaneF.SeStepI.stateSeg_relC8_I
#print axioms LaneF.SeStepI.fin_pos
#print axioms LaneF.SeStepI.fin_meta_out
#print axioms LaneF.SeStepI.resume_pop_close
