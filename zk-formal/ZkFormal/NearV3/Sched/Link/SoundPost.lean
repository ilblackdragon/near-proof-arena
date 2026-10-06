import ZkFormal.NearV3.Sched.Link.SoundSha

/-!
# ZkFormal.NearV3.Sched.Link.SoundPost — the post bytes are the core's new state (stage D step 2)

For instance τ with process key block `f` (rounds `m`) and `stF` the spec's final process state
(`specSt … (lpState … (codecA0 τ) …) m`, the state `proc_core'''` composes):

* **`codec_ash`**: the last 32 hash-input bytes are `Ps[τ].ash` (public `SPUBB` records);
* **`codec_hash`**: the post hash is `sha256 (h0Of τ ‖ Ps[τ].ash)` (`codec_digest`);
* **`sched_post`**: `svOf τ` (the bytes sent on `SPOST`, `codec_schedVal`) is
  `State.encode ⟨canonLinks Ps[τ].ids stF.allowance, sha256 (h0Of τ ‖ Ps[τ].ash)⟩`:
  `codec_post_encode`, ids by the `SDL` line (`codec_ids`), allowances by `codec_afin` (memory FIN).
-/

namespace ZkFormal.NearV3.Sched

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha ZkFormal.Chacha.Table.E
open NearSpecV3 NearSpecV3.Scheduler

/-- A public `SPUBB` record matching `(τ, 2, j, b, 0, 0, 0)` is `ash` byte `j` of instance τ. -/
theorem ash_msg {Ps : List InstPub} {fwd : List (Nat × Nat)} (hlen : Ps.length < 2013265921)
    {M : List Fp} (hM : M ∈ (render Ps fwd).pubb.map (·.map Fp.ofNat))
    {τ j b : Nat} (hτ : τ < 2013265921) (hj : j < 32) (hb : b < 2013265921)
    (e : M = [τ, TAG_ASH, j, b, 0, 0, 0].map Fp.ofNat) :
    τ < Ps.length ∧ b = ((Ps.getD τ instD).ash.getD j 0).toNat := by
  subst e
  obtain ⟨r, hr, hre⟩ := List.mem_map.1 hM
  rw [render_pubb, List.mem_append, List.mem_flatMap] at hr
  have u8 : ∀ (x : UInt8), x.toNat < 2013265921 := fun x => by have := x.toNat_lt; omega
  rcases hr with ⟨τ', hτ', hr⟩ | hr
  · rw [List.mem_append] at hr
    rcases hr with hr | hr
    · simp only [keyRecs, List.mem_map] at hr
      obtain ⟨k, -, rfl⟩ := hr
      simp only [List.map_cons, List.cons.injEq] at hre
      exact absurd (ofNat_inj' (by decide) (by decide) hre.2.1) (by simp [TAG_ASH, TAG_KEY])
    · simp only [ashRecs, List.mem_map, List.mem_range] at hr
      obtain ⟨k, hk, rfl⟩ := hr
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at hre
      obtain ⟨e1, -, e3, e4, -⟩ := hre
      have h1 := ofNat_inj' (by have := List.mem_range.1 hτ'; omega) hτ e1
      have h3 := ofNat_inj' (by omega) (by omega) e3
      have h4 := ofNat_inj' (u8 _) hb e4
      subst h1 h3
      exact ⟨List.mem_range.1 hτ', h4.symm⟩
  · simp only [fwdRecs, List.mem_map] at hr
    obtain ⟨l, -, rfl⟩ := hr
    simp only [List.map_cons, List.map_append, List.cons_append, List.cons.injEq] at hre
    exact absurd (ofNat_inj' (by decide) (by decide) hre.2.1) (by simp [TAG_FWD, TAG_ASH])

section
variable {AP : AirP} {pub : List Fp} {tr : Trace Fp}

/-- **The `ash` half of the hash input.** -/
theorem codec_ash (hH : HoldsP AP pub tr) {tc : Nat} (O : CodecValOwn AP tc) (PB : PubbOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrecB : I.recs B_SPUBB true = (render Ps fwd).pubb) (hlen : Ps.length < 2013265921)
    {f : Nat} (hf : f < tr.height tc) (hF : cv tr tc f Codec.kF = 1) {j : Nat} (hj : j < 32) :
    Codec.shaByte tr tc f (32 + j) = ((Ps.getD (cv tr tc f Codec.tau) instD).ash.getD j 0).toNat := by
  have hL := codec_local hH O
  have hH22 := codec_h22 hH O
  obtain ⟨-, T2⟩ := Codec.codec_trailer hL hH22 hf hF
  obtain ⟨-, -, m9, msg9⟩ := T2 j hj
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlt, -⟩ := Codec.codec_block hL hH22 hf hF
  have hp := recv_pub hH PB.none PB.pub O.lt (show f + 5 + 24 * cv tr tc f Codec.NN + 32 + j < tr.height tc by omega)
    (by rw [O.tab]; exact codec_mem 9 (by decide)) (by rw [Codec.i9_def]) (by rw [Codec.i9_def])
    (by rw [m9]; exact Nat.one_ne_zero)
  rw [I.count, hrecB, msg9] at hp
  have hmem := List.count_pos_iff.1 (Nat.pos_of_ne_zero hp)
  have := (ash_msg hlen hmem (cv_lt _ _) hj (cv_lt _ _) rfl).2
  unfold Codec.shaByte
  rw [if_neg (by omega), ← Nat.add_assoc]
  exact this

/-- **The post sanity hash.** -/
theorem codec_hash (hH : HoldsP AP pub tr) {tc tsha : Nat} (O : CodecValOwn AP tc) (SO : SparOwn AP)
    (SH : ShaOwn AP tsha) (SK : ShaKind AP pub tr tc) (PB : PubbOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (Ps : List InstPub) (fwd : List (Nat × Nat))
    (hrecP : I.recs B_SPAR true = (render Ps fwd).par) (hrecB : I.recs B_SPUBB true = (render Ps fwd).pubb)
    (h256 : Ps.length ≤ 256)
    {f : Nat} (hf : f < tr.height tc) (hF : cv tr tc f Codec.kF = 1)
    (hash32 : (Ps.getD (cv tr tc f Codec.tau) instD).ash.length = 32) :
    (∀ j, j < 64 → Codec.shaByte tr tc f j < 256) ∧
      (List.range 32).map (fun j => UInt8.ofNat (cv tr tc (f + 5 + 24 * cv tr tc f Codec.NN) (Codec.reg j))) =
        NearSpec.sha256 (h0Of tr tc (cv tr tc f Codec.tau) ++ (Ps.getD (cv tr tc f Codec.tau) instD).ash) := by
  have hlen : Ps.length < 2013265921 := by omega
  obtain ⟨hb, hd⟩ := codec_digest hH O SO SH SK I Ps fwd hrecP h256 hf hF
  refine ⟨hb, ?_⟩
  rw [hd]
  show ArenaCore.sha256 _ = ArenaCore.sha256 _
  congr 1
  rw [(pre_block hH O SO I Ps fwd hrecP hlen hf hF).2, Codec.rowBytes_map]
  apply List.ext_getElem (by rw [List.length_append, hash32]; simp)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]
  by_cases hi : i < 32
  · rw [List.getElem_append_left (by simp; exact hi)]
    simp only [List.getElem_map, List.getElem_range]
    unfold Codec.shaByte; rw [if_pos hi]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.length_map, List.length_range]
    have := codec_ash hH O PB I Ps fwd hrecB hlen hf hF (j := i - 32) (by omega)
    rw [show 32 + (i - 32) = i by omega] at this
    rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hash32]; omega),
      Option.getD_some]
    exact UInt8.ofNat_toNat

/-- The memory context of instance τ = `tau f` (`proc_core'''`'s state). -/
theorem memCtx_of {tp tm tcmp ts tch tg tsd tcd : Nat} {Ps : List InstPub}
    (C : InitCtx AP pub tr tp tm tcmp ts tch tg tsd tcd Ps) (PB : PubbOwn AP)
    (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat))
    (hrecP : I.recs B_SPAR true = (render Ps fwd).par) (hrecB : I.recs B_SPUBB true = (render Ps fwd).pubb)
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (Ib : Proc.Inst tr tp f m) :
    cv tr tp f Proc.tau < Ps.length ∧
    MemCtx AP pub tr tp tm tcmp ts tch tg tsd tcd f m (Ps.getD (cv tr tp f Proc.tau) instD)
      (Ps.getD (cv tr tp f Proc.tau) instD).allowed
      (lpState (Ps.getD (cv tr tp f Proc.tau) instD).ids (Ps.getD (cv tr tp f Proc.tau) instD).params
        (Ps.getD (cv tr tp f Proc.tau) instD).allowed (codecA0 tr tcd (cv tr tp f Proc.tau))
        (Ps.getD (cv tr tp f Proc.tau) instD).seed) := by
  have hH := C.hH
  have O := C.O
  have h256 := C.h256
  have hlen : Ps.length < 2013265921 := by omega
  have hτs := proc_htau hH O.tp_lt O.tp_tab PB I Ps fwd hrecB hlen
  have htau : ∀ w, w < tr.height tp → cv tr tp w Proc.act = 1 → cv tr tp w Proc.tau < 256 :=
    fun w hw ha => by have := hτs w hw ha; omega
  have hτ : cv tr tp f Proc.tau < Ps.length :=
    hτs f hf (Proc.act_of (pLocal_of hH O.tp_lt O.tp_tab) hf (Or.inl hk))
  have PO : InstOk (Ps.getD (cv tr tp f Proc.tau) instD) := C.hP _ hτ
  have SP := scanPub_of_idx I Ps fwd hrecP hlen hτ
  have PS := parSmall_of_idx I Ps fwd hrecP h256 (fun τ h => ⟨(C.hP τ h).raw, (C.hP τ h).n64⟩)
  have hV := C.initVals_of I fwd hrecP hτ
  exact ⟨hτ, ⟨hH, O, C.OS, C.OO, PS, htau, hf, hk, hc, Ib, SP, ScanPubOk.of_pv86 PO.params PO.n64 PO.raw,
    lpState_bnd _ PO.n1 _ PO.params _ _ _, lpState_szA _ _ _ _ _, hV⟩⟩

/-- **The post bytes of instance τ are the scheduler core's new state.** -/
theorem sched_post {tp tm tcmp ts tch tg tsd tcd tsha : Nat} {Ps : List InstPub}
    (C : InitCtx AP pub tr tp tm tcmp ts tch tg tsd tcd Ps) (PB : PubbOwn AP) (DO : SdlOwn AP tcd)
    (SH : ShaOwn AP tsha) (SK : ShaKind AP pub tr tcd)
    (I : PubIdx AP pub Fp.ofNat) (fwd : List (Nat × Nat))
    (hrecP : I.recs B_SPAR true = (render Ps fwd).par) (hrecB : I.recs B_SPUBB true = (render Ps fwd).pubb)
    (hrecD : I.recs B_SDL true = (render Ps fwd).dlSend)
    (hsame : ∀ τ, τ < Ps.length → (Ps.getD τ instD).ids = (Ps.getD 0 instD).ids)
    (hash32 : ∀ τ, τ < Ps.length → (Ps.getD τ instD).ash.length = 32)
    {f m : Nat} (hf : f < tr.height tp) (hk : cv tr tp f Proc.kK = 1) (hc : cv tr tp f Proc.kc = 0)
    (Ib : Proc.Inst tr tp f m) :
    let τ := cv tr tp f Proc.tau
    let P := Ps.getD τ instD
    let stF := specSt P.ids.length P.allowed (reqsOf P) tr tp f
      (lpState P.ids P.params P.allowed (codecA0 tr tcd τ) P.seed) m
    (∀ x ∈ svOf tr tcd τ, x < 256) ∧
    (svOf tr tcd τ).map UInt8.ofNat =
      NearSpec.Bandwidth.State.encode
        ⟨canonLinks P.ids (fun l => stF.allowance[l]!), NearSpec.sha256 (h0Of tr tcd τ ++ P.ash)⟩ := by
  intro τ P stF
  have hH := C.hH
  have h256 := C.h256
  have hlen : Ps.length < 2013265921 := by omega
  have hL := codec_local hH C.OC
  have hH22 := codec_h22 hH C.OC
  obtain ⟨hτ, M⟩ := memCtx_of C PB I fwd hrecP hrecB hf hk hc Ib
  obtain ⟨fc, hfc, hF, hτc⟩ := C.codec_exists I fwd hrecP hτ
  have PO := C.hP _ hτ
  have P0 := C.hP 0 (by omega)
  obtain ⟨-, -, hNN, -⟩ := codec_hdr hH C.OC C.SO I Ps fwd hrecP h256 hfc hF (by rw [hτc]; exact PO)
  rw [hτc] at hNN
  have hsv := svOf_block hH C.OC C.SO I Ps fwd hrecP hlen hfc hF
  rw [hτc] at hsv
  -- bytes
  have hbytes : ∀ x ∈ svOf tr tcd τ, x < 256 := by
    rw [hsv]; intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have hi' := List.mem_range.1 hi
    obtain ⟨P1, -⟩ := Codec.codec_post hL hH22 hfc hF
    obtain ⟨m1, -⟩ := P1 i (by omega)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hlt, -⟩ := Codec.codec_block hL hH22 hfc hF
    have hrow : fc + i < tr.height tcd := by omega
    have he := Codec.encG_eval _ (mult1_enc (by rw [m1]; exact Nat.one_ne_zero)) hL hrow
    exact (Codec.bytes hL hrow he).2.1
  refine ⟨hbytes, ?_⟩
  rw [hsv, List.map_map]
  have e1 : ((List.range (37 + 24 * cv tr tcd fc Codec.NN)).map
      (UInt8.ofNat ∘ fun i => cv tr tcd (fc + i) Codec.bpost)) =
      Codec.rowBytes tr tcd Codec.bpost fc (37 + 24 * cv tr tcd fc Codec.NN) := by
    rw [Codec.rowBytes_map]; rfl
  rw [e1, Codec.codec_post_encode hL hH22 hfc hF]
  have hh := (codec_hash hH C.OC C.SO SH SK PB I Ps fwd hrecP hrecB h256 hfc hF
    (by rw [hτc]; exact hash32 _ hτ)).2
  rw [hτc] at hh
  rw [hh]
  congr 2
  -- the links
  unfold Codec.postLinks canonLinks
  rw [hNN, InstPub.n]
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.1 hk
  have hkN : k < cv tr tcd fc Codec.NN := by rw [hNN, InstPub.n]; exact hk'
  have hid := rowLE_idByte (ids := P.ids) (r := fc + 5 + 24 * k) (k := k)
    (by intro x hx; exact PO.ids64 x hx) (fun o ho => by
      rw [hsame _ hτ]
      exact codec_ids hH C.OC C.SO DO I Ps fwd hrecP hrecD h256 P0.n64 _ fc hfc hF rfl k hkN o ho)
  rw [hid.1, hid.2]
  have ha := codec_afin M C.OC hfc hF hτc (by rw [hNN]) hk'
  rw [ha]
  rfl

end

end ZkFormal.NearV3.Sched
