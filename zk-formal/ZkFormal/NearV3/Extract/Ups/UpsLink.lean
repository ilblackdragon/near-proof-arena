import ZkFormal.NearV3.Extract.Ups.UpsUpper

/-!
# ZkFormal.NearV3.Extract.Ups.UpsLink — `upsV3` against the spec (M7e, steps 2–3 assembled)

For every instance `τ ≤ K`, with `T'_τ = fullTree R V' (headAt τ).rid` the lockstep post trie of the head of `τ`
(`R = Rpost`, `V' = Vpost`, the records with their post values) and `v_τ = sv τ` the scheduler's new value:

* **`ups_s0f`** / **`upsV3_s0f`** (step 2): `upsV3` sends one `S0F (τ, present, vid)`, and `(present, vid)` is
  `T'_τ.find [0,15]`: `present = 1` and the value is `valOf V' (vpos vid)`, or `present = vid = 0` and the key is
  absent (`walk3_find_of` on the `upsV3` walk with the post values, `walkHyp_any`);
* **`upsV3_link`** (step 3): the `ROOT` digest `upsV3` sends for `τ` is, byte for byte, the hash of
  `upsert T'_τ [0,15] v_τ` (which is defined: `ups_upsert`), including every `memory_usage`; with `RootChain`,
  that digest is the next head's pre root (`τ < K`) or `rK` (`τ = K`);
* **`upsV3_linkB`**: the same from the views, balances, `ShaHyp` and the interface structures alone (`RootChain`,
  `UpsTauDistinct`, `τ < 2^17` and the walk hypotheses are derived).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-! ## Upserted nodes are nodes -/

theorem wrapExt_isNode (p : List Nat) (b : NearSpec.PTrie) (h : isNode b = true) :
    isNode (NearSpec.wrapExt p b) = true := by
  cases p with
  | nil => exact h
  | cons x r => rfl

theorem splitLeaf_isNode (k : List Nat) (sl : NearSpec.Slot) (key : List Nat) (v : NearSpec.Bytes) :
    isNode (NearSpec.splitLeaf k sl key v) = true := by
  unfold NearSpec.splitLeaf
  dsimp only
  split <;> first | exact wrapExt_isNode _ _ rfl | rfl

theorem splitExt_isNode (k : List Nat) (c : NearSpec.PTrie) (m : Nat) (key : List Nat) (v : NearSpec.Bytes) :
    isNode (NearSpec.splitExt k c m key v) = true := by
  unfold NearSpec.splitExt
  dsimp only
  split
  · rfl
  · split <;> exact wrapExt_isNode _ _ rfl

/-- **`PTrie.upsert` returns a node.** -/
theorem upsert_isNode (t : NearSpec.PTrie) (key : List Nat) (v : NearSpec.Bytes) (Q : NearSpec.PTrie)
    (h : t.upsert key v = some Q) : isNode Q = true := by
  cases t with
  | hash hh => simp [NearSpec.PTrie.upsert] at h
  | leaf k sl m =>
    simp only [NearSpec.PTrie.upsert] at h
    split at h
    · cases h; rfl
    · cases h; exact splitLeaf_isNode _ _ _ _
  | ext k c m =>
    simp only [NearSpec.PTrie.upsert] at h
    split at h
    · split at h
      · cases h; rfl
      · cases h
    · cases h; exact splitExt_isNode _ _ _ _ _
  | branch bv cs m =>
    cases key with
    | nil => simp only [NearSpec.PTrie.upsert] at h; cases h; rfl
    | cons n rest =>
      simp only [NearSpec.PTrie.upsert, Option.map_eq_some_iff] at h
      obtain ⟨r, -, rfl⟩ := h
      rfl

attribute [local irreducible] UpsSeg.row UpsSeg.next

/-! ## `S0F` -/

section
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- **`S0F` of a segment**: one send, by `W0`. -/
theorem ups_s0fMsgs : s.msgs B_S0F true = [[s.row 0 tau, s.row 0 pres, s.row 0 vid]] := by
  obtain ⟨L, ps, fls, wsl, hL⟩ := ups_layout hw s hs
  have h4 := hL.walk.1
  unfold UpsSeg.msgs
  rw [flatMap_ite_congr (g := fun i => if i = 0 then [[s.row 0 tau, s.row 0 pres, s.row 0 vid]] else []) ?_]
  · exact flatMap_single _ _ 0 (by omega)
  intro i hi
  rcases Nat.lt_or_ge i 4 with h | h
  · rw [hL.msgsW i h B_S0F true]
    have F := walkFlags hw hs hL i h
    by_cases h0 : i = 0
    · subst h0
      simp [B_ROOT, B_MIDROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP, F.1]
    · have : s.row i sf ≠ 1 := fun h' => h0 (F.1.1 h')
      simp [B_ROOT, B_MIDROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP, this, h0]
  · rw [if_neg (by omega)]
    rcases Nat.lt_or_ge i (4 + L) with hv | hv
    · rw [show i = 4 + (i - 4) by omega, hL.msgsV (i - 4) (by omega) B_S0F true]
      simp [B_S0F, B_SPOST, B_BYTES]
    · rw [hL.msgsQ i hv hi B_S0F true]
      simp [B_S0F, B_DIGEST, B_BYTES, B_UPB, B_MEMD]

end

theorem upsWalk_key3 (s : UpsSeg) : (upsWalk s).key3 = UpsSpec.key := by
  rw [Walk3.key3_eq]; simp [upsWalk, stepOf, wsym, List.range_succ, UpsSpec.key]

section
variable {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
  {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} {sv : Nat → NearSpec.Bytes}
  {othersU : List Msg} {ws : List WalkR}
  (E : UpsEnv vs hds es others shaS shaR pv v sv othersU ws)
  {K : Nat} {r0 rK : List Nat} (hC : RootChain hds (v.map upsE) K r0 rK)
include E hC

/-- **Step 2: `S0F (present, vid)` is the lookup of `[0,15]` in the lockstep post trie of the head of `τ`.** -/
theorem ups_s0f {s : UpsSeg} (hs : s ∈ v) :
    (s.row 0 pres = 1 ∧ (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds (s.row 0 tau)).rid).find UpsSpec.key =
        some (some (valOf (Vpost vs es pv) (Link3.vpos (Link3.vid0 es) (s.row 0 vid))))) ∨
    (s.row 0 pres = 0 ∧ s.row 0 vid = 0 ∧
      (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds (s.row 0 tau)).rid).find UpsSpec.key = some none) := by
  have hw := E.ups
  obtain ⟨L, ps, fls, wsl, hL⟩ := ups_layout hw s hs
  obtain ⟨ci, ti, di, si, kd, sdx, hP⟩ := ups_plan hw hs hL
  have G' := Link3.walkHyp_any E.node E.head E.val E.walk.walk E.par E.vpar E.walk.balE E.walk.balB
    (Link3.rec_bytes E.node E.head E.val E.par E.sha) E.walk.sym (Vpost vs es pv)
  obtain ⟨h, hh, ht, hV, hA⟩ := Walk3.walk3_find_of G' (upsWalk_mem (ws := ws) hs)
  have hhd : h = headAt hds (s.row 0 tau) := by
    have := (hC.head_all h hh).2; rw [ht] at this; exact this
  subst hhd
  rw [upsWalk_key3] at hV hA
  have hlast : (upsWalk s).last = stepOf (s.row 3) 3 := by
    unfold WalkR.last; rw [upsWalk_len]; exact upsWalk_step s (by omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hpr, hvd⟩ := ups_walkTerm hw hs hL hP
  have h4 := hL.walk.1
  have sp : s.row 3 pres = s.row 0 pres := hL.segc 3 (by omega) pres (by decide)
  have sv' : s.row 3 vid = s.row 0 vid := hL.segc 3 (by omega) vid (by decide)
  have hm := (wRowF hw hs hL 3 (by omega)).modes.1
  unfold WalkR.fk WalkR.k at hV
  unfold WalkR.fk at hA
  rw [hlast] at hV hA
  rcases (show s.row 3 mS = 0 ∨ s.row 3 mS = 1 by omega) with h0 | h1
  · have hmd : (stepOf (s.row 3) 3).mode ≠ 0 := by
      intro hc
      simp only [stepOf, h0] at hc
      by_cases a : s.row 3 mK = 1 <;> by_cases b : s.row 3 mB = 1 <;> simp [a, b] at hc
    rw [if_neg hmd] at hA
    refine Or.inr ⟨by rw [← sp, hpr, h0], by rw [← sv', hvd, h0, Nat.zero_mul], hA rfl⟩
  · have hmd : (stepOf (s.row 3) 3).mode = 0 := by simp [stepOf, h1]
    rw [if_pos hmd, if_pos hmd] at hV
    have := hV rfl
    simp only [stepOf, List.getD_cons_succ, List.getD_cons_zero] at this
    refine Or.inl ⟨by rw [← sp, hpr, h1], ?_⟩
    rw [← sv', hvd, h1, Nat.one_mul]; exact this

/-- **The post root of a segment** is the hash of the upsert at the head's root record. -/
theorem ups_post {s : UpsSeg} (hs : s ∈ v) :
    ∃ Q, (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds (s.row 0 tau)).rid).upsert UpsSpec.key
        (sv (s.row 0 tau)) = some Q ∧ (upsE s).post = Q.hashOf.map UInt8.toNat := by
  have hw := E.ups
  obtain ⟨L, ps, fls, wsl, hL⟩ := ups_layout hw s hs
  obtain ⟨ci, ti, di, si, kd, sdx, hP⟩ := ups_plan hw hs hL
  have hU := ups_upsert E hs hL hP hC
  refine ⟨_, hU, ?_⟩
  rw [ups_rootDig E hs hL hP (ups_vbytesE E hs hL hP) (ups_shape E hs hL hP),
    hashOf_eq_enc _ (upsert_isNode _ _ _ _ hU)]

/-- **Step 3: the `upsV3` link.**  For every instance `τ ≤ K`, the upsert of `[0,15]` with the scheduler's value
`sv τ` into the lockstep post trie of the head of `τ` is defined, and the `ROOT` digest `upsV3` sends for `τ` is its
hash, byte for byte (so every `memory_usage` on the new path is exact); it is the next head's pre root, or `rK`. -/
theorem upsV3_link (τ : Nat) (hτ : τ ≤ K) :
    ∃ Q, (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds τ).rid).upsert UpsSpec.key (sv τ) = some Q ∧
      (upsAt (v.map upsE) τ).post = Q.hashOf.map UInt8.toNat ∧ Link3.toB (upsAt (v.map upsE) τ).post = Q.hashOf ∧
      (τ < K → (headAt hds (τ + 1)).pre = Q.hashOf.map UInt8.toNat) ∧ (τ = K → rK = Q.hashOf.map UInt8.toNat) := by
  obtain ⟨hm, ht⟩ := hC.ups_mem τ hτ
  obtain ⟨s, hs, he⟩ := List.mem_map.1 hm
  have hτs : s.row 0 tau = τ := by rw [← ht, ← he]; rfl
  obtain ⟨Q, hU, hpost⟩ := ups_post E hC hs
  rw [hτs] at hU
  have hpost' : (upsAt (v.map upsE) τ).post = Q.hashOf.map UInt8.toNat := by rw [← he]; exact hpost
  refine ⟨Q, hU, hpost', by rw [hpost']; exact Link3.toB_toNat _, fun hlt => by rw [hC.link τ hlt, hpost'],
    fun hK => by subst hK; rw [← hC.postK, hpost']⟩

/-- **Step 2 per instance**: the `S0F` message `upsV3` sends for `τ ≤ K` is `T'_τ.find [0,15]`. -/
theorem upsV3_s0f (τ : Nat) (hτ : τ ≤ K) :
    ∃ s ∈ v, s.row 0 tau = τ ∧ s.msgs B_S0F true = [[τ, s.row 0 pres, s.row 0 vid]] ∧
      ((s.row 0 pres = 1 ∧ (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds τ).rid).find UpsSpec.key =
          some (some (valOf (Vpost vs es pv) (Link3.vpos (Link3.vid0 es) (s.row 0 vid))))) ∨
       (s.row 0 pres = 0 ∧ s.row 0 vid = 0 ∧
          (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds τ).rid).find UpsSpec.key = some none)) := by
  obtain ⟨hm, ht⟩ := hC.ups_mem τ hτ
  obtain ⟨s, hs, he⟩ := List.mem_map.1 hm
  have hτs : s.row 0 tau = τ := by rw [← ht, ← he]; rfl
  have H := ups_s0f E hC hs
  rw [hτs] at H
  exact ⟨s, hs, hτs, by rw [ups_s0fMsgs E.ups hs, hτs], H⟩

end

/-- **The `upsV3` link from the views, balances, `ShaHyp` and the interfaces alone** (`RootChain` from the
`ROOT`/`MIDROOT` balances, distinct instances and `τ < 2^17` from it with `K < 2^17`, the walk hypotheses of all
walks from the `EDGE`/`BMAP` balances and `KEYNIB`): for every `τ ≤ K`, `upsV3_link` and `upsV3_s0f`. -/
theorem upsV3_linkB {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
    {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} {sv : Nat → NearSpec.Bytes}
    {othersU : List Msg} {ws : List WalkR} {prov : List Msg} {K : Nat} {r0 rK : List Nat}
    -- views
    (hN : NodeWf3 vs) (hhw : HeadWf hds) (hvw : ValWf es) (hw : UpsWf v) (hW : WalkWf3 ws)
    (hWr : (ws.flatMap (·.steps)).length ≤ 2 ^ 21)
    -- balances
    (hb : Link3.ParentBal vs hds) (hvb : Link3.VParentBal vs es) (hupb : UpbBal vs v)
    (hE : WalkBal vs hds ws v B_EDGE) (hB : WalkBal vs hds ws v B_BMAP) (hKn : Link3.KeynibOk ws prov)
    (hbytesU : ∀ m, shaR B_BYTES m = cnt ((upsTraffic v).sends B_BYTES ++ othersU) m)
    (hothU : ∀ m ∈ othersU, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_VUPS)
    (hdigU : ∀ m ∈ (upsTraffic v).recvs B_DIGEST, 0 < shaS B_DIGEST m.toFp)
    (hmemd : (((upsTraffic v).sends B_MEMD).map Msg.toFp).Perm (((upsTraffic v).recvs B_MEMD).map Msg.toFp))
    (hK : K + 1 < P) (hK17 : K < 2 ^ 17) (hr0 : ∀ x ∈ r0, x < P) (hrK : ∀ x ∈ rK, x < P)
    (hROOT : (([[0] ++ r0] ++ (upsTraffic v).sends B_ROOT).map Msg.toFp).Perm
      ((headRecvs hds B_ROOT ++ [[K + 1] ++ rK]).map Msg.toFp))
    (hMID : ((headSends hds B_MIDROOT).map Msg.toFp).Perm (((upsTraffic v).recvs B_MIDROOT).map Msg.toFp))
    (hlen : hds.length < P)
    -- SHA
    (hsha : Link3.ShaHyp vs hds es others shaS shaR)
    -- interfaces
    (hvpost : Link3.VPostOk others pv)
    (hvpostLen : ∀ p (hp : p < vs.length) i l pre po, vs[p].v.value = some (i, l, pre, po, true) → (pv i).length ≤ l)
    (hsched : SchedVal v sv) :
    ∀ τ, τ ≤ K →
      (∃ Q, (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds τ).rid).upsert UpsSpec.key (sv τ) = some Q ∧
        (upsAt (v.map upsE) τ).post = Q.hashOf.map UInt8.toNat ∧ Link3.toB (upsAt (v.map upsE) τ).post = Q.hashOf ∧
        (τ < K → (headAt hds (τ + 1)).pre = Q.hashOf.map UInt8.toNat) ∧ (τ = K → rK = Q.hashOf.map UInt8.toNat)) ∧
      (∃ s ∈ v, s.row 0 tau = τ ∧ s.msgs B_S0F true = [[τ, s.row 0 pres, s.row 0 vid]] ∧
        ((s.row 0 pres = 1 ∧ (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds τ).rid).find UpsSpec.key =
            some (some (valOf (Vpost vs es pv) (Link3.vpos (Link3.vid0 es) (s.row 0 vid))))) ∨
         (s.row 0 pres = 0 ∧ s.row 0 vid = 0 ∧
            (fullTree (Rpost vs es) (Vpost vs es pv) (headAt hds τ).rid).find UpsSpec.key = some none))) := by
  have hC := ups_chain hhw hw hK hr0 hrK hROOT hMID hlen
  have E : UpsEnv vs hds es others shaS shaR pv v sv othersU ws :=
    { node := hN, head := hhw, val := hvw, par := hb, vpar := hvb, sha := hsha, vpost := hvpost,
      vpostLen := hvpostLen, ups := hw, upb := hupb, sched := hsched, bytesU := hbytesU, othU := hothU,
      digU := hdigU, memd := hmemd, tauD := ups_tauDistinct hC,
      tauB := fun s hs => by have := ups_tauBound hC s hs; omega,
      walk := ups_walkHyp hN hhw hvw hW hWr hw hb hvb hE hB hKn (Link3.rec_bytes hN hhw hvw hb hsha) _ }
  exact fun τ hτ => ⟨upsV3_link E hC τ hτ, upsV3_s0f E hC τ hτ⟩

end ZkFormal.NearV3.UpsRows
