import ZkFormal.NearV3.Render.Ups.CompactExtract.UpsVb
import ZkFormal.NearV3.Extract.Ups.UpsChain
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
theorem upsE_wf {v : List UpsSeg} (hw : Wf v) : UpsEWf (v.map upsE) := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨s, -, rfl⟩ := List.mem_map.1 hu; exact ⟨regN_len _, regN_len _⟩
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hu
    refine ⟨rowLt hw hs _ _, fun x hx => ?_, fun x hx => ?_, rowLt hw hs _ _⟩ <;>
    · simp only [upsE, regN, List.mem_map, List.mem_range] at hx
      obtain ⟨i, -, rfl⟩ := hx; exact rowLt hw hs _ _

theorem flatMap_single {β : Type} (m : β) : ∀ (n c : Nat), c < n →
    (List.range n).flatMap (fun i => if i = c then [m] else []) = [m]
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, c, h => by
    rw [List.range_succ, List.flatMap_append]
    by_cases hc : c = n
    · subst hc
      have : (List.range c).flatMap (fun i => if i = c then [m] else []) = [] := by
        rw [List.flatMap_eq_nil_iff]; intro i hi; rw [if_neg (by have := List.mem_range.1 hi; omega)]
      simp [this]
    · rw [flatMap_single m n c (by omega)]; simp [show ¬ n = c from fun h => hc h.symm]

theorem flatMap_sing {α β : Type} (f : α → β) : ∀ l : List α, l.flatMap (fun a => [f a]) = l.map f
  | [] => rfl
  | a :: l => by simp [flatMap_sing f l]

theorem flatMap_ite_congr {β : Type} {f g : Nat → List β} {n : Nat} (h : ∀ i, i < n → f i = g i) :
    (List.range n).flatMap f = (List.range n).flatMap g :=
  flatMap_congrR (fun i hi => h i (List.mem_range.1 hi))

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- The walk-row flags of `W0 … W3`. -/
theorem walkFlags {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
    (hL : UpsLayout s ps fls wsl) (i : Nat) (hi : i < 4) :
    (s.row i sf = 1 ↔ i = 0) ∧ (s.row i wt3 = 1 ↔ i = 3) := by
  have hlt : i < s.rows.length := by have := hL.walk.1; omega
  obtain ⟨-, -, hwk, bsf, bw1, bw2, bw3, -⟩ := currentKinds (okRow hw hs hlt) (rowLt hw hs _)
  have wk1 := hL.wk i hi
  obtain ⟨-, h0, h1, h2, h3⟩ := hL.walk
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> constructor <;>
    constructor <;> intro <;> omega

/-- **`ROOT` of a segment**: one send, by `W3`. -/
theorem ups_rootMsgs : s.msgs B_ROOT true = [[(s.row 0 tau + 1) % P] ++ regN (s.row 3)] := by
  obtain ⟨ps, fls, wsl, hL⟩ := ups_layout hw s hs
  have h4 := hL.walk.1
  unfold UpsSeg.msgs
  rw [flatMap_ite_congr (g := fun i => if i = 3 then [[(s.row 0 tau + 1) % P] ++ regN (s.row 3)] else []) ?_]
  · exact flatMap_single _ _ 3 (by omega)
  intro i hi
  rcases Nat.lt_or_ge i 4 with h | h
  · rw [hL.msgsW i h B_ROOT true]
    have F := walkFlags hw hs hL i h
    by_cases h3 : i = 3
    · subst h3
      simp [B_ROOT, B_MIDROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP, F.2, hL.segc 3 hi tau (by decide)]
    · have : s.row i wt3 ≠ 1 := fun h' => h3 (F.2.1 h')
      simp [B_ROOT, B_MIDROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP, this, h3]
  · rw [if_neg (by omega)]
    rw [hL.msgsQ i h hi B_ROOT true]
    simp [B_ROOT, B_DIGEST, B_BYTES, B_UPB, B_MEMD]

/-- **`MIDROOT` of a segment**: one receive, by `W0`. -/
theorem ups_midMsgs : s.msgs B_MIDROOT false = [[s.row 0 tau, s.row 0 rootRid] ++ regN (s.row 0)] := by
  obtain ⟨ps, fls, wsl, hL⟩ := ups_layout hw s hs
  have h4 := hL.walk.1
  unfold UpsSeg.msgs
  rw [flatMap_ite_congr (g := fun i => if i = 0 then [[s.row 0 tau, s.row 0 rootRid] ++ regN (s.row 0)] else []) ?_]
  · exact flatMap_single _ _ 0 (by omega)
  intro i hi
  rcases Nat.lt_or_ge i 4 with h | h
  · rw [hL.msgsW i h B_MIDROOT false]
    have F := walkFlags hw hs hL i h
    by_cases h0 : i = 0
    · subst h0
      simp [B_ROOT, B_MIDROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP, F.1]
    · have : s.row i sf ≠ 1 := fun h' => h0 (F.1.1 h')
      simp [B_ROOT, B_MIDROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP, this, h0]
  · rw [if_neg (by omega)]
    rw [hL.msgsQ i h hi B_MIDROOT false]
    simp [B_MIDROOT, B_DIGEST, B_BYTES, B_UPB, B_MEMD]

end

theorem ups_rootSends {v : List UpsSeg} (hw : Wf v) : (upsTraffic v).sends B_ROOT = upsSends (v.map upsE) B_ROOT := by
  rw [upsSends_root]
  show v.flatMap (·.msgs B_ROOT true) = _
  rw [flatMap_congrR (g := fun s => [[(s.row 0 tau + 1) % P] ++ regN (s.row 3)])
    (fun s hs => ups_rootMsgs hw hs)]
  rw [flatMap_sing, List.map_map]; rfl

theorem ups_midRecvs {v : List UpsSeg} (hw : Wf v) : (upsTraffic v).recvs B_MIDROOT = upsRecvs (v.map upsE) B_MIDROOT := by
  rw [upsRecvs_mid]
  show v.flatMap (·.msgs B_MIDROOT false) = _
  rw [flatMap_congrR (g := fun s => [[s.row 0 tau, s.row 0 rootRid] ++ regN (s.row 0)]) (fun s hs => ups_midMsgs hw hs)]
  rw [flatMap_sing, List.map_map]; rfl

/-- **The instance chain over the real table.** -/
theorem ups_chain {hs : List HeadE} {v : List UpsSeg} {K : Nat} {r0 rK : List Nat}
    (hhw : HeadWf hs) (hw : Wf v) (hK : K + 1 < P) (hr0 : ∀ x ∈ r0, x < P) (hrK : ∀ x ∈ rK, x < P)
    (hROOT : (([[0] ++ r0] ++ (upsTraffic v).sends B_ROOT).map Msg.toFp).Perm
      ((headRecvs hs B_ROOT ++ [[K + 1] ++ rK]).map Msg.toFp))
    (hMID : ((headSends hs B_MIDROOT).map Msg.toFp).Perm (((upsTraffic v).recvs B_MIDROOT).map Msg.toFp))
    (hlen : hs.length < P) :
    RootChain hs (v.map upsE) K r0 rK := by
  rw [ups_rootSends hw] at hROOT
  rw [ups_midRecvs hw] at hMID
  exact root_chain hhw (upsE_wf hw) hK hr0 hrK hROOT hMID hlen

/-- **Distinct instances.** -/
theorem ups_tauDistinct {hs : List HeadE} {v : List UpsSeg} {K : Nat} {r0 rK : List Nat}
    (hC : RootChain hs (v.map upsE) K r0 rK) : UpsTauDistinct v := by
  intro s hs s' hs' he
  have hc := hC.ups_count (s.row 0 tau)
  rw [List.countP_map] at hc
  have hc1 : v.countP (fun t => t.row 0 tau == s.row 0 tau) ≤ 1 := by
    have : v.countP ((fun u => u.tau == s.row 0 tau) ∘ upsE) = v.countP (fun t => t.row 0 tau == s.row 0 tau) := rfl
    rw [← this, hc]; split <;> omega
  exact Chain3.uniq_of_countP hc1 hs hs' (by simp) (by simp [he])

/-- **Instances are `≤ K`.** -/
theorem ups_tauBound {hs : List HeadE} {v : List UpsSeg} {K : Nat} {r0 rK : List Nat}
    (hC : RootChain hs (v.map upsE) K r0 rK) : ∀ s ∈ v, s.row 0 tau ≤ K :=
  fun s hs => (hC.ups_all (upsE s) (List.mem_map.2 ⟨s, hs, rfl⟩)).1

/-! ## The post root of a segment -/

section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s ∈ v)
  {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
  (hL : UpsLayout s ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP

/-- `W3` looks up the root part's digest at its length. -/
theorem rootLook3 (k : Nat) (hk : k < ps.length) (hroot : k + 1 = ps.length) :
    3 < s.rows.length ∧ s.row 3 gD = 1 ∧ s.row 3 dI = upsIdN (s.row 0 tau) (k + 1) ∧ s.row 3 dL = ps[k].2 := by
  obtain ⟨h4, -, -, -, hw3⟩ := hL.walk
  have hlt : 3 < s.rows.length := by omega
  have ok3 := okRow hw hs hlt
  have hq : s.row 3 qb = 0 := by
    obtain ⟨ha, hact, -⟩ := currentKinds ok3 (rowLt hw hs _)
    have := hL.wk 3 (by omega)
    omega
  obtain ⟨hlt0, hq0, hpf⟩ := pFirst hw hs hL k hk
  have hr := (hP.root k hk).2 hroot
  obtain ⟨-, hjn, hql⟩ := rootPart (okRow hw hs hlt0) (rowLt hw hs _) (nextLt hw hs _) hq0 hr
  have hj : s.row ps[k].1 j = k + 1 := (hL.part k hk).1
  have sc := hL.segc
  have hnQ : s.row 3 nQ = k + 1 := by
    rw [sc 3 hlt nQ (by decide), ← sc _ hlt0 nQ (by decide), ← hjn, hj]
  have hrl : s.row 3 rlen = ps[k].2 := by
    rw [sc 3 hlt rlen (by decide), ← sc _ hlt0 rlen (by decide), ← hql, qlenPart hw hs hL hP k hk]
  refine ⟨hlt, w3gD ok3 (rowLt hw hs _) (nextLt hw hs _) hw3 hq, ?_, ?_⟩
  · have := dIj_nat (rowLt hw hs _ _) (w3dI ok3 (rowLt hw hs _) hw3)
    rw [this, hnQ, sc 3 hlt tau (by decide)]
  · rw [natv (rowLt hw hs _ _) (rowLt hw hs _ _) (w3dL ok3 (rowLt hw hs _) hw3), hrl]

end

theorem ofNat_toNat_map (l : NearSpec.Bytes) : (l.map UInt8.toNat).map UInt8.ofNat = l := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left; intro x _; simp

/-- **The `ROOT` digest of a segment** (`reg(W3)`, i.e. `(upsE s).post`) is the hash of the encoding of its
root part's node `upsQ (|ps| − 1)`. -/
theorem ups_rootDig {vs : List NodeS3} {hds : List HeadE} {es : List ValE} {others : List Msg}
    {shaS shaR : Nat → List Fp → Nat} {pv : Nat → NearSpec.Bytes} {v : List UpsSeg} {sv : Nat → NearSpec.Bytes}
    {othersU : List Msg} {ws : List WalkR} {taus : List Nat}
    (E : UpsEnv vs hds es others shaS shaR pv v sv othersU ws taus)
    {s : UpsSeg} (hs : s ∈ v) {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
    (hL : UpsLayout s ps fls wsl) {ci ti di si : Nat} {kd sdx : Nat → Nat} (hP : UpsPlan s ps ci ti di si kd sdx)
    (hvb : s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256)
    (hshape : ∀ k, k < ps.length → SrcShape ci si ti (sdx k) (kd k) (srcOf (Rpost vs es) (Vpost vs es pv) s ps k)) :
    (upsE s).post = (NearSpec.sha256 (nodeEnc (upsQ ci si ti (s.row 0 tX) (sv (s.row 0 tau)) kd sdx
      (srcOf (Rpost vs es) (Vpost vs es pv) s ps) (ps.length - 1)))).map UInt8.toNat := by
  have hne := hL.nonempty
  have hk : ps.length - 1 < ps.length := by omega
  obtain ⟨hlt, hg, hI, hLn⟩ := rootLook3 E.ups hs hL hP (ps.length - 1) hk (by omega)
  have HS := sha_seg E.ups (Link3.ShaHyp.sha E.sha) taus sv othersU E.relays E.bytesU E.othU E.digU E.tauD
    (ups_idBound E.node E.head E.par E.ups E.upb E.tauB) s hs ps fls wsl hL
  have h1 := (HS 3 hlt hg (ps.length - 1) hk hI hLn).2
  have h2 := (ups_partsAll E hs hL hP hvb hshape (ps.length - 1) hk).1
  show regN (s.row 3) = _
  rw [h1, h2, ofNat_toNat_map]

end ZkFormal.NearV3.Render.UpsRelay.Extract
