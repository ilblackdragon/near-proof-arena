import ZkFormal.NearV3.Extract.Ups.UpsExt
import ZkFormal.NearV3.Link.Chain3

/-!
# ZkFormal.NearV3.Extract.Ups.UpsChain — the instance chain over the real `upsV3` table (M7e, step 4)

`upsE s = ⟨τ, reg(W0), reg(W3)⟩` is the abstract entry (`Chain3.UpsE`) of a segment: `W0` receives
`MIDROOT [τ] ++ reg(W0)` and `W3` sends `ROOT [(τ + 1) % P] ++ reg(W3)`, and no other row of a segment uses
these buses (`ups_rootMsgs`, `ups_midMsgs`).

* **`ups_chain`**: with the `ROOT` / `MIDROOT` balances over the real traffic, `root_chain` applies to
  `v.map upsE`: every instance `τ ≤ K` has exactly one head and one segment, and the roots chain;
* **`ups_tauDistinct`**: `UpsTauDistinct v` (distinct segments have distinct instances);
* **`ups_tauBound`**: instances are `≤ K`, so `< 2^17` when `K < 2^17`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- The abstract entry of a segment. -/
def upsE (s : UpsSeg) : UpsE := ⟨s.row 0 tau, regN (s.row 0), regN (s.row 3)⟩

theorem regN_len (C : URow) : (regN C).length = 32 := by simp [regN]

theorem upsE_wf {v : List UpsSeg} (hw : UpsWf v) : UpsEWf (v.map upsE) := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · obtain ⟨s, -, rfl⟩ := List.mem_map.1 hu; exact ⟨regN_len _, regN_len _⟩
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hu
    refine ⟨rowLt hw hs _ _, fun x hx => ?_, fun x hx => ?_⟩ <;>
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
variable {v : List UpsSeg} (hw : UpsWf v) {s : UpsSeg} (hs : s ∈ v)
include hw hs

/-- The walk-row flags of `W0 … W3`. -/
theorem walkFlags {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {wsl : List Nat}
    (hL : UpsLayout s L ps fls wsl) (i : Nat) (hi : i < 4) :
    (s.row i sf = 1 ↔ i = 0) ∧ (s.row i wt3 = 1 ↔ i = 3) := by
  have hlt : i < s.rows.length := by have := hL.walk.1; omega
  obtain ⟨-, -, hwk, bsf, bw1, bw2, bw3, -⟩ := kinds (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _)
  have wk1 := hL.wk i hi
  obtain ⟨-, h0, h1, h2, h3⟩ := hL.walk
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> constructor <;>
    constructor <;> intro <;> omega

/-- **`ROOT` of a segment**: one send, by `W3`. -/
theorem ups_rootMsgs : s.msgs B_ROOT true = [[(s.row 0 tau + 1) % P] ++ regN (s.row 3)] := by
  obtain ⟨L, ps, fls, wsl, hL⟩ := ups_layout hw s hs
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
    rcases Nat.lt_or_ge i (4 + L) with hv | hv
    · rw [show i = 4 + (i - 4) by omega, hL.msgsV (i - 4) (by omega) B_ROOT true]
      simp [B_ROOT, B_SPOST, B_BYTES]
    · rw [hL.msgsQ i hv hi B_ROOT true]
      simp [B_ROOT, B_DIGEST, B_BYTES, B_UPB, B_MEMD]

/-- **`MIDROOT` of a segment**: one receive, by `W0`. -/
theorem ups_midMsgs : s.msgs B_MIDROOT false = [[s.row 0 tau] ++ regN (s.row 0)] := by
  obtain ⟨L, ps, fls, wsl, hL⟩ := ups_layout hw s hs
  have h4 := hL.walk.1
  unfold UpsSeg.msgs
  rw [flatMap_ite_congr (g := fun i => if i = 0 then [[s.row 0 tau] ++ regN (s.row 0)] else []) ?_]
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
    rcases Nat.lt_or_ge i (4 + L) with hv | hv
    · rw [show i = 4 + (i - 4) by omega, hL.msgsV (i - 4) (by omega) B_MIDROOT false]
      simp [B_MIDROOT, B_SPOST, B_BYTES]
    · rw [hL.msgsQ i hv hi B_MIDROOT false]
      simp [B_MIDROOT, B_DIGEST, B_BYTES, B_UPB, B_MEMD]

end

theorem ups_rootSends {v : List UpsSeg} (hw : UpsWf v) : (upsTraffic v).sends B_ROOT = upsSends (v.map upsE) B_ROOT := by
  rw [upsSends_root]
  show v.flatMap (·.msgs B_ROOT true) = _
  rw [flatMap_congrR (g := fun s => [[(s.row 0 tau + 1) % P] ++ regN (s.row 3)])
    (fun s hs => ups_rootMsgs hw hs)]
  rw [flatMap_sing, List.map_map]; rfl

theorem ups_midRecvs {v : List UpsSeg} (hw : UpsWf v) : (upsTraffic v).recvs B_MIDROOT = upsRecvs (v.map upsE) B_MIDROOT := by
  rw [upsRecvs_mid]
  show v.flatMap (·.msgs B_MIDROOT false) = _
  rw [flatMap_congrR (g := fun s => [[s.row 0 tau] ++ regN (s.row 0)]) (fun s hs => ups_midMsgs hw hs)]
  rw [flatMap_sing, List.map_map]; rfl

/-- **The instance chain over the real table.** -/
theorem ups_chain {hs : List HeadE} {v : List UpsSeg} {K : Nat} {r0 rK : List Nat}
    (hhw : HeadWf hs) (hw : UpsWf v) (hK : K + 1 < P) (hr0 : ∀ x ∈ r0, x < P) (hrK : ∀ x ∈ rK, x < P)
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

end ZkFormal.NearV3.UpsRows
