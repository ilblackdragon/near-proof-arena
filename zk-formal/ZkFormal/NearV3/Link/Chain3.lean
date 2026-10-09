import ZkFormal.NearV3.Extract.HeadProof
import ZkFormal.Near.Link.Bus

/-!
# ZkFormal.NearV3.Link.Chain3 — the ROOT / MIDROOT instance chain (M7a)

Participants on `B_ROOT` and `B_MIDROOT` (message `[τ] ++ d`):
* heads (`HeadE`): receive `ROOT [h.tau] ++ h.pre`, send `MIDROOT [h.tau] ++ ([h.rid] ++ h.post)`;
* `upsV3`, abstract (`UpsE`): receive `MIDROOT [u.tau] ++ ([u.rid] ++ u.mid)`, send
  `ROOT [(u.tau + 1) % P] ++ u.post`.  The table computes `τ + 1` in `Fp`, whose image is
  `Fp.ofNat (τ + 1) = Fp.ofNat ((τ + 1) % P)`; we use the canonical representative `% P` so that
  every message is canonical (`Canon`) and `toFp_inj` applies;
* the public bus: sends `ROOT [0] ++ r0`, receives `ROOT [K + 1] ++ rK` (`K + 1 < P`).

`root_chain`: from the two balances (`Perm` of the `Fp` images) and `hs.length < P`, every
instance `τ ≤ K` has exactly one head and exactly one ups entry, none has `τ > K`, and the chain
closes: `(hd 0).pre = r0`, `(hd (τ+1)).pre = (up τ).post`, `(up τ).mid = (hd τ).post`,
`(up K).post = rK`, and `(up τ).rid = (hd τ).rid` (the root record the upsert starts from).

Proof: `H τ` / `U τ` count heads / ups with tau `τ`. MIDROOT gives `U = H`; ROOT gives
`H τ + [τ = K+1] = [τ = 0] + U (τ - 1 mod P)`, so `H` is `H 0` on `[0, K]` and `H 0 - 1` on
`(K, P)`, with `H 0 ≥ 1`; `H 0 ≥ 2` would put a head on each of the `P` residues.
-/

namespace ZkFormal.NearV3

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link

/-- An abstract `upsV3` entry (instance `tau`: mid-root in, post-root out). -/
structure UpsE where
  tau : Nat
  /-- the root record of the instance (received on `MIDROOT`) -/
  rid : Nat
  mid : List Nat
  post : List Nat
  deriving Repr, Inhabited

structure UpsEWf (us : List UpsE) : Prop where
  len : ∀ u ∈ us, u.mid.length = 32 ∧ u.post.length = 32
  canon : ∀ u ∈ us, u.tau < P ∧ (∀ x ∈ u.mid, x < P) ∧ (∀ x ∈ u.post, x < P) ∧ u.rid < P

def upsSends (us : List UpsE) (b : Nat) : List Msg :=
  if b = B_ROOT then us.map fun u => [(u.tau + 1) % P] ++ u.post else []

def upsRecvs (us : List UpsE) (b : Nat) : List Msg :=
  if b = B_MIDROOT then us.map fun u => [u.tau] ++ ([u.rid] ++ u.mid) else []

/-- ROOT balance: public send and ups sends against head receives and the public receive. -/
def RootBal (hs : List HeadE) (us : List UpsE) (K : Nat) (r0 rK : List Nat) : Prop :=
  (([[0] ++ r0] ++ upsSends us B_ROOT).map Msg.toFp).Perm
    ((headRecvs hs B_ROOT ++ [[K + 1] ++ rK]).map Msg.toFp)

/-- MIDROOT balance: head sends against ups receives. -/
def MidBal (hs : List HeadE) (us : List UpsE) : Prop :=
  ((headSends hs B_MIDROOT).map Msg.toFp).Perm ((upsRecvs us B_MIDROOT).map Msg.toFp)

theorem headSends_mid (hs : List HeadE) :
    headSends hs B_MIDROOT = hs.map fun h => [h.tau] ++ ([h.rid] ++ h.post) := by
  simp [headSends]

theorem headRecvs_root (hs : List HeadE) : headRecvs hs B_ROOT = hs.map fun h => [h.tau] ++ h.pre := by
  simp [headRecvs, show B_ROOT ≠ B_DIGEST by decide]

theorem upsSends_root (us : List UpsE) : upsSends us B_ROOT = us.map fun u => [(u.tau + 1) % P] ++ u.post := by
  simp [upsSends]

theorem upsRecvs_mid (us : List UpsE) : upsRecvs us B_MIDROOT = us.map fun u => [u.tau] ++ ([u.rid] ++ u.mid) := by
  simp [upsRecvs]

/-- The head / ups entry of an instance (first in the list; unique under `root_chain`). -/
def headAt (hs : List HeadE) (τ : Nat) : HeadE := (hs.find? fun h => h.tau == τ).getD default
def upsAt (us : List UpsE) (τ : Nat) : UpsE := (us.find? fun u => u.tau == τ).getD default

/-- **The closed instance chain** `τ = 0..K`. -/
structure RootChain (hs : List HeadE) (us : List UpsE) (K : Nat) (r0 rK : List Nat) : Prop where
  head_count : ∀ τ, hs.countP (fun h => h.tau == τ) = if τ ≤ K then 1 else 0
  ups_count : ∀ τ, us.countP (fun u => u.tau == τ) = if τ ≤ K then 1 else 0
  head_mem : ∀ τ ≤ K, headAt hs τ ∈ hs ∧ (headAt hs τ).tau = τ
  ups_mem : ∀ τ ≤ K, upsAt us τ ∈ us ∧ (upsAt us τ).tau = τ
  head_all : ∀ h ∈ hs, h.tau ≤ K ∧ h = headAt hs h.tau
  ups_all : ∀ u ∈ us, u.tau ≤ K ∧ u = upsAt us u.tau
  pre0 : (headAt hs 0).pre = r0
  link : ∀ τ < K, (headAt hs (τ + 1)).pre = (upsAt us τ).post
  mid : ∀ τ ≤ K, (upsAt us τ).mid = (headAt hs τ).post
  rid : ∀ τ ≤ K, (upsAt us τ).rid = (headAt hs τ).rid
  postK : (upsAt us K).post = rK

namespace Chain3

theorem uniq_of_countP {α : Type} {p : α → Bool} : ∀ {l : List α}, l.countP p ≤ 1 →
    ∀ {a b : α}, a ∈ l → b ∈ l → p a → p b → a = b
  | [], _, _, _, ha, _, _, _ => by simp at ha
  | x :: l, hc, a, b, ha, hb, hpa, hpb => by
    rw [List.countP_cons] at hc
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · have := List.countP_pos_iff.2 ⟨b, hb', hpb⟩; rw [if_pos hpa] at hc; omega
    · have := List.countP_pos_iff.2 ⟨a, ha', hpa⟩; rw [if_pos hpb] at hc; omega
    · exact uniq_of_countP (by split at hc <;> omega) ha' hb' hpa hpb

theorem card_le {α : Type} (f : α → Nat) (l : List α) (n : Nat)
    (h : ∀ τ < n, ∃ x ∈ l, f x = τ) : n ≤ l.length := by
  have hs : List.range n ⊆ l.map f := fun τ hτ => by
    obtain ⟨x, hx, hfx⟩ := h τ (List.mem_range.1 hτ); exact List.mem_map.2 ⟨x, hx, hfx⟩
  have := List.nodup_range.length_le_of_subset hs
  simpa using this

theorem find_spec {α : Type} {l : List α} {f : α → Nat} {τ : Nat} {x : α} (hx : x ∈ l) (hfx : f x = τ) :
    ∃ y, l.find? (fun a => f a == τ) = some y ∧ y ∈ l ∧ f y = τ := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (List.find?_isSome (p := fun a => f a == τ) |>.2 ⟨x, hx, by
    show (f x == τ) = true; rw [hfx]; exact beq_self_eq_true τ⟩)
  exact ⟨y, hy, List.mem_of_find?_eq_some hy, by simpa using List.find?_some hy⟩

/-- The cyclic recurrence: `H` is `1` on `[0, K]` and `0` on `(K, P)`. -/
theorem recur (H : Nat → Nat) (K n : Nat) (hK : K + 1 < n)
    (h0 : H 0 = H (n - 1) + 1)
    (hs : ∀ τ, 1 ≤ τ → τ < n → H (τ - 1) = H τ + if τ = K + 1 then 1 else 0)
    (hcard : (∀ τ < n, 1 ≤ H τ) → False) :
    ∀ τ < n, H τ = if τ ≤ K then 1 else 0 := by
  have hlo : ∀ τ ≤ K, H τ = H 0 := by
    intro τ; induction τ with
    | zero => intro; rfl
    | succ t ih => intro ht; have := hs (t + 1) (by omega) (by omega); simp at this; rw [← ih (by omega)]
                   split at this <;> omega
  have hhi : ∀ j, K + 1 + j < n → H (K + 1 + j) + 1 = H 0 := by
    intro j; induction j with
    | zero =>
      intro hj; have := hs (K + 1) (by omega) hj
      rw [if_pos rfl, Nat.add_sub_cancel] at this; show H (K + 1) + 1 = H 0; rw [← hlo K (Nat.le_refl _)]; omega
    | succ t ih =>
      intro hj; have := hs (K + 1 + t + 1) (by omega) hj
      rw [Nat.add_sub_cancel, if_neg (by omega)] at this
      rw [show K + 1 + (t + 1) = K + 1 + t + 1 by omega, ← ih (by omega)]; omega
  have hn1 := hhi (n - 1 - (K + 1)) (by omega)
  rw [show K + 1 + (n - 1 - (K + 1)) = n - 1 by omega] at hn1
  have hH0 : H 0 = 1 := by
    rcases Nat.lt_or_ge (H 0) 2 with h | h
    · omega
    · exfalso; apply hcard; intro τ hτ
      rcases Nat.lt_or_ge K τ with h' | h'
      · have := hhi (τ - (K + 1)) (by omega); rw [show K + 1 + (τ - (K + 1)) = τ by omega] at this; omega
      · rw [hlo τ h']; omega
  intro τ hτ
  split
  · rw [hlo τ (by omega)]; exact hH0
  · have := hhi (τ - (K + 1)) (by omega); rw [show K + 1 + (τ - (K + 1)) = τ by omega] at this; omega

theorem toFp_head (a : Nat) (d : List Nat) : (Msg.toFp ([a] ++ d)).head? = some (Fp.ofNat a) := by
  simp [Msg.toFp]

/-- Matching two canonical `[τ] ++ d` messages by their `Fp` images. -/
theorem msg_eq {a b : Nat} {d e : List Nat} (ha : a < P) (hb : b < P) (hd : ∀ x ∈ d, x < P)
    (he : ∀ x ∈ e, x < P) (h : Msg.toFp ([a] ++ d) = Msg.toFp ([b] ++ e)) : a = b ∧ d = e := by
  have := toFp_inj (a := [a] ++ d) (b := [b] ++ e)
    (fun x hx => by simp at hx; exact hx.elim (fun e => e ▸ ha) (fun hx => hd x hx))
    (fun x hx => by simp at hx; exact hx.elim (fun e => e ▸ hb) (fun hx => he x hx)) h
  simpa using this

theorem canonApp {a : Nat} {l : List Nat} (ha : a < P) (hl : ∀ x ∈ l, x < P) : ∀ x ∈ [a] ++ l, x < P := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact ha
  · exact hl x hx

theorem ofNat_iff {a b : Nat} (ha : a < P) (hb : b < P) : Fp.ofNat a = Fp.ofNat b ↔ a = b :=
  ⟨Link.ofNat_inj ha hb, fun h => h ▸ rfl⟩

/-- "the message has tau `τ`" on `Fp` images. -/
def tauIs (τ : Nat) (m : List Fp) : Bool := decide (m.head? = some (Fp.ofNat τ))

theorem countP_tau {α : Type} (l : List α) (t : α → Nat) (d : α → List Nat) (hl : ∀ x ∈ l, t x < P)
    {τ : Nat} (hτ : τ < P) :
    ((l.map fun x => [t x] ++ d x).map Msg.toFp).countP (tauIs τ) = l.countP (fun x => t x == τ) := by
  rw [List.map_map, List.countP_map]
  refine List.countP_congr (fun x hx => ?_)
  simp only [Function.comp, tauIs, toFp_head, Option.some.injEq, decide_eq_true_eq, beq_iff_eq]
  exact ofNat_iff (hl x hx) hτ

theorem countP_one (a : Nat) (d : List Nat) {τ : Nat} (ha : a < P) (hτ : τ < P) :
    ([[a] ++ d].map Msg.toFp).countP (tauIs τ) = if τ = a then 1 else 0 := by
  simp only [List.map_cons, List.map_nil, List.countP_cons, List.countP_nil, tauIs, toFp_head,
    Option.some.injEq, decide_eq_true_eq, ofNat_iff ha hτ, Nat.zero_add]
  by_cases h : τ = a
  · subst h; simp
  · simp [h, Ne.symm h]

end Chain3

open Chain3 in
/-- **M7a — the ROOT / MIDROOT instance chain.** -/
theorem root_chain {hs : List HeadE} {us : List UpsE} {K : Nat} {r0 rK : List Nat}
    (hhw : HeadWf hs) (huw : UpsEWf us) (hK : K + 1 < P)
    (hr0 : ∀ x ∈ r0, x < P) (hrK : ∀ x ∈ rK, x < P)
    (hROOT : RootBal hs us K r0 rK) (hMID : MidBal hs us) (hlen : hs.length < P) :
    RootChain hs us K r0 rK := by
  have hP1 : 1 < P := by unfold P; decide
  -- counts
  let H : Nat → Nat := fun τ => hs.countP (fun h => h.tau == τ)
  let U : Nat → Nat := fun τ => us.countP (fun u => u.tau == τ)
  have hmid : ∀ τ < P, U τ = H τ := by
    intro τ hτ
    have := hMID.countP_eq (tauIs τ)
    rw [headSends_mid, upsRecvs_mid, countP_tau _ _ _ (fun h hh => (hhw.canon h hh).1) hτ,
      countP_tau _ _ _ (fun u hu => (huw.canon u hu).1) hτ] at this
    exact this.symm
  have hroot : ∀ τ < P, (if τ = 0 then 1 else 0) + us.countP (fun u => (u.tau + 1) % P == τ) =
      H τ + if τ = K + 1 then 1 else 0 := by
    intro τ hτ
    have := hROOT.countP_eq (tauIs τ)
    simp only [List.map_append, List.countP_append] at this
    rw [headRecvs_root, upsSends_root, countP_tau _ _ _ (fun h hh => (hhw.canon h hh).1) hτ,
      countP_tau _ _ _ (fun u hu => Nat.mod_lt _ (by omega)) hτ,
      countP_one _ _ (by omega) hτ, countP_one _ _ hK hτ] at this
    exact this
  have hsh : ∀ τ, 1 ≤ τ → τ < P → us.countP (fun u => (u.tau + 1) % P == τ) = U (τ - 1) := by
    intro τ h1 hτ
    refine List.countP_congr (fun u hu => ?_)
    have ht := (huw.canon u hu).1
    simp only [beq_iff_eq]
    rcases Nat.lt_or_ge (u.tau + 1) P with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [show u.tau + 1 = P by omega, Nat.mod_self]; omega
  have hsh0 : us.countP (fun u => (u.tau + 1) % P == 0) = U (P - 1) := by
    refine List.countP_congr (fun u hu => ?_)
    have ht := (huw.canon u hu).1
    simp only [beq_iff_eq]
    rcases Nat.lt_or_ge (u.tau + 1) P with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · rw [show u.tau + 1 = P by omega, Nat.mod_self]; omega
  have hHc : ∀ τ < P, H τ = if τ ≤ K then 1 else 0 := by
    refine recur H K P hK ?_ ?_ ?_
    · have := hroot 0 (by omega)
      rw [hsh0, hmid _ (by omega)] at this; simp at this; omega
    · intro τ h1 hτ
      have := hroot τ hτ
      rw [hsh τ h1 hτ, hmid _ (by omega), if_neg (by omega)] at this; omega
    · intro hall
      have := card_le HeadE.tau hs P (fun τ hτ => by
        obtain ⟨h, hh, hp⟩ := List.countP_pos_iff.1 (Nat.lt_of_lt_of_le Nat.zero_lt_one (hall τ hτ))
        exact ⟨h, hh, by simpa using hp⟩)
      omega
  have hHall : ∀ τ, H τ = if τ ≤ K then 1 else 0 := by
    intro τ
    rcases Nat.lt_or_ge τ P with h | h
    · exact hHc τ h
    · rw [if_neg (by omega)]
      exact List.countP_eq_zero.2 (fun x hx => by
        have := (hhw.canon x hx).1; simp only [beq_iff_eq]; omega)
  have hUall : ∀ τ, U τ = if τ ≤ K then 1 else 0 := by
    intro τ
    rcases Nat.lt_or_ge τ P with h | h
    · rw [hmid τ h]; exact hHc τ h
    · rw [if_neg (by omega)]
      exact List.countP_eq_zero.2 (fun x hx => by
        have := (huw.canon x hx).1; simp only [beq_iff_eq]; omega)
  -- existence / uniqueness
  have hex : ∀ τ ≤ K, ∃ h ∈ hs, h.tau = τ := fun τ hτ => by
    have : 0 < H τ := by rw [hHall τ, if_pos hτ]; omega
    obtain ⟨h, hh, hp⟩ := List.countP_pos_iff.1 this; exact ⟨h, hh, by simpa using hp⟩
  have uex : ∀ τ ≤ K, ∃ u ∈ us, u.tau = τ := fun τ hτ => by
    have : 0 < U τ := by rw [hUall τ, if_pos hτ]; omega
    obtain ⟨u, hu, hp⟩ := List.countP_pos_iff.1 this; exact ⟨u, hu, by simpa using hp⟩
  have hle : ∀ h ∈ hs, h.tau ≤ K := fun h hh => by
    have : 0 < H h.tau := List.countP_pos_iff.2 ⟨h, hh, by simp⟩
    rw [hHall] at this; split at this <;> omega
  have ule : ∀ u ∈ us, u.tau ≤ K := fun u hu => by
    have : 0 < U u.tau := List.countP_pos_iff.2 ⟨u, hu, by simp⟩
    rw [hUall] at this; split at this <;> omega
  have huniq : ∀ {a b}, a ∈ hs → b ∈ hs → a.tau = b.tau → a = b := fun {a b} ha hb he =>
    uniq_of_countP (p := fun h => h.tau == a.tau) (by
      have := hHall a.tau; show H a.tau ≤ 1; rw [this]; split <;> omega) ha hb (by simp) (by simp [he])
  have uuniq : ∀ {a b}, a ∈ us → b ∈ us → a.tau = b.tau → a = b := fun {a b} ha hb he =>
    uniq_of_countP (p := fun u => u.tau == a.tau) (by
      have := hUall a.tau; show U a.tau ≤ 1; rw [this]; split <;> omega) ha hb (by simp) (by simp [he])
  have hAt : ∀ τ ≤ K, headAt hs τ ∈ hs ∧ (headAt hs τ).tau = τ := fun τ hτ => by
    obtain ⟨h, hh, ht⟩ := hex τ hτ
    obtain ⟨y, hy, hy1, hy2⟩ := find_spec (f := HeadE.tau) hh ht
    simp only [headAt]; rw [hy]; exact ⟨hy1, hy2⟩
  have uAt : ∀ τ ≤ K, upsAt us τ ∈ us ∧ (upsAt us τ).tau = τ := fun τ hτ => by
    obtain ⟨u, hu, ht⟩ := uex τ hτ
    obtain ⟨y, hy, hy1, hy2⟩ := find_spec (f := UpsE.tau) hu ht
    simp only [upsAt]; rw [hy]; exact ⟨hy1, hy2⟩
  have hAll : ∀ h ∈ hs, h.tau ≤ K ∧ h = headAt hs h.tau := fun h hh =>
    ⟨hle h hh, huniq hh (hAt _ (hle h hh)).1 (hAt _ (hle h hh)).2.symm⟩
  have uAll : ∀ u ∈ us, u.tau ≤ K ∧ u = upsAt us u.tau := fun u hu =>
    ⟨ule u hu, uuniq hu (uAt _ (ule u hu)).1 (uAt _ (ule u hu)).2.symm⟩
  -- messages
  have rootMem : ∀ m ∈ [[0] ++ r0] ++ upsSends us B_ROOT,
      ∃ m' ∈ headRecvs hs B_ROOT ++ [[K + 1] ++ rK], Msg.toFp m = Msg.toFp m' := fun m hm => by
    have := hROOT.subset (List.mem_map.2 ⟨m, hm, rfl⟩)
    obtain ⟨m', hm', he⟩ := List.mem_map.1 this; exact ⟨m', hm', he.symm⟩
  have hcanH : ∀ h ∈ hs, h.tau < P ∧ (∀ x ∈ h.pre, x < P) ∧ ∀ x ∈ h.post, x < P := fun h hh =>
    ⟨(hhw.canon h hh).1, (hhw.canon h hh).2.2.2.2.2.1, (hhw.canon h hh).2.2.2.2.2.2⟩
  -- ROOT-side match: a canonical `[a] ++ d` sent on ROOT is `[a] ++ h.pre` or the public receive.
  have rootMatch : ∀ {a d}, [a] ++ d ∈ [[0] ++ r0] ++ upsSends us B_ROOT → a < P → (∀ x ∈ d, x < P) →
      (∃ h ∈ hs, h.tau = a ∧ h.pre = d) ∨ (a = K + 1 ∧ d = rK) := fun {a d} hm ha hd => by
    obtain ⟨m', hm', he⟩ := rootMem _ hm
    rw [headRecvs_root] at hm'; simp only [List.mem_append, List.mem_map, List.mem_singleton] at hm'
    rcases hm' with ⟨h, hh, rfl⟩ | rfl
    · obtain ⟨e1, e2⟩ := msg_eq ha (hcanH h hh).1 hd (hcanH h hh).2.1 he
      exact .inl ⟨h, hh, e1.symm, e2.symm⟩
    · obtain ⟨e1, e2⟩ := msg_eq ha hK hd hrK he; exact .inr ⟨e1, e2⟩
  have midEq : ∀ τ ≤ K, (upsAt us τ).mid = (headAt hs τ).post ∧ (upsAt us τ).rid = (headAt hs τ).rid := by
    intro τ hτ
    obtain ⟨hh, ht⟩ := hAt τ hτ
    have := hMID.subset (List.mem_map.2 ⟨[τ] ++ ([(headAt hs τ).rid] ++ (headAt hs τ).post), by
      rw [headSends_mid]; simp only [List.mem_map]; exact ⟨_, hh, by rw [ht]⟩, rfl⟩)
    obtain ⟨m', hm', he⟩ := List.mem_map.1 this
    rw [upsRecvs_mid] at hm'; simp only [List.mem_map] at hm'
    obtain ⟨u, hu, rfl⟩ := hm'
    have cu := huw.canon u hu
    have ch := hhw.canon _ hh
    obtain ⟨e1, e2⟩ := msg_eq cu.1 (by omega) (canonApp cu.2.2.2 cu.2.1) (canonApp ch.2.1 ch.2.2.2.2.2.2) he
    simp only [List.singleton_append, List.cons.injEq] at e2
    have hu' : upsAt us τ = u := by rw [← e1]; exact ((uAll u hu).2).symm
    rw [hu']; exact ⟨e2.2, e2.1⟩
  refine ⟨hHall, hUall, hAt, uAt, hAll, uAll, ?_, ?_, fun τ hτ => (midEq τ hτ).1, fun τ hτ => (midEq τ hτ).2, ?_⟩
  · rcases rootMatch (a := 0) (d := r0) (by simp) (by omega) hr0 with ⟨h, hh, ht, hp⟩ | ⟨h1, -⟩
    · rw [← hp, (hAll h hh).2, ht]
    · omega
  · intro τ hτ
    obtain ⟨hu, ht⟩ := uAt τ (by omega)
    have hm : [τ + 1] ++ (upsAt us τ).post ∈ [[0] ++ r0] ++ upsSends us B_ROOT := by
      rw [upsSends_root]; simp only [List.mem_append, List.mem_map]
      exact .inr ⟨_, hu, by rw [ht, Nat.mod_eq_of_lt (by omega)]⟩
    rcases rootMatch hm (by omega) (huw.canon _ hu).2.2.1 with ⟨h, hh, ht', hp⟩ | ⟨h1, -⟩
    · rw [← hp, (hAll h hh).2, ht']
    · omega
  · obtain ⟨hu, ht⟩ := uAt K (Nat.le_refl _)
    have hm : [K + 1] ++ (upsAt us K).post ∈ [[0] ++ r0] ++ upsSends us B_ROOT := by
      rw [upsSends_root]; simp only [List.mem_append, List.mem_map]
      exact .inr ⟨_, hu, by rw [ht, Nat.mod_eq_of_lt hK]⟩
    rcases rootMatch hm hK (huw.canon _ hu).2.2.1 with ⟨h, hh, ht', -⟩ | ⟨-, hp⟩
    · have := hle h hh; omega
    · exact hp

end ZkFormal.NearV3
