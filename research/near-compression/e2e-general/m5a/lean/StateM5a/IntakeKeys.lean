import StateM5a.KeyOrder

/-!
# StateM5a.IntakeKeys — the real INTAKE leaves have strictly increasing, distinct keys

* **`wsb_so`**: two consecutive real phase-0 `WSB` rows `r, r + 1` (`r + 1 < wsLen`) have `so = 1`,
  so `r` receives `ORD(kid_r, kid_{r+1})`: `bytesLt (keyBytes kid_r) (keyBytes kid_{r+1})`
  (`KeyOrder.ord_recv`).
* **`wsb_sorted`**: for real phase-0 rows `a < b`, `bytesLt (keyBytes kid_a) (keyBytes kid_b)`
  (transitivity of `bytesLt`).
* **`intakeKeysDistinct`**: `WsKey.IntakeKeysDistinct compress (wsLeaves tr pub D 0) wsLen`.  A
  leaf digest `digest6 (compress IV b)` at real position `i` is row `i`'s (`WsLeafF.wslLD`,
  `wsb_leaf`), so with `LeafCR` `b` is row `i`'s block and `WsKey.keyOf b` its `kd` limbs
  (`key_of_block`) `= pairs (sha256 (keyBytes kid_i))` (`KeyDigest.wsb_kd`); equal `keyOf`s give
  equal SHA-256 digests, with `Sha256CR` equal key bytes, and strict order forces `i = j`.
  (`WsKey.keyOf` of a well-formed leaf block reads the 16 key-digest limbs `kd`, the leaf's key
  as the working set stores it: `pairs (sha256 key)`.)
-/

namespace StateM5a.IntakeKeys

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.KeyDecode
open StateM5a.Tape StateM5a.KcChain StateM5a.KeyDigest StateM5a.KeyOrder NearSpec NearSpecV3.D2

set_option maxRecDepth 100000

/-! ## `bytesLt` -/

theorem bytesLt_irrefl : ∀ a : Bytes, bytesLt a a = false
  | [] => rfl
  | x :: xs => by simp [bytesLt, bytesLt_irrefl xs]

theorem bytesLt_trans : ∀ a b c : Bytes, bytesLt a b = true → bytesLt b c = true → bytesLt a c = true
  | [], [], _, h, _ => by simp [bytesLt] at h
  | [], _ :: _, [], _, h => by simp [bytesLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [bytesLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [bytesLt] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [bytesLt] at h1 h2 ⊢
    by_cases a1 : x.toNat < y.toNat <;> by_cases a2 : y.toNat < x.toNat <;> simp [a1, a2] at h1 <;>
      by_cases b1 : y.toNat < z.toNat <;> by_cases b2 : z.toNat < y.toNat <;> simp [b1, b2] at h2 <;>
      first
      | (have : x.toNat < z.toNat := by omega
         simp [this])
      | (have e1 : x.toNat = y.toNat := by omega
         have e2 : y.toNat = z.toNat := by omega
         have n1 : ¬ x.toNat < z.toNat := by omega
         have n2 : ¬ z.toNat < x.toNat := by omega
         simp [n1, n2]
         exact bytesLt_trans xs ys zs h1 h2)

theorem sha256_length (m : Bytes) : (sha256 m).length = 32 := by
  have hb : ∀ w n, (ArenaCore.Bytes.beN w n).length = w := by
    intro w; induction w with
    | zero => intro; rfl
    | succ w ih => intro n; simp [ArenaCore.Bytes.beN, ih]
  have hd : ∀ h : List Nat, (ArenaCore.SHA256.digestBytes h).length = 4 * h.length := by
    intro h; induction h with
    | nil => rfl
    | cons x xs ih => simp [ArenaCore.SHA256.digestBytes, hb] at ih ⊢; omega
  show (ArenaCore.sha256 m).length = 32
  unfold ArenaCore.sha256
  rw [hd, ArenaCore.SHA256.blocks_length _ _ _ rfl]

/-! ## The phase-0 order -/

theorem m_so (D : Nat) : Wsb.c "so" - (1 - Wsb.c "ph") * (1 - Wsb.c "e") * Wsb.c "real" * Wsb.nx "real" ∈
    Wsb.constraints D := by unfold Wsb.constraints; simp
theorem m_e (D : Nat) : Wsb.c "e" * (Wsb.c "i" - K (2 ^ D - 1)) ∈ Wsb.constraints D := by
  unfold Wsb.constraints; simp
theorem wsb_ord_mem : rcv B_ORD (Wsb.c "so") [Wsb.c "kid", Wsb.nx "kid"] ∈ Wsb.interactions := memD_mem (by decide)

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}

/-- The key bytes of `WSB` row `r`. -/
def wkey (tr : Trace Fp) (pub : List Fp) (r : Nat) : Bytes := keyBytes tr (ev tr 5 r pub (Wsb.c "kid"))

theorem phase0 (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30) {r : Nat}
    (hr : r < WsLen.wsLen pub) :
    r < tr.height 5 ∧ ev tr 5 r pub (Wsb.c "ph") = 0 ∧ ev tr 5 r pub (Wsb.c "i") = r ∧
      ev tr 5 r pub (Wsb.c "real") = 1 := by
  have hc := wsb_hc hH
  have hlog := wsb_log hH
  have hW := WsLen.wsb_wsLen_le hc hlog hD
  have h0 : 0 < tr.height 5 := Nat.two_pow_pos _
  have hl := (WsLen.wsb_last (D := D) hc).2
  have hrl : r < tr.height 5 := by
    rcases FieldWsb.wsb_index hc hlog hD (tr.height 5 - 1) (by omega) with ⟨a, _⟩ | ⟨_, b⟩
    · omega
    · omega
  rcases FieldWsb.wsb_index hc hlog hD r hrl with ⟨a, b⟩ | ⟨_, b⟩
  · refine ⟨hrl, a, b, ?_⟩
    exact (WsLen.wsb_real_iff hc hlog hD hrl).2.2 (by omega)
  · omega

/-- **Consecutive real phase-0 rows are in key order.** -/
theorem wsb_so (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hO : ∀ T ∈ extra, sendsOn T.interactions B_ORD = false) {r : Nat}
    (hr : r + 1 < WsLen.wsLen pub) : bytesLt (wkey tr pub r) (wkey tr pub (r + 1)) = true := by
  have hc := wsb_hc hH
  have hlog := wsb_log hH
  have hW := WsLen.wsb_wsLen_le hc hlog hD
  obtain ⟨h0, p0, i0, re0⟩ := phase0 hH hD (by omega : r < WsLen.wsLen pub)
  obtain ⟨h1, -, -, re1⟩ := phase0 hH hD hr
  have nx : ∀ s, ev tr 5 r pub (Wsb.nx s) = ev tr 5 (r + 1) pub (Wsb.c s) := fun s => FieldWsb.wsb_nx s r h1
  have he : ev tr 5 r pub (Wsb.c "e") = 0 := by
    rcases FieldRows2.ev_bool (hold rfl (hc r h0) (FieldWsb.m_bool "e" (by simp))) with h | h
    · exact h
    · have := eq_of_sub (FieldWsb.wsb_gate h (hold rfl (hc r h0) (m_e D)))
      rw [i0, show K (2 ^ D - 1) = Expr.const (2 ^ D - 1) from rfl, ev_const] at this
      have := Nat.one_le_two_pow (n := D)
      have : 2 ^ D ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hD
      rw [Nat.mod_eq_of_lt (by omega)] at *
      omega
  have hso : ev tr 5 r pub (Wsb.c "so") = 1 := by
    rw [eq_of_sub (hold rfl (hc r h0) (m_so D)), ev_hmul, ev_hmul, ev_hmul, FieldRows2.ev_one_sub0 p0,
      FieldRows2.ev_one_sub0 he, re0, nx, re1]
  have hm := msg_mem_busList (A := fullAir D extra nb np) (pub := pub) (t := 5) (by rw [fullAir_len]; omega)
    (by rw [fullAir_get (by simp [m5aAir]) _]; exact wsb_ord_mem) h0 rfl (ev_one_eval hso)
  obtain ⟨a, b, he', hab⟩ := ord_recv hH hN hL hO hm
  simp only [rcv, Interaction.msgVal, List.map_cons, List.map_nil, List.cons.injEq] at he'
  obtain ⟨rfl, rfl, -⟩ := he'
  unfold wkey
  rw [← nx]
  exact hab

/-- **The real phase-0 rows hold strictly increasing keys.** -/
theorem wsb_sorted (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hO : ∀ T ∈ extra, sendsOn T.interactions B_ORD = false) :
    ∀ d a, a + d + 1 < WsLen.wsLen pub → bytesLt (wkey tr pub a) (wkey tr pub (a + d + 1)) = true := by
  intro d
  induction d with
  | zero => intro a h; exact wsb_so hH hD hN hL hO h
  | succ d ih =>
    intro a h
    exact bytesLt_trans _ _ _ (ih a (by omega)) (wsb_so hH hD hN hL hO (by omega))

/-- **Distinct real phase-0 rows have distinct keys** (`Sha256CR`: and distinct `kd` limbs). -/
theorem wsb_kd_inj (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30) (hCR : Walk.Sha256CR)
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hO : ∀ T ∈ extra, sendsOn T.interactions B_ORD = false)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxG : ∀ T ∈ extra, sendsOn T.interactions B_KDIG = false) {i j : Nat}
    (hi : i < WsLen.wsLen pub) (hj : j < WsLen.wsLen pub)
    (he : (List.range 16).map (fun u => ev tr 5 i pub (Wsb.c "kd" u)) =
      (List.range 16).map (fun u => ev tr 5 j pub (Wsb.c "kd" u))) : i = j := by
  obtain ⟨hi5, -, -, ri⟩ := phase0 hH hD hi
  obtain ⟨hj5, -, -, rj⟩ := phase0 hH hD hj
  rw [wsb_kd hH hxB hxD hxK hxG hi5 ri, wsb_kd hH hxB hxD hxK hxG hj5 rj] at he
  have hs := congrArg limbBytes he
  rw [limbBytes_pairs _ (by rw [sha256_length]), limbBytes_pairs _ (by rw [sha256_length])] at hs
  have hk : wkey tr pub i = wkey tr pub j := hCR _ _ hs
  rcases Nat.lt_trichotomy i j with h | h | h
  · have := wsb_sorted hH hD hN hL hO (j - i - 1) i (by omega)
    rw [show i + (j - i - 1) + 1 = j by omega, ← hk, bytesLt_irrefl] at this
    exact absurd this (by decide)
  · exact h
  · have := wsb_sorted hH hD hN hL hO (i - j - 1) j (by omega)
    rw [show j + (i - j - 1) + 1 = i by omega, hk, bytesLt_irrefl] at this
    exact absurd this (by decide)

end

open StateM5a.Sha512If StateM5a.WsDecode StateM5a.WsDecode2 StateM5a.WsDecode3 StateM5a.WsDecode4
open StateM5a.WsKey StateM5a.WsLeafF in
/-- **`WsKey.IntakeKeysDistinct` from `Holds`** (premises: `Sha256CR`, `LeafCR`, the SHA-512 chip
contract — those of `WsLeafF.wsb_leaf` — and extra tables silent on the key buses). -/
theorem intakeKeysDistinct {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
    {compress : List Nat → List Nat → List Nat}
    (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30) (hCR : Walk.Sha256CR) (hLCR : LeafCR compress)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG)
    (hcomp : CompressOK compress)
    (hC : Sha512IfContract compress ((busList (fullAir D extra nb np) tr pub B_IF384 true).map decIf))
    (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
    (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
    (hO : ∀ T ∈ extra, sendsOn T.interactions B_ORD = false)
    (hxB : ∀ T ∈ extra, sendsOn T.interactions B_SHA_BYTES = false)
    (hxD : ∀ T ∈ extra, sendsOn T.interactions B_SHA_DIGEST = false)
    (hxK : ∀ T ∈ extra, sendsOn T.interactions B_KC = false)
    (hxG : ∀ T ∈ extra, sendsOn T.interactions B_KDIG = false) :
    IntakeKeysDistinct compress (wsLeaves tr pub D 0) (WsLen.wsLen pub) := by
  have hW := wsbKdRange hH hxB hxD hxK hxG
  have hWl := WsLen.wsb_wsLen_le (wsb_hc hH) (wsb_log hH) hD
  have leafk : ∀ i, i < WsLen.wsLen pub → ∀ b, GoodB b →
      (wsLeaves tr pub D 0)[i]? = some (digest6 (compress IV384 b)) →
      WsKey.keyOf b = (List.range 16).map (fun u => ev tr 5 i pub (Wsb.c "kd" u)) := by
    intro i hi b hb hd
    obtain ⟨h5, -, -, re⟩ := phase0 hH hD hi
    rw [wslLD tr pub D 0 i (by omega)] at hd
    simp only [Nat.zero_mul, Nat.zero_add, Option.some.injEq] at hd
    obtain ⟨hok, bw, hgb, eB, eo⟩ := wsb_leaf hH hx hcomp hC hW h5 (ev_one_eval re)
    have hbw : b = bw := hLCR b bw hb hgb (by rw [← hd, eo])
    subst hbw
    exact key_of_block eB hgb.2 hok.1 (leafX_lt hok.2.2.1 hok.2.2.2.1 hok.2.2.2.2.1
      (fun k hk => (hok.2.1 k hk).1) (fun k hk => (hok.2.1 k hk).2))
  intro i j b b' hi hj hb hb' hdi hdj hk
  exact wsb_kd_inj hH hD hCR hN hL hO hxB hxD hxK hxG hi hj
    (by rw [← leafk i hi b hb hdi, ← leafk j hj b' hb' hdj, hk])

end StateM5a.IntakeKeys
