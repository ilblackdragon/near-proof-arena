import StateM5a.WsDecode4

/-!
# StateM5a.WsKey — `hkd` from distinct INTAKE keys and a collision-free leaf digest

`WsSeg.ws_final` needs `hkd`: two touched leaves of one segment with the same key are at the same
index.  The argument:

* the leaf digest is `LD bw = digest6 (compress IV384 bw)` of the 16 block words, and the key is
  read off the block (`keyOf`: the low 16 bits of each word's top limb, `kd + 2^16·x` with
  `kd < 2^16`, `x < 256`; `key_of_block`).  A touched leaf's old and new blocks have the same key,
  its own `kd` (`wsl_keys`);
* **keys stay at their positions** (`key_inv`, record level): if the leaf at index `i` after `s`
  segments is `LD b`, then the INTAKE leaf at `i` is `LD b0` with the same key (each segment
  replaces a leaf with one of the same key; `LeafCR`, the leaf compression has no collision on
  well-formed blocks, is a named hypothesis);
* `hkd_of`: so with distinct keys at the real INTAKE positions (`IntakeKeysDistinct`, a named
  premise until the `ORD` / `KCMP` / `KDIG` chain is decoded) and every touched leaf a real entry
  (`i < wsLen`), same key ⇒ same index;
* **`ws_decoded_final3`**: `WsDecode4.ws_decoded_final2` with `hkd` discharged.
-/

namespace StateM5a.WsKey

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.Sha512If
open StateM5a.WsDecode StateM5a.WsDecode2 StateM5a.WsDecode3 StateM5a.WsDecode4 StateM5a.WsBus
open StateM5a.WsRaw StateM5a.Merkle StateM5a.WsSeg StateM5a.WsTree

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Record level: keys stay at their positions -/

section Rec
variable {Kd V α B : Type} {wsl : List (WslRow Kd V α)} {ws0 : List α}
  {G : B → Prop} {LD : B → α} {key : B → Kd}
  (hCR : ∀ b b', G b → G b' → LD b = LD b' → b = b')
  (hrow : ∀ l ∈ wsl, ∃ bo bn, G bo ∧ G bn ∧ l.dgO = LD bo ∧ l.dgN = LD bn ∧ key bo = l.kd ∧ key bn = l.kd)
  (hold : ∀ l ∈ wsl, (wsAt wsl ws0 l.seg)[l.i]? = some l.dgO)
include hCR hrow hold

/-- **Keys stay at their positions.** -/
theorem key_inv : ∀ (s i : Nat) (b : B), G b → (wsAt wsl ws0 s)[i]? = some (LD b) →
    ∃ b0, G b0 ∧ ws0[i]? = some (LD b0) ∧ key b0 = key b
  | 0, i, b, hb, h => ⟨b, hb, h, rfl⟩
  | s + 1, i, b, hb, h => by
    change (segApply wsl s (wsAt wsl ws0 s))[i]? = _ at h
    rw [segApply_get] at h
    unfold touch at h
    cases hf : wsl.find? (fun l => decide (l.seg = s ∧ l.i = i)) with
    | none =>
      rw [hf] at h
      cases hw : (wsAt wsl ws0 s)[i]? with
      | none => rw [hw] at h; simp at h
      | some a =>
        rw [hw] at h
        simp only [Option.map_none, Option.getD_none, Option.map_some, Option.some.injEq] at h
        exact key_inv s i b hb (by rw [hw, h])
    | some l =>
      rw [hf] at h
      have hl := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [decide_eq_true_eq] at hp
      obtain ⟨bo, bn, gbo, gbn, eo, en, ko, kn⟩ := hrow l hl
      cases hw : (wsAt wsl ws0 s)[i]? with
      | none => rw [hw] at h; simp at h
      | some a =>
        rw [hw] at h
        simp only [Option.map_some, Option.getD_some, Option.some.injEq] at h
        have hbn : b = bn := hCR _ _ hb gbn (by rw [← h, en])
        have hold' := hold l hl
        rw [hp.1, hp.2, eo] at hold'
        obtain ⟨b0, g0, e0, k0⟩ := key_inv s i bo gbo hold'
        exact ⟨b0, g0, e0, by rw [k0, ko, hbn, kn]⟩

/-- **Same key ⇒ same index** within a segment, from distinct keys at the real INTAKE positions. -/
theorem hkd_of {m : Nat} (hreal : ∀ l ∈ wsl, l.i < m)
    (hdist0 : ∀ i j b b', i < m → j < m → G b → G b' → ws0[i]? = some (LD b) → ws0[j]? = some (LD b') →
      key b = key b' → i = j) :
    ∀ l ∈ wsl, ∀ l' ∈ wsl, l.seg = l'.seg → l.kd = l'.kd → l.i = l'.i := by
  intro l hl l' hl' hs hk
  obtain ⟨bo, -, gbo, -, eo, -, ko, -⟩ := hrow l hl
  obtain ⟨bo', -, gbo', -, eo', -, ko', -⟩ := hrow l' hl'
  have h1 := hold l hl
  have h2 := hold l' hl'
  rw [eo] at h1
  rw [eo', ← hs] at h2
  obtain ⟨b0, g0, e0, k0⟩ := key_inv hCR hrow hold _ _ _ gbo h1
  obtain ⟨b0', g0', e0', k0'⟩ := key_inv hCR hrow hold _ _ _ gbo' h2
  exact hdist0 _ _ _ _ (hreal l hl) (hreal l' hl') g0 g0' e0 e0' (by rw [k0, k0', ko, ko', hk])

end Rec

/-! ## Keys of leaf blocks -/

/-- The key of a leaf block: the low 16 bits of each word's top limb. -/
def keyOf (bw : List Nat) : List Nat := (List.range 16).map fun t => bw.getD t 0 / 2 ^ 42 % 2 ^ 16

/-- Well-formed leaf blocks: 16 words of 64 bits. -/
def GoodB (bw : List Nat) : Prop := bw.length = 16 ∧ W64 bw

/-- **Named hypothesis**: the one-compression leaf digest has no collision on well-formed blocks. -/
def LeafCR (compress : List Nat → List Nat → List Nat) : Prop :=
  ∀ b b', GoodB b → GoodB b' → digest6 (compress IV384 b) = digest6 (compress IV384 b') → b = b'

/-- **Distinct INTAKE keys** (premise): the real INTAKE leaves (`i < wsLen`) are leaf digests of
blocks with pairwise distinct keys.  (Its derivation — `WSB`'s `ORD` chain of strictly increasing
key ids through `KCMP`, `KDIG` and SHA-256 collision resistance — is not decoded here.) -/
def IntakeKeysDistinct (compress : List Nat → List Nat → List Nat) (ws0 : List Dig) (m : Nat) : Prop :=
  ∀ i j b b', i < m → j < m → GoodB b → GoodB b' → ws0[i]? = some (digest6 (compress IV384 b)) →
    ws0[j]? = some (digest6 (compress IV384 b')) → keyOf b = keyOf b' → i = j

theorem key_of_block {tr : Trace Fp} {t r : Nat} {pub : List Fp} {kd x pv cv : Nat → Expr} {bw : List Nat}
    (hB : (leafBlock kd x pv cv).map (dec3 tr t r pub) = bw.map wlimbs) (hW : W64 bw)
    (hk : ∀ u < 16, ev tr t r pub (kd u) < 2 ^ 16) (hx : ∀ u < 16, ev tr t r pub (x u) < 256) :
    keyOf bw = (List.range 16).map fun u => ev tr t r pub (kd u) := by
  unfold keyOf
  apply List.map_congr_left
  intro u hu
  have hu := List.mem_range.1 hu
  obtain ⟨a, b, he⟩ := leaf_third kd x pv cv u hu
  have h := congrArg (·[u]?) hB
  simp only [List.getElem?_map, he, Option.map_some] at h
  cases hb : bw[u]? with
  | none => simp [hb] at h
  | some w =>
    rw [hb] at h
    simp only [Option.map_some, Option.some.injEq, dec3, wlimbs, List.cons.injEq, and_true] at h
    have e := h.2.2
    rw [ev_hadd, ev_hmul, show K 65536 = Expr.const 65536 from rfl, ev_const] at e
    have k1 := hk u hu
    have x1 := hx u hu
    simp only [Nat.reducePow, Nat.reduceMod] at e k1 ⊢
    rw [Nat.mod_eq_of_lt (show 65536 * ev tr t r pub (x u) < P by omega),
      Nat.mod_eq_of_lt (show ev tr t r pub (kd u) + 65536 * ev tr t r pub (x u) < P by omega)] at e
    rw [List.getD_eq_getElem?_getD, hb, Option.getD_some, ← e]
    omega

theorem leafX_lt {tr : Trace Fp} {t r : Nat} {pub : List Fp} {pp cp wr : Expr} {plx clx : Nat → Expr}
    (h1 : ev tr t r pub pp ≤ 1) (h2 : ev tr t r pub cp ≤ 1) (h3 : ev tr t r pub wr ≤ 1)
    (hp : ∀ k < LEN_CHUNKS, ev tr t r pub (plx k) < 256) (hc : ∀ k < LEN_CHUNKS, ev tr t r pub (clx k) < 256) :
    ∀ u < 16, ev tr t r pub (leafX pp cp wr plx clx u) < 256 := by
  intro u hu
  unfold leafX
  split
  · simp only [ev_hadd, ev_hmul, K, ev_const, Nat.reduceMod]
    rw [Nat.mod_eq_of_lt (show 2 * ev tr t r pub cp < P by omega),
      Nat.mod_eq_of_lt (show 4 * ev tr t r pub wr < P by omega),
      Nat.mod_eq_of_lt (show ev tr t r pub pp + 2 * ev tr t r pub cp < P by omega),
      Nat.mod_eq_of_lt (show ev tr t r pub pp + 2 * ev tr t r pub cp + 4 * ev tr t r pub wr < P by omega)]
    omega
  · split
    · exact hp _ (by unfold LEN_CHUNKS at *; omega)
    · split
      · exact hc _ (by unfold LEN_CHUNKS at *; omega)
      · show ev tr t r pub (Expr.const 0) < 256
        rw [ev_const]; decide

/-! ## Touched leaves keep their key -/

section Keys
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  {compress : List Nat → List Nat → List Nat}
  (hH : Holds (fullAir D extra nb np) pub tr)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG)
  (hcomp : CompressOK compress)
  (hC : Sha512IfContract compress ((busList (fullAir D extra nb np) tr pub B_IF384 true).map decIf))
include hH hx hcomp hC

omit hH hx hcomp hC in
theorem wsl_mem_b (s : String) (hs : s ∈ ["act", "pp", "cp", "wr", "ncp", "nwr"]) :
    bool (Wsl.c s) ∈ Wsl.constraints := by
  unfold Wsl.constraints
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- **A touched leaf's two digests are leaf compressions of blocks with its key.** -/
theorem wsl_keys : ∀ l ∈ wsl tr pub, ∃ bo bn, GoodB bo ∧ GoodB bn ∧
    l.dgO = digest6 (compress IV384 bo) ∧ l.dgN = digest6 (compress IV384 bn) ∧ keyOf bo = l.kd ∧ keyOf bn = l.kd := by
  intro l hl
  obtain ⟨r, hr, hA, rfl⟩ := actRows_mem hl
  obtain ⟨⟨bo, lo, wo, eo, dO⟩, ⟨bn, ln, wn, en, dN⟩, hkd, hch⟩ := wsl_leaf hH hx hcomp hC hr hA
  have hc := holds_constr hH (t := 10) (by decide) full_wsl r hr
  have b : ∀ s, s ∈ ["act", "pp", "cp", "wr", "ncp", "nwr"] → ev tr 10 r pub (Wsl.c s) ≤ 1 :=
    fun s hs => bool_le (hold rfl hc (wsl_mem_b s hs))
  have hlt := fun k hk => Nat.lt_trans (hch k hk).1 (by decide : 64 < 256)
  have ko := key_of_block eo wo hkd (leafX_lt (b "pp" (by simp)) (b "cp" (by simp)) (b "wr" (by simp))
    hlt (fun k hk => Nat.lt_trans (hch k hk).2.1 (by decide)))
  have kn := key_of_block en wn hkd (leafX_lt (b "pp" (by simp)) (b "ncp" (by simp)) (b "nwr" (by simp))
    hlt (fun k hk => Nat.lt_trans (hch k hk).2.2 (by decide)))
  exact ⟨bo, bn, ⟨lo, wo⟩, ⟨ln, wn⟩, dO, dN, ko, kn⟩

end Keys

/-! ## The final working set with `hkd` discharged -/

/-- **The final working set from `Holds`, `hkd` discharged** (premises: the chip contract,
`CompressOK`, tape times, `NodeCR`, `LeafCR`, distinct INTAKE keys). -/
theorem ws_decoded_final3 {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
    {compress : List Nat → List Nat → List Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions,
      i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG ∧ i.bus ≠ B_TREE)
    (hcomp : CompressOK compress)
    (hC : Sha512IfContract compress ((busList (fullAir D extra nb np) tr pub B_IF384 true).map decIf))
    (htape : ∀ m ∈ busList (fullAir D extra nb np) tr pub B_WRITE true, tn (m.getD 1 0) < 2 ^ 24)
    (hD1 : 1 ≤ D) (hD : D ≤ 20) (hCR : NodeCR compress) (hLCR : LeafCR compress)
    (hdist0 : IntakeKeysDistinct compress (wsLeaves tr pub D 0) (WsLen.wsLen pub)) :
    ∃ nw, wsLeaves tr pub D 1 = WsSeg.wsAt (wsl tr pub) (wsLeaves tr pub D 0) nw ∧
    (∀ l ∈ wsl tr pub, l.seg < nw ∧ l.i < 2 ^ D ∧
        (WsSeg.wsAt (wsl tr pub) (wsLeaves tr pub D 0) l.seg)[l.i]? = some l.dgO ∧
        (WsSeg.wsAt (wsl tr pub) (wsLeaves tr pub D 0) (l.seg + 1))[l.i]? = some l.dgN) ∧
    (∀ i, i < 2 ^ D → (∀ l ∈ wsl tr pub, l.i ≠ i) → (wsLeaves tr pub D 1)[i]? = (wsLeaves tr pub D 0)[i]?) ∧
    (∀ l ∈ wsl tr pub, (∀ l' ∈ wsl tr pub, l'.i = l.i → l'.seg ≤ l.seg) →
      (wsLeaves tr pub D 1)[l.i]? = some l.dgN) ∧
    (∀ l ∈ wsl tr pub, ∃ s : List (WsCost.Acc (List Nat)), s.Perm (accOf (wsa tr pub) l.key) ∧
      s.Pairwise (fun a b => b.t < a.t) ∧ l.ncur = WsCost.lastVal l.cur s ∧ l.idl = WsCost.lastT s ∧
      WsCost.Reads l.cur s) ∧
    (∀ a ∈ wsa tr pub, ∃ l ∈ wsl tr pub, l.key = a.key) ∧
    (∀ l ∈ wsl tr pub, l.i < WsLen.wsLen pub) := by
  have hx4 : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG :=
    fun T hT i hi => ⟨(hx T hT i hi).1, (hx T hT i hi).2.1, (hx T hT i hi).2.2.1, (hx T hT i hi).2.2.2.1⟩
  have hxt : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_TREE := fun T hT i hi => (hx T hT i hi).2.2.2.2
  obtain ⟨⟨r0, hs0, hr0⟩, ⟨nw, rF, hq0, hrF⟩⟩ := wsn_roots hH hxt hcomp hC hD1 hD
  obtain ⟨hpt, hok, -, -, hwl, hrch⟩ := ws_decoded hH hx4 hcomp hC htape hD1 hD
  obtain ⟨-, -, hT⟩ := ws_compose hpt hok (hrch r0 rF nw hs0 hq0) hCR (slice_length _ _ _ _) hr0
    (wsl := wsl tr pub)
  have hkd := hkd_of (G := GoodB) (LD := fun b => digest6 (compress IV384 b)) (key := keyOf)
    (fun b b' g g' e => hLCR b b' g g' e) (wsl_keys hH hx4 hcomp hC) (fun l hl => (hT l hl).2.2.1)
    (m := WsLen.wsLen pub) (fun l hl => (hwl l hl).2) hdist0
  exact ws_decoded_final2 hH hx hcomp hC htape hD1 hD hCR hkd
/-! ## Leaf contents across segments (record level) -/

/-- **A segment opens a leaf with the block the previous touching segment closed it with**: with a
collision-free leaf digest, if `l'` is the last row touching index `l.i` before `l`'s segment, the
block of `l`'s old digest is the block of `l'`'s new digest (and with no earlier touch, the INTAKE
leaf's block: `key_inv` / `wsAt_untouched`). -/
theorem open_eq_close {Kd V α B : Type} {wsl : List (WslRow Kd V α)} {ws0 : List α} {n : Nat}
    {G : B → Prop} {LD : B → α}
    (hCR : ∀ b b', G b → G b' → LD b = LD b' → b = b')
    (huniq : ∀ l ∈ wsl, ∀ l' ∈ wsl, l.seg = l'.seg → l.i = l'.i → l = l')
    (hlen : ws0.length = n) (hold : ∀ l ∈ wsl, (wsAt wsl ws0 l.seg)[l.i]? = some l.dgO)
    {l l' : WslRow Kd V α} (hl : l ∈ wsl) (hl' : l' ∈ wsl) (hi : l'.i = l.i) (hs : l'.seg < l.seg)
    (hlast : ∀ l'' ∈ wsl, l''.i = l.i → l''.seg < l.seg → l''.seg ≤ l'.seg) (hin : l.i < n)
    {bo bn : B} (go : G bo) (gn : G bn) (eo : l.dgO = LD bo) (en : l'.dgN = LD bn) : bo = bn := by
  have h1 := hold l hl
  have h2 := wsAt_last huniq hlen hl' (hi ▸ hin) l.seg hs (fun l'' h1 h2 h3 => hlast l'' h1 (h2.trans hi) h3)
  rw [hi, h1, eo, en] at h2
  exact hCR _ _ go gn (Option.some.inj h2)

end StateM5a.WsKey
