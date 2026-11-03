import StateM5a.WsKey

/-!
# StateM5a.WsLeafF — equal leaf blocks give equal fields (field level)

A leaf block `Ws.leafBlock kd x pv cv` read as limb triples (`dec3`) determines, on two rows (of
any tables), the 16-bit limbs `kd`, `pv`, `cv` and the side slots `x` (`block_fields`: word by word,
the third limb `kd + 2^16·x` is split by `WsCost.leafLimb_inj` with `kd < 2^16`, `x < 2^8`).
From the slots: `pp`, `cp`, `wr` (slot 0 = `pp + 2cp + 4wr`, booleans) and the length chunks, hence
the lengths (`len_eq`, the `lenChunks` constraint).

* `wsb_leaf`: a real `WSB` row's digest is the leaf compression of its block (`comp_iv`), and its
  slots are bytes; `WsbKdRange` (premise) — its `kd` limbs are 16-bit (they are `KDIG`'s, i.e. the
  `KEY` table's SHA-256 digest bytes paired; not decoded here).
-/

namespace StateM5a.WsLeafF

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.Sha512If
open StateM5a.WsDecode StateM5a.WsDecode2 StateM5a.WsDecode3 StateM5a.WsDecode4 StateM5a.WsKey StateM5a.WsBus
open StateM5a.WsRaw StateM5a.Merkle StateM5a.WsSeg StateM5a.WsTree

local notation "P" => 2013265921

set_option maxRecDepth 100000

/-! ## Words of a leaf block -/

theorem leaf_lo (kd x pv cv : Nat → Expr) (w : Nat) (hw : w < 8) :
    (leafBlock kd x pv cv)[w]? = some (pv (2 * w), pv (2 * w + 1), kd w + K 65536 * x w) := by
  unfold leafBlock
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_map, List.getElem?_range hw]; rfl

theorem leaf_hi (kd x pv cv : Nat → Expr) (v : Nat) (hv : v < 8) :
    (leafBlock kd x pv cv)[8 + v]? = some (cv (2 * v), cv (2 * v + 1), kd (8 + v) + K 65536 * x (8 + v)) := by
  unfold leafBlock
  rw [List.getElem?_append_right (by simp), List.getElem?_map]
  simp only [List.length_map, List.length_range, Nat.add_sub_cancel_left]
  rw [List.getElem?_range hv]; rfl

section
variable {tr : Trace Fp} {pub : List Fp} {t1 r1 t2 r2 : Nat}

/-- Two equal triples. -/
theorem triple_eq {a b c a' b' c' : Expr}
    (h : dec3 tr t1 r1 pub (a, b, c) = dec3 tr t2 r2 pub (a', b', c')) :
    ev tr t1 r1 pub a = ev tr t2 r2 pub a' ∧ ev tr t1 r1 pub b = ev tr t2 r2 pub b' ∧
      ev tr t1 r1 pub c = ev tr t2 r2 pub c' := by
  simp only [dec3, List.cons.injEq, and_true] at h
  exact h

theorem hi_split {k x k' x' : Expr} (hk : ev tr t1 r1 pub k < 2 ^ 16) (hk' : ev tr t2 r2 pub k' < 2 ^ 16)
    (hx : ev tr t1 r1 pub x < 256) (hx' : ev tr t2 r2 pub x' < 256)
    (h : ev tr t1 r1 pub (k + K 65536 * x) = ev tr t2 r2 pub (k' + K 65536 * x')) :
    ev tr t1 r1 pub k = ev tr t2 r2 pub k' ∧ ev tr t1 r1 pub x = ev tr t2 r2 pub x' := by
  rw [ev_hadd, ev_hmul, ev_hadd, ev_hmul, show K 65536 = Expr.const 65536 from rfl, ev_const, ev_const] at h
  simp only [Nat.reduceMod] at h
  rw [Nat.mod_eq_of_lt (show 65536 * ev tr t1 r1 pub x < P by omega),
    Nat.mod_eq_of_lt (show 65536 * ev tr t2 r2 pub x' < P by omega)] at h
  exact WsCost.leafLimb_inj hk hk' (by omega) (by omega) h

/-- **Equal leaf blocks have equal fields.** -/
theorem block_fields {kd x pv cv kd' x' pv' cv' : Nat → Expr}
    (h : (leafBlock kd x pv cv).map (dec3 tr t1 r1 pub) = (leafBlock kd' x' pv' cv').map (dec3 tr t2 r2 pub))
    (hk : ∀ u < 16, ev tr t1 r1 pub (kd u) < 2 ^ 16) (hk' : ∀ u < 16, ev tr t2 r2 pub (kd' u) < 2 ^ 16)
    (hx : ∀ u < 16, ev tr t1 r1 pub (x u) < 256) (hx' : ∀ u < 16, ev tr t2 r2 pub (x' u) < 256) :
    ∀ u < 16, ev tr t1 r1 pub (kd u) = ev tr t2 r2 pub (kd' u) ∧ ev tr t1 r1 pub (x u) = ev tr t2 r2 pub (x' u) ∧
      ev tr t1 r1 pub (pv u) = ev tr t2 r2 pub (pv' u) ∧ ev tr t1 r1 pub (cv u) = ev tr t2 r2 pub (cv' u) := by
  have lo : ∀ w < 8, ev tr t1 r1 pub (pv (2 * w)) = ev tr t2 r2 pub (pv' (2 * w)) ∧
      ev tr t1 r1 pub (pv (2 * w + 1)) = ev tr t2 r2 pub (pv' (2 * w + 1)) ∧
      ev tr t1 r1 pub (kd w) = ev tr t2 r2 pub (kd' w) ∧ ev tr t1 r1 pub (x w) = ev tr t2 r2 pub (x' w) := by
    intro w hw
    have e := congrArg (·[w]?) h
    simp only [List.getElem?_map, leaf_lo _ _ _ _ w hw, Option.map_some, Option.some.injEq] at e
    obtain ⟨a, b, c⟩ := triple_eq e
    obtain ⟨c1, c2⟩ := hi_split (hk w (by omega)) (hk' w (by omega)) (hx w (by omega)) (hx' w (by omega)) c
    exact ⟨a, b, c1, c2⟩
  have hi : ∀ v < 8, ev tr t1 r1 pub (cv (2 * v)) = ev tr t2 r2 pub (cv' (2 * v)) ∧
      ev tr t1 r1 pub (cv (2 * v + 1)) = ev tr t2 r2 pub (cv' (2 * v + 1)) ∧
      ev tr t1 r1 pub (kd (8 + v)) = ev tr t2 r2 pub (kd' (8 + v)) ∧
      ev tr t1 r1 pub (x (8 + v)) = ev tr t2 r2 pub (x' (8 + v)) := by
    intro v hv
    have e := congrArg (·[8 + v]?) h
    simp only [List.getElem?_map, leaf_hi _ _ _ _ v hv, Option.map_some, Option.some.injEq] at e
    obtain ⟨a, b, c⟩ := triple_eq e
    obtain ⟨c1, c2⟩ := hi_split (hk _ (by omega)) (hk' _ (by omega)) (hx _ (by omega)) (hx' _ (by omega)) c
    exact ⟨a, b, c1, c2⟩
  intro u hu
  have pvu : ev tr t1 r1 pub (pv u) = ev tr t2 r2 pub (pv' u) := by
    rcases Nat.mod_two_eq_zero_or_one u with h2 | h2
    · have := (lo (u / 2) (by omega)).1; rwa [show 2 * (u / 2) = u by omega] at this
    · have := (lo (u / 2) (by omega)).2.1; rwa [show 2 * (u / 2) + 1 = u by omega] at this
  have cvu : ev tr t1 r1 pub (cv u) = ev tr t2 r2 pub (cv' u) := by
    rcases Nat.mod_two_eq_zero_or_one u with h2 | h2
    · have := (hi (u / 2) (by omega)).1; rwa [show 2 * (u / 2) = u by omega] at this
    · have := (hi (u / 2) (by omega)).2.1; rwa [show 2 * (u / 2) + 1 = u by omega] at this
  by_cases h8 : u < 8
  · exact ⟨(lo u h8).2.2.1, (lo u h8).2.2.2, pvu, cvu⟩
  · have := hi (u - 8) (by omega)
    rw [show 8 + (u - 8) = u by omega] at this
    exact ⟨this.2.2.1, this.2.2.2, pvu, cvu⟩

theorem ev_slot0 {t r : Nat} {pp cp wr : Expr} {plx clx : Nat → Expr}
    (h1 : ev tr t r pub pp ≤ 1) (h2 : ev tr t r pub cp ≤ 1) (h3 : ev tr t r pub wr ≤ 1) :
    ev tr t r pub (leafX pp cp wr plx clx 0) = ev tr t r pub pp + 2 * ev tr t r pub cp + 4 * ev tr t r pub wr := by
  have e : leafX pp cp wr plx clx 0 = pp + K 2 * cp + K 4 * wr := by simp [leafX]
  rw [e, ev_hadd, ev_hadd, ev_hmul, ev_hmul, show K 2 = Expr.const 2 from rfl,
    show K 4 = Expr.const 4 from rfl, ev_const, ev_const]
  generalize ev tr t r pub pp = a at h1 ⊢
  generalize ev tr t r pub cp = b at h2 ⊢
  generalize ev tr t r pub wr = c at h3 ⊢
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;>
    rcases (show c = 0 ∨ c = 1 by omega) with rfl | rfl <;> rfl

/-- Slot 0 splits into the three flags. -/
theorem slot0 {pp cp wr pp' cp' wr' : Expr} {plx clx plx' clx' : Nat → Expr}
    (h1 : ev tr t1 r1 pub pp ≤ 1) (h2 : ev tr t1 r1 pub cp ≤ 1) (h3 : ev tr t1 r1 pub wr ≤ 1)
    (h1' : ev tr t2 r2 pub pp' ≤ 1) (h2' : ev tr t2 r2 pub cp' ≤ 1) (h3' : ev tr t2 r2 pub wr' ≤ 1)
    (h : ev tr t1 r1 pub (leafX pp cp wr plx clx 0) = ev tr t2 r2 pub (leafX pp' cp' wr' plx' clx' 0)) :
    ev tr t1 r1 pub pp = ev tr t2 r2 pub pp' ∧ ev tr t1 r1 pub cp = ev tr t2 r2 pub cp' ∧
      ev tr t1 r1 pub wr = ev tr t2 r2 pub wr' := by
  rw [ev_slot0 h1 h2 h3, ev_slot0 h1' h2' h3'] at h
  omega

/-- The value of a length from its chunks. -/
theorem ev_chunks (ch : Nat → Expr) {t r : Nat} :
    ev tr t r pub (sumE ((List.range LEN_CHUNKS).map fun k => K (64 ^ k) * ch k)) =
      ((List.range LEN_CHUNKS).map fun k => 64 ^ k % P * ev tr t r pub (ch k) % P).sum % P := by
  rw [ev_sumE, List.map_map]
  congr 2
  apply List.map_congr_left
  intro k _
  simp only [Function.comp_def, ev_hmul, K, ev_const]

/-- **Lengths with equal chunks are equal** (both rows satisfy `lenChunks`). -/
theorem len_eq {v v' : Expr} {ch ch' : Nat → Expr}
    (hv : ev tr t1 r1 pub (lenChunks v ch) = 0) (hv' : ev tr t2 r2 pub (lenChunks v' ch') = 0)
    (h : ∀ k < LEN_CHUNKS, ev tr t1 r1 pub (ch k) = ev tr t2 r2 pub (ch' k)) :
    ev tr t1 r1 pub v = ev tr t2 r2 pub v' := by
  unfold lenChunks at hv hv'
  rw [eq_of_sub hv, eq_of_sub hv', ev_chunks, ev_chunks]
  have e : ((List.range LEN_CHUNKS).map fun k => 64 ^ k % P * ev tr t1 r1 pub (ch k) % P) =
      (List.range LEN_CHUNKS).map fun k => 64 ^ k % P * ev tr t2 r2 pub (ch' k) % P :=
    List.map_congr_left (fun k hk => by rw [h k (List.mem_range.1 hk)])
  rw [e]

end

/-! ## Leaf rows and their contents -/

/-- The expressions of a leaf row: its block is `leafBlock kd (leafX pp cp wr plx clx) pv cv`. -/
structure LE where
  kd : Nat → Expr
  pv : Nat → Expr
  cv : Nat → Expr
  plx : Nat → Expr
  clx : Nat → Expr
  pp : Expr
  cp : Expr
  wr : Expr
  pl : Expr
  cl : Expr

def LE.blk (e : LE) : List W3 := leafBlock e.kd (leafX e.pp e.cp e.wr e.plx e.clx) e.pv e.cv

section
variable (tr : Trace Fp) (pub : List Fp) (t r : Nat)

/-- The row facts a leaf row needs (ranges, flags, the length chunks). -/
def LE.OK (e : LE) : Prop :=
  (∀ u < 16, ev tr t r pub (e.kd u) < 2 ^ 16) ∧
  (∀ k < LEN_CHUNKS, ev tr t r pub (e.plx k) < 256 ∧ ev tr t r pub (e.clx k) < 256) ∧
  ev tr t r pub e.pp ≤ 1 ∧ ev tr t r pub e.cp ≤ 1 ∧ ev tr t r pub e.wr ≤ 1 ∧
  ev tr t r pub (lenChunks e.pl e.plx) = 0 ∧ ev tr t r pub (lenChunks e.cl e.clx) = 0

def LE.kdV (e : LE) : List Nat := vecN tr pub t r e.kd 16
/-- The pre-value ref `(pp, pl, pv16)`. -/
def LE.preV (e : LE) : List Nat := [ev tr t r pub e.pp, ev tr t r pub e.pl] ++ vecN tr pub t r e.pv 16
/-- The current value and written flag `(cp, cl, cv16, wr)` (the `WM` value format). -/
def LE.curV (e : LE) : List Nat :=
  [ev tr t r pub e.cp, ev tr t r pub e.cl] ++ vecN tr pub t r e.cv 16 ++ [ev tr t r pub e.wr]

end

/-- **Equal blocks, equal contents** (two leaf rows of any tables). -/
theorem content_eq {tr : Trace Fp} {pub : List Fp} {t1 r1 t2 r2 : Nat} {e1 e2 : LE}
    (h1 : e1.OK tr pub t1 r1) (h2 : e2.OK tr pub t2 r2)
    (hb : e1.blk.map (dec3 tr t1 r1 pub) = e2.blk.map (dec3 tr t2 r2 pub)) :
    e1.kdV tr pub t1 r1 = e2.kdV tr pub t2 r2 ∧ e1.preV tr pub t1 r1 = e2.preV tr pub t2 r2 ∧
      e1.curV tr pub t1 r1 = e2.curV tr pub t2 r2 := by
  obtain ⟨k1, c1, p1, q1, w1, l1, m1⟩ := h1
  obtain ⟨k2, c2, p2, q2, w2, l2, m2⟩ := h2
  have x1 := leafX_lt p1 q1 w1 (fun k hk => (c1 k hk).1) (fun k hk => (c1 k hk).2)
  have x2 := leafX_lt p2 q2 w2 (fun k hk => (c2 k hk).1) (fun k hk => (c2 k hk).2)
  have hf := block_fields hb k1 k2 x1 x2
  obtain ⟨e0, e0', e0''⟩ := slot0 p1 q1 w1 p2 q2 w2 (hf 0 (by decide)).2.1
  have ch : ∀ k < LEN_CHUNKS, ev tr t1 r1 pub (e1.plx k) = ev tr t2 r2 pub (e2.plx k) ∧
      ev tr t1 r1 pub (e1.clx k) = ev tr t2 r2 pub (e2.clx k) := by
    intro k hk
    have hk4 : k < 4 := hk
    have a := (hf (k + 1) (by omega)).2.1
    have b := (hf (k + 5) (by omega)).2.1
    rw [leafX_p _ _ _ _ _ k hk4, leafX_p _ _ _ _ _ k hk4] at a
    rw [leafX_c _ _ _ _ _ k hk4, leafX_c _ _ _ _ _ k hk4] at b
    exact ⟨a, b⟩
  have hpl := len_eq l1 l2 (fun k hk => (ch k hk).1)
  have hcl := len_eq m1 m2 (fun k hk => (ch k hk).2)
  have vk : ∀ f g : Nat → Expr, (∀ u < 16, ev tr t1 r1 pub (f u) = ev tr t2 r2 pub (g u)) →
      vecN tr pub t1 r1 f 16 = vecN tr pub t2 r2 g 16 := fun f g h =>
    List.map_congr_left (fun u hu => h u (List.mem_range.1 hu))
  refine ⟨vk _ _ fun u hu => (hf u hu).1, ?_, ?_⟩
  · simp only [LE.preV, e0, hpl, vk _ _ fun u hu => (hf u hu).2.2.1]
  · simp only [LE.curV, e0', e0'', hcl, vk _ _ fun u hu => (hf u hu).2.2.2]

/-! ## The three kinds of leaf rows -/

def wslOldE : LE := ⟨fun t => Wsl.c "kd" t, fun t => Wsl.c "pv" t, fun t => Wsl.c "cv" t, fun k => Wsl.c "plx" k,
  fun k => Wsl.c "clx" k, Wsl.c "pp", Wsl.c "cp", Wsl.c "wr", Wsl.c "pl", Wsl.c "cl"⟩
def wslNewE : LE := ⟨fun t => Wsl.c "kd" t, fun t => Wsl.c "pv" t, fun t => Wsl.c "ncv" t, fun k => Wsl.c "plx" k,
  fun k => Wsl.c "nclx" k, Wsl.c "pp", Wsl.c "ncp", Wsl.c "nwr", Wsl.c "pl", Wsl.c "ncl"⟩
def wsbE : LE := ⟨fun t => Wsb.c "kd" t, fun t => Wsb.c "pv" t, fun t => Wsb.c "cv" t, fun k => Wsb.c "plx" k,
  fun k => Wsb.c "clx" k, Wsb.c "pp", Wsb.c "cp", Wsb.c "wr", Wsb.c "pl", Wsb.c "cl"⟩

theorem wslOld_blk : wslOldE.blk = wslOldB := rfl
theorem wslNew_blk : wslNewE.blk = wslNewB := rfl
theorem wsb_blk : wsbE.blk = Wsb.leaf := rfl

theorem wslOld_cur {tr : Trace Fp} {pub : List Fp} {r : Nat} :
    wslOldE.curV tr pub 10 r = (wslRow tr pub r).cur := rfl
theorem wslNew_cur {tr : Trace Fp} {pub : List Fp} {r : Nat} :
    wslNewE.curV tr pub 10 r = (wslRow tr pub r).ncur := rfl
theorem wslNew_pre {tr : Trace Fp} {pub : List Fp} {r : Nat} :
    wslNewE.preV tr pub 10 r = wslOldE.preV tr pub 10 r := rfl
theorem wslNew_kd {tr : Trace Fp} {pub : List Fp} {r : Nat} :
    wslNewE.kdV tr pub 10 r = wslOldE.kdV tr pub 10 r := rfl

/-- **Premise**: a real `WSB` row's `kd` limbs are 16-bit (they are `KDIG`'s: the `KEY` table's
SHA-256 digest bytes, paired; not decoded here). -/
def WsbKdRange (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 5 → (Wsb.c "real").eval tr 5 r pub = 1 → ∀ j < 16, ev tr 5 r pub (Wsb.c "kd" j) < 2 ^ 16

/-! ## Row facts -/

theorem wslLD (tr : Trace Fp) (pub : List Fp) (D : Nat) (ph i : Nat) (hi : i < 2 ^ D) :
    (wsLeaves tr pub D ph)[i]? = some (rowDig tr 5 (ph * 2 ^ D + i) pub (fun j => Wsb.c "dg" j)) := by
  simp only [wsLeaves, slice, List.getElem?_map, List.getElem?_range hi, Option.map_some, lv,
    Nat.zero_mul, Nat.zero_add]

section Facts
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}
  {compress : List Nat → List Nat → List Nat}
  (hH : Holds (fullAir D extra nb np) pub tr)
  (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧ i.bus ≠ B_RNG)
  (hcomp : CompressOK compress)
  (hC : Sha512IfContract compress ((busList (fullAir D extra nb np) tr pub B_IF384 true).map decIf))

theorem wsl_mem_len : lenChunks (Wsl.c "pl") (fun k => Wsl.c "plx" k) ∈ Wsl.constraints ∧
    lenChunks (Wsl.c "cl") (fun k => Wsl.c "clx" k) ∈ Wsl.constraints ∧
    lenChunks (Wsl.c "ncl") (fun k => Wsl.c "nclx" k) ∈ Wsl.constraints := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold Wsl.constraints; simp)

theorem wsb_mem_len : lenChunks (Wsb.c "pl") (fun k => Wsb.c "plx" k) ∈ Wsb.constraints D ∧
    lenChunks (Wsb.c "cl") (fun k => Wsb.c "clx" k) ∈ Wsb.constraints D := by
  refine ⟨?_, ?_⟩ <;> (unfold Wsb.constraints; simp)

theorem wsb_mem_b (s : String) (hs : s ∈ ["pp", "cp", "wr"]) : bool (Wsb.c s) ∈ Wsb.constraints D := by
  unfold Wsb.constraints
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;> simp

include hH hx hcomp hC in
/-- An active `WSL` row's two leaf rows satisfy `LE.OK`. -/
theorem wsl_okE {r : Nat} (hr : r < tr.height 10) (hA : (Wsl.c "act").eval tr 10 r pub = 1) :
    wslOldE.OK tr pub 10 r ∧ wslNewE.OK tr pub 10 r := by
  obtain ⟨-, -, hkd, hch⟩ := wsl_leaf hH hx hcomp hC hr hA
  have hc := holds_constr hH (t := 10) (by decide) full_wsl r hr
  have b : ∀ s, s ∈ ["act", "pp", "cp", "wr", "ncp", "nwr"] → ev tr 10 r pub (Wsl.c s) ≤ 1 :=
    fun s hs => bool_le (hold rfl hc (wsl_mem_b s hs))
  obtain ⟨m1, m2, m3⟩ := wsl_mem_len
  exact ⟨⟨hkd, fun k hk => ⟨by have := (hch k hk).1; simp only [wslOldE]; omega,
      by have := (hch k hk).2.1; simp only [wslOldE]; omega⟩,
      b "pp" (by simp), b "cp" (by simp), b "wr" (by simp), hold rfl hc m1, hold rfl hc m2⟩,
    ⟨hkd, fun k hk => ⟨by have := (hch k hk).1; simp only [wslNewE]; omega,
      by have := (hch k hk).2.2; simp only [wslNewE]; omega⟩,
      b "pp" (by simp), b "ncp" (by simp), b "nwr" (by simp), hold rfl hc m1, hold rfl hc m3⟩⟩

include hH hx hcomp hC in
/-- **A real `WSB` row's leaf**: its digest is the leaf compression of its block, and (with
`WsbKdRange`) it satisfies `LE.OK`. -/
theorem wsb_leaf (hW : WsbKdRange tr pub) {r : Nat} (hr : r < tr.height 5)
    (hR : (Wsb.c "real").eval tr 5 r pub = 1) :
    wsbE.OK tr pub 5 r ∧ ∃ bw : List Nat, GoodB bw ∧ wsbE.blk.map (dec3 tr 5 r pub) = bw.map wlimbs ∧
      rowDig tr 5 r pub (fun j => Wsb.c "dg" j) = digest6 (compress IV384 bw) := by
  have hperm := holds_perm hH B_IF384
  have hlt : 5 < (fullAir D extra nb np).tables.length := by rw [full_len]; omega
  have hc := holds_constr hH (t := 5) (by decide) (full_wsb (D := D)) r hr
  have rng : ∀ e : Expr, rcv B_RNG (Wsb.c "real") [e] ∈ Wsb.interactions → ev tr 5 r pub e < 256 :=
    fun e he => rng_rcv hH (hxR hx) hlt (by rw [full_wsb]; exact he) hr hR
  have hch : ∀ k < LEN_CHUNKS, ev tr 5 r pub (Wsb.c "plx" k) < 256 ∧ ev tr 5 r pub (Wsb.c "clx" k) < 256 := by
    intro k hk
    have m : ∀ e, e ∈ [rcv B_RNG (Wsb.c "real") [Wsb.c "plx" k], rcv B_RNG (Wsb.c "real") [Wsb.c "clx" k]] →
        e ∈ Wsb.interactions := fun e he =>
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, he⟩)))
    exact ⟨rng _ (m _ (by simp)), rng _ (m _ (by simp))⟩
  have b : ∀ s, s ∈ ["pp", "cp", "wr"] → ev tr 5 r pub (Wsb.c s) ≤ 1 :=
    fun s hs => bool_le (hold rfl hc (wsb_mem_b (D := D) s hs))
  obtain ⟨m1, m2⟩ := wsb_mem_len (D := D)
  refine ⟨⟨hW r hr hR, hch, b "pp" (by simp), b "cp" (by simp), b "wr" (by simp), hold rfl hc m1, hold rfl hc m2⟩, ?_⟩
  have hm := comp_mem hperm hlt (g := Wsb.c "real") (cid := Wsb.c "cid")
    (ws := ivW ++ Wsb.leaf ++ digW (fun t => Wsb.c "dg" t) ++ wordsOf (fun t => Wsb.c "dx" t) 2)
    (fun i hi => by
      rw [full_wsb]
      exact List.mem_append_left _ (List.mem_append_right _ hi)) hr hR
  rw [leaf_dec] at hm
  obtain ⟨bw, h16, hw, eB, eo⟩ := comp_iv hcomp hC (by simp [Wsb.leaf, leafBlock]) (by simp [digW])
    (by simp [wordsOf]) hm
  exact ⟨bw, ⟨h16, hw⟩, eB, rowDig_of eo⟩

end Facts

/-- **INTAKE rows**: a phase-0 `WSB` row's current value is its pre-value, not written. -/
theorem wsb_ph0_cur {D : Nat} {tr : Trace Fp} {pub : List Fp} {r : Nat}
    (hc : ∀ e ∈ (Wsb.table D).constraints, e.eval tr 5 r pub = 0) (hp : ev tr 5 r pub (Wsb.c "ph") = 0) :
    wsbE.curV tr pub 5 r = wsbE.preV tr pub 5 r ++ [0] := by
  have g := ev_one_sub0 (tr := tr) (t := 5) (r := r) (pub := pub) hp
  have k : ∀ e, (1 - Wsb.c "ph") * e ∈ Wsb.constraints D → ev tr 5 r pub e = 0 :=
    fun e he => FieldWsb.wsb_gate g (hold rfl hc he)
  have e1 : ev tr 5 r pub (Wsb.c "cp") = ev tr 5 r pub (Wsb.c "pp") :=
    eq_of_sub (k (Wsb.c "cp" - Wsb.c "pp") (by unfold Wsb.constraints; simp))
  have e2 : ev tr 5 r pub (Wsb.c "cl") = ev tr 5 r pub (Wsb.c "pl") :=
    eq_of_sub (k (Wsb.c "cl" - Wsb.c "pl") (by unfold Wsb.constraints; simp))
  have e3 : ev tr 5 r pub (Wsb.c "wr") = 0 := k _ (by unfold Wsb.constraints; simp)
  have e4 : ∀ j < 16, ev tr 5 r pub (Wsb.c "cv" j) = ev tr 5 r pub (Wsb.c "pv" j) := fun j hj =>
    eq_of_sub (k (Wsb.c "cv" j - Wsb.c "pv" j) (by
      unfold Wsb.constraints
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, by simp⟩)))))
  simp only [LE.curV, LE.preV, wsbE, List.cons_append, List.singleton_append, List.append_assoc]
  have e5 : vecN tr pub 5 r (fun t => Wsb.c "cv" t) 16 = vecN tr pub 5 r (fun t => Wsb.c "pv" t) 16 :=
    List.map_congr_left (fun j hj => e4 j (List.mem_range.1 hj))
  rw [e1, e2, e3, e5]

end StateM5a.WsLeafF
