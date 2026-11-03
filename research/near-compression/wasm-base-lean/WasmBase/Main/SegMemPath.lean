import WasmBase.Main.SegIface
import WasmBase.Main.SegShaMemb
import WasmBase.Main.SegShaMpath

/-!
# WasmBase.Main.SegMemPath — MPATH blocks as byte-level Merkle paths (E2E M4c, sub-lane MEM)

Preparation for the memory-root conjunct (`Main/SegMemRoot.lean`):

* `write_access_pd`: lane B's `Merkle.write_access_sound` with the hash injective only on digests
  satisfying a predicate `Pd` (for SHA-384: 48-byte strings, injective unless `Sha384Coll`).
* `Canon x b`: an 18-limb field digest `x` is the limbs of six 64-bit words whose bytes are `b`
  (`PubDigIs pub k b` is `Canon (pubDig pub k) b`).  `mfold_canon`: MPATH's limb-level fold
  `mfold shaNode` of canonical digests is canonical and its bytes are lane B's `pathRoot nodeH`.
* The MPATH block structure: every top row has a unique block start (`mp_block_of_top`,
  `mp_block_unique`), every active bottom row ends in a top row (`mp_block_of_bot`);
  `mp_block_bytes`: a block of a `HoldsX` trace is, in bytes, a Merkle path of depth `D` (public)
  at the index `blk` (`sidesOk`), old root `pathRoot (old leaf)`, new root `pathRoot (new leaf)`, both
  canonical — the new one also for read-only blocks once the leaf message says new = old.
-/

namespace WasmBase

open ZkFormal.Algebra Chips Seg StateM5a.Sha512If
open NearSpecV3.E2E.Bnd (Sha384Coll sha384 sha384_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace MemRoot

open StateM5a.Merkle

/-! ## 1. Merkle write access with a partially injective hash -/

section generic
variable {α : Type} (H : α → α → α) (Pd : α → Prop)

theorem up_pd (hH : ∀ a b, Pd (H a b)) : ∀ (l : List α) (x : α), x ∈ up H l → Pd x
  | a :: b :: r, x, hx => by
    simp only [up, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hH a b
    · exact up_pd hH r x hx
  | [], x, hx => by simp [up] at hx
  | [_], x, hx => by simp [up] at hx

/-- **`Merkle.write_access_sound` for a hash injective on `Pd`-digests.** -/
theorem write_access_pd (hH : ∀ a b, Pd (H a b))
    (hinj : ∀ a b c d, Pd a → Pd b → Pd c → Pd d → H a b = H c d → a = c ∧ b = d) :
    ∀ (D : Nat) (l : List α) (i : Nat) (x : α) (ps : List (Bool × α)),
      (∀ y ∈ l, Pd y) → Pd x → (∀ p ∈ ps, Pd p.2) →
      l.length = 2 ^ D → i < 2 ^ D → ps.length = D → sidesOk i ps →
      root H D l = some (pathRoot H x ps) →
      l[i]? = some x ∧ ∀ x', root H D (l.set i x') = some (pathRoot H x' ps)
  | 0, l, i, x, ps, _, _, _, hl, hi, hp, _, hr => by
    match l, ps with
    | [y], [] =>
      have : i = 0 := by simp at hi; omega
      subst this
      simp only [root, pathRoot, Option.some.injEq] at hr
      subst hr
      exact ⟨rfl, fun x' => rfl⟩
    | [], _ => simp at hl
    | _ :: _ :: _, _ => simp at hl
    | [_], _ :: _ => simp at hp
  | D + 1, l, i, x, ps, hlP, hxP, hpP, hl, hi, hp, hs, hr => by
    match ps with
    | [] => simp at hp
    | (s, y) :: ps' =>
      simp only [sidesOk] at hs
      obtain ⟨hs1, hs2⟩ := hs
      have hyP : Pd y := hpP (s, y) List.mem_cons_self
      have hpP' : ∀ p ∈ ps', Pd p.2 := fun p hp => hpP p (List.mem_cons_of_mem _ hp)
      simp only [pathRoot] at hr
      simp only [root] at hr
      have hul : (up H l).length = 2 ^ D := by rw [up_length, hl, Nat.pow_succ]; omega
      have hi2 : i / 2 < 2 ^ D := by rw [Nat.pow_succ] at hi; omega
      have hp' : ps'.length = D := by simpa using hp
      have hxP' : Pd (if s then H y x else H x y) := by split <;> exact hH _ _
      obtain ⟨hx1, hupd⟩ := write_access_pd hH hinj D (up H l) (i / 2) _ ps' (up_pd H Pd hH l) hxP' hpP'
        hul hi2 hp' hs2 hr
      have hlen : 2 * (i / 2) + 1 < l.length := by rw [hl, Nat.pow_succ]; omega
      obtain ⟨a, ha⟩ : ∃ a, l[2 * (i / 2)]? = some a :=
        ⟨l[2 * (i / 2)]'(by omega), List.getElem?_eq_getElem _⟩
      obtain ⟨b, hb⟩ : ∃ b, l[2 * (i / 2) + 1]? = some b :=
        ⟨l[2 * (i / 2) + 1]'hlen, List.getElem?_eq_getElem _⟩
      have haP : Pd a := hlP a (List.mem_of_getElem? ha)
      have hbP : Pd b := hlP b (List.mem_of_getElem? hb)
      have hpair := up_pair H l (i / 2) a b ha hb
      rw [hpair] at hx1
      simp only [Option.some.injEq] at hx1
      by_cases hodd : i % 2 = 1
      · have hsT : s = true := by simp [hs1, hodd]
        subst hsT
        simp only [ite_true] at hx1
        obtain ⟨hay, hbx⟩ := hinj _ _ _ _ haP hbP hyP hxP hx1
        subst hay; subst hbx
        have hi' : i = 2 * (i / 2) + 1 := by omega
        refine ⟨by rw [hi']; exact hb, fun x' => ?_⟩
        simp only [root, pathRoot, ite_true]
        rw [hi', up_set_odd H l (i / 2) x' a ha (by rw [hb]; simp)]
        exact hupd (H a x')
      · have hsF : s = false := by simp [hs1, hodd]
        subst hsF
        simp only [Bool.false_eq_true, ite_false] at hx1
        obtain ⟨hax, hby⟩ := hinj _ _ _ _ haP hbP hxP hyP hx1
        subst hax; subst hby
        have hi' : i = 2 * (i / 2) := by omega
        refine ⟨by rw [hi']; exact ha, fun x' => ?_⟩
        simp only [root, pathRoot, Bool.false_eq_true, ite_false]
        rw [hi', up_set_even H l (i / 2) x' b hb]
        exact hupd (H x' b)

end generic

/-! ## 2. SHA-384 nodes on 48-byte digests -/

/-- 48-byte digests. -/
def D48 (x : ArenaCore.Bytes) : Prop := x.length = 48

theorem nodeH_d48 (a b : ArenaCore.Bytes) : D48 (StateM5a.StateView.nodeH a b) := sha384_length _

/-- Without a SHA-384 collision, `nodeH` is injective on 48-byte children. -/
theorem nodeH_inj (hn : ¬ Sha384Coll) : ∀ a b c d, D48 a → D48 b → D48 c → D48 d →
    StateM5a.StateView.nodeH a b = StateM5a.StateView.nodeH c d → a = c ∧ b = d := by
  intro a b c d ha _ hc _ h
  classical
  by_cases e : a ++ b = c ++ d
  · exact List.append_inj e (by rw [ha, hc])
  · exact absurd (StateM5a.StateView.sha384_coll e h) hn

/-- Without a SHA-384 collision, SHA-384 is injective. -/
theorem sha384_inj (hn : ¬ Sha384Coll) {a b : ArenaCore.Bytes} (h : sha384 a = sha384 b) : a = b := by
  classical
  by_cases e : a = b
  · exact e
  · exact absurd (StateM5a.StateView.sha384_coll e h) hn

/-! ## 3. Canonical limb digests -/

/-- `x` (18 field limbs) is the limbs of six 64-bit words whose bytes are `b`. -/
def Canon (x : List F) (b : ArenaCore.Bytes) : Prop :=
  ∃ d : List Nat, d.length = 6 ∧ W64 d ∧ x = SegSha.limbsF d ∧ SegSha.wbytes d = b

/-- The bytes a canonical limb digest stands for. -/
def bytesOf (x : List F) : ArenaCore.Bytes := SegSha.wbytes (SegSha.decF x)

theorem Canon.bytes {x : List F} {b : ArenaCore.Bytes} (h : Canon x b) : bytesOf x = b := by
  obtain ⟨d, hl, hw, rfl, rfl⟩ := h
  rw [bytesOf, SegSha.decF_limbsF hl hw]

theorem Canon.d48 {x : List F} {b : ArenaCore.Bytes} (h : Canon x b) : D48 b := by
  obtain ⟨d, hl, -, -, rfl⟩ := h
  show (SegSha.wbytes d).length = 48
  rw [SegSha.wbytes_length, hl]

theorem canon_of {x : List F} {d : List Nat} (hl : d.length = 6) (hw : W64 d) (e : x = SegSha.limbsF d) :
    Canon x (bytesOf x) := ⟨d, hl, hw, e, by rw [e, bytesOf, SegSha.decF_limbsF hl hw]⟩

theorem pubDigIs_iff {pub : List F} {k : Nat} {b : ArenaCore.Bytes} : PubDigIs pub k b ↔ Canon (pubDig pub k) b :=
  Iff.rfl

/-- The byte path of an MPATH `(sibling, bit)` list. -/
def bpath (L : List (List F × F)) : List (Bool × ArenaCore.Bytes) :=
  L.map fun p => (decide (p.2 = 1), bytesOf p.1)

/-- **MPATH's limb-level fold is lane B's byte-level path root** on canonical digests. -/
theorem mfold_canon : ∀ (L : List (List F × F)) (cur : List F) (bc : ArenaCore.Bytes), Canon cur bc →
    (∀ p ∈ L, Canon p.1 (bytesOf p.1)) →
    Canon (mfold SegSha.shaNode cur L) (pathRoot StateM5a.StateView.nodeH bc (bpath L))
  | [], cur, bc, h, _ => h
  | (sib, b) :: L, cur, bc, h, hL => by
    obtain ⟨dc, lc, wc, ec, bce⟩ := h
    obtain ⟨ds, ls, ws, es, bse⟩ := hL (sib, b) List.mem_cons_self
    simp only at es bse
    have hstep : Canon (mstep SegSha.shaNode cur sib b)
        (if decide (b = 1) then StateM5a.StateView.nodeH (bytesOf sib) bc
          else StateM5a.StateView.nodeH bc (bytesOf sib)) := by
      unfold mstep
      by_cases hb : b = 1
      · rw [if_pos hb, if_pos (by simp [hb])]
        obtain ⟨dout, l3, w3, e3, b3⟩ := SegSha.shaNode_sha384 ls lc ws wc
        refine ⟨dout, l3, w3, by rw [es, ec]; exact e3, ?_⟩
        rw [b3, bse, bce]; rfl
      · rw [if_neg hb, if_neg (by simp [hb])]
        obtain ⟨dout, l3, w3, e3, b3⟩ := SegSha.shaNode_sha384 lc ls wc ws
        refine ⟨dout, l3, w3, by rw [es, ec]; exact e3, ?_⟩
        rw [b3, bse, bce]; rfl
    have := mfold_canon L _ _ hstep (fun p hp => hL p (List.mem_cons_of_mem _ hp))
    simpa only [mfold, bpath, List.map_cons, pathRoot] using this

theorem bpath_length (L : List (List F × F)) : (bpath L).length = L.length := by simp [bpath]

theorem bpath_d48 {L : List (List F × F)} (hL : ∀ p ∈ L, Canon p.1 (bytesOf p.1)) :
    ∀ p ∈ bpath L, D48 p.2 := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact (hL q hq).d48

/-- The natural number with binary digits `g 0, g 1, …, g (n − 1)` (least significant first). -/
def natOf : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, g => (if g 0 then 1 else 0) + 2 * natOf n (fun l => g (l + 1))

theorem natOf_lt : ∀ (n : Nat) (g : Nat → Bool), natOf n g < 2 ^ n
  | 0, _ => by simp [natOf]
  | n + 1, g => by
    have := natOf_lt n (fun l => g (l + 1))
    simp only [natOf, Nat.pow_succ]; split <;> omega

/-- The side bits of a path are the binary digits of `natOf`. -/
theorem sidesOk_natOf {β : Type} : ∀ (n : Nat) (g : Nat → Bool) (y : Nat → β),
    sidesOk (natOf n g) ((List.range n).map fun l => (g l, y l))
  | 0, _, _ => trivial
  | n + 1, g, y => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    refine ⟨?_, ?_⟩
    · simp only [natOf]; cases g 0 <;> simp <;> omega
    · have e : natOf (n + 1) g / 2 = natOf n (fun l => g (l + 1)) := by
        simp only [natOf]; split <;> omega
      rw [e]
      exact sidesOk_natOf n (fun l => g (l + 1)) (fun l => y (l + 1))

theorem foldr_range_succ (h : Nat → F) (n : Nat) :
    ((List.range (n + 1)).map h).foldr (· + ·) 0 = h 0 + ((List.range n).map fun l => h (l + 1)).foldr (· + ·) 0 := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl

/-- The field sum `Σ bit_l·2^l` of bits is the cast of `natOf`. -/
theorem bitsum_natOf : ∀ (n : Nat) (b : Nat → F), (∀ l, l < n → b l = 0 ∨ b l = 1) →
    ((List.range n).map fun l => b l * ((2 ^ l : Nat) : F)).foldr (· + ·) 0 =
      ((natOf n (fun l => decide (b l = 1)) : Nat) : F)
  | 0, _, _ => rfl
  | n + 1, b, hb => by
    rw [foldr_range_succ]
    have ih := bitsum_natOf n (fun l => b (l + 1)) (fun l hl => hb (l + 1) (by omega))
    have e : ((List.range n).map fun l => b (l + 1) * ((2 ^ (l + 1) : Nat) : F)).foldr (· + ·) 0 =
        2 * ((List.range n).map fun l => b (l + 1) * ((2 ^ l : Nat) : F)).foldr (· + ·) 0 := by
      generalize List.range n = L
      induction L with
      | nil => show (0 : F) = 2 * 0; grind
      | cons a L ihL =>
        simp only [List.map_cons, List.foldr_cons, ihL, Nat.pow_succ, Lean.Grind.Semiring.natCast_mul]
        grind
    rw [e, ih]
    simp only [natOf, Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]
    have p0 : ((2 ^ 0 : Nat) : F) = 1 := rfl
    have c2 : ((2 : Nat) : F) = 2 := rfl
    rcases hb 0 (by omega) with h | h
    · have h' : decide (b 0 = 1) = false := by rw [h]; decide
      simp only [h', h, p0, c2, Bool.false_eq_true, if_false]
      show 0 * 1 + _ = ((0 : Nat) : F) + _; grind
    · have h' : decide (b 0 = 1) = true := by rw [h]; decide
      simp only [h', h, p0, c2, if_true]
      show 1 * 1 + _ = ((1 : Nat) : F) + _; grind

/-! ## 4. MPATH blocks -/

/-- Rows `r0 … r` of MPATH form one block: `r0` active and bottom, `r` top, no top row between. -/
def MpBlock (tr : Trace) (r0 r : Nat) : Prop :=
  r0 ≤ r ∧ r < tr.height 20 ∧ mc tr r0 0 = 1 ∧ mc tr r0 1 = 1 ∧ mc tr r 2 = 1 ∧
    ∀ r', r0 ≤ r' → r' < r → mc tr r' 2 = 0

theorem sel_eq {tr : Trace} {r base : Nat} :
    (mc tr r 3 = 0 → selL tr r base = mdig tr r base ∧ selR tr r base = mdig tr r 48) ∧
    (mc tr r 3 = 1 → selL tr r base = mdig tr r 48 ∧ selR tr r base = mdig tr r base) := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩ <;>
    (simp only [selL, selR, mdig]; apply List.map_congr_left; intro i _; rw [h]; grind)

/-- The `(sibling, bit)` list of a block of `n` rows from `r0`. -/
def mpL (tr : Trace) (r0 n : Nat) : List (List F × F) :=
  (List.range n).map fun l => (mdig tr (r0 + l) 48, mc tr (r0 + l) 3)

/-- Its bit function. -/
def mpBits (tr : Trace) (r0 : Nat) : Nat → Bool := fun l => decide (mc tr (r0 + l) 3 = 1)

theorem bpath_mpL (tr : Trace) (r0 n : Nat) :
    bpath (mpL tr r0 n) = (List.range n).map fun l => (mpBits tr r0 l, bytesOf (mdig tr (r0 + l) 48)) := by
  simp [bpath, mpL, mpBits]

section blocks
variable {nloc ngl : Nat} {pub : List F} {tr : Trace} (H : HoldsX (wasmBaseSegAir nloc ngl) pub tr)
include H

theorem mp_back : ∀ r, r < tr.height 20 → mc tr r 0 = 1 →
    ∃ r0, r0 ≤ r ∧ mc tr r0 1 = 1 ∧ ∀ r', r0 ≤ r' → r' < r → mc tr r' 2 = 0 := by
  intro r
  induction r with
  | zero => intro hr ha; exact ⟨0, Nat.le_refl _, ((mp_edges H hr).1 rfl ha).1, fun r' h1 h2 => by omega⟩
  | succ r ih =>
    intro hr ha
    rcases (mp_bool H hr).2.1 with hb | hb
    · have har : mc tr r 0 = 1 := (mp_kb H hr ha).1 r (by omega)
      have ht : mc tr r 2 = 0 := by
        rcases (mp_bool H (r := r) (by omega)).2.2.1 with h | h
        · exact h
        · have := ((mp_edges H (r := r) (by omega)).2.1 hr h ha).1
          rw [hb] at this; exact absurd this (by decide)
      obtain ⟨r0, h1, h2, h3⟩ := ih (by omega) har
      refine ⟨r0, by omega, h2, fun r' a b => ?_⟩
      by_cases e : r' = r
      · subst e; exact ht
      · exact h3 r' a (by omega)
    · exact ⟨r + 1, Nat.le_refl _, hb, fun r' h1 h2 => by omega⟩

/-- Every top row ends a block. -/
theorem mp_block_of_top {r : Nat} (hr : r < tr.height 20) (ht : mc tr r 2 = 1) : ∃ r0, MpBlock tr r0 r := by
  have ha := mp_top_act H hr ht
  obtain ⟨r0, h1, h2, h3⟩ := mp_back H r hr ha
  exact ⟨r0, h1, hr, (mp_kb H hr ha).1 r0 h1, h2, ht, h3⟩

/-- Every active bottom row starts a block. -/
theorem mp_block_of_bot {r0 : Nat} (hr0 : r0 < tr.height 20) (ha : mc tr r0 0 = 1) (hb : mc tr r0 1 = 1) :
    ∃ r, MpBlock tr r0 r := by
  have key : ∀ k r, r0 ≤ r → r + k + 1 = tr.height 20 → mc tr r 0 = 1 →
      (∀ r', r0 ≤ r' → r' < r → mc tr r' 2 = 0) → ∃ r, MpBlock tr r0 r := by
    intro k
    induction k with
    | zero =>
      intro r h0 hk har hmid
      have ht := (mp_edges H (r := r) (by omega)).2.2.2 (by omega) har
      exact ⟨r, h0, by omega, ha, hb, ht, hmid⟩
    | succ k ih =>
      intro r h0 hk har hmid
      rcases (mp_bool H (r := r) (by omega)).2.2.1 with ht | ht
      · have hn := mp_next H (r := r) (by omega) har ht
        exact ih (r + 1) (by omega) (by omega) hn.1 fun r' a b => by
          by_cases e : r' = r
          · subst e; exact ht
          · exact hmid r' a (by omega)
      · exact ⟨r, h0, by omega, ha, hb, ht, hmid⟩
  exact key (tr.height 20 - r0 - 1) r0 (Nat.le_refl _) (by omega) ha (fun r' a b => by omega)

/-- A top row's block start is unique. -/
theorem mp_block_unique {r0 r0' r : Nat} (h : MpBlock tr r0 r) (h' : MpBlock tr r0' r) : r0 = r0' := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := h'
  have side : ∀ x y, MpBlock tr x r → MpBlock tr y r → x < y → False := by
    intro x y hx hy hxy
    obtain ⟨-, -, -, -, -, hxm⟩ := hx
    obtain ⟨y1, -, ya, yb, -, -⟩ := hy
    have hy1 : mc tr (y - 1) 0 = 1 := (mp_kb H (r := y) (by omega) ya).1 (y - 1) (by omega)
    have ht : mc tr (y - 1) 2 = 0 := hxm (y - 1) (by omega) (by omega)
    have := (mp_next H (r := y - 1) (by omega) hy1 ht).2.1
    rw [show y - 1 + 1 = y by omega, yb] at this
    exact absurd this (by decide)
  rcases Nat.lt_trichotomy r0 r0' with l | e | l
  · exact (side _ _ ⟨a1, a2, a3, a4, a5, a6⟩ ⟨b1, b2, b3, b4, b5, b6⟩ l).elim
  · exact e
  · exact (side _ _ ⟨b1, b2, b3, b4, b5, b6⟩ ⟨a1, a2, a3, a4, a5, a6⟩ l).elim

/-- **A block in bytes.**  Under the chip hypothesis, a block `r0 … r` (`n = r − r0 + 1` rows) of
MPATH is a Merkle path of depth `D` (the public depth): the siblings and the old leaf are canonical,
the old root `ri` is (canonically) `pathRoot` of the old leaf, the new root `rt` that of the new leaf
(writable block) or `rt = ri` (read-only), `blk` is `natOf n bits` (the bits are its binary digits),
and `kb`, `ro` are the block's. -/
theorem mp_block_bytes {chip : List IfMsg} (hC : SegSha.ChipIf SegSha.compressW (wasmBaseSegAir nloc ngl) pub tr chip)
    {r0 r : Nat} (hB : MpBlock tr r0 r) {D : Nat} (hD : (pub.getD pubDepth 0).toNat = D) (hD1 : 1 ≤ D) :
    r - r0 + 1 = D ∧
    (∀ p ∈ mpL tr r0 D, Canon p.1 (bytesOf p.1)) ∧
    Canon (mdig tr r0 12) (bytesOf (mdig tr r0 12)) ∧
    Canon (mdig tr r 114) (pathRoot StateM5a.StateView.nodeH (bytesOf (mdig tr r0 12)) (bpath (mpL tr r0 D))) ∧
    (mc tr r0 4 = 0 → Canon (mdig tr r0 30) (bytesOf (mdig tr r0 30)) ∧
      Canon (mdig tr r 132) (pathRoot StateM5a.StateView.nodeH (bytesOf (mdig tr r0 30)) (bpath (mpL tr r0 D)))) ∧
    (mc tr r0 4 = 1 → mdig tr r 132 = mdig tr r 114) ∧
    mc tr r0 5 = ((natOf D (mpBits tr r0) : Nat) : F) ∧
    mc tr r 9 = mc tr r0 9 ∧ mc tr r 4 = mc tr r0 4 ∧ (mc tr r0 4 = 0 ∨ mc tr r0 4 = 1) := by
  obtain ⟨h1, hr, ha, hb, ht, hm⟩ := hB
  have hP := P_val
  have hh := H.heightLe 20 (by simp [seg_air_len]); unfold maxLogHeight at hh
  have e1 : r0 + (r - r0 + 1 - 1) = r := by omega
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := SegSha.mpath_block_sha H hC (r0 := r0) (n := r - r0 + 1) (by omega)
    (by omega) ha hb (fun l hl => hm (r0 + l) (by omega) (by omega)) (by rw [e1]; exact ht)
  rw [e1] at o1 o2 o3 o6 o7
  -- n = D
  have hn : r - r0 + 1 = D := by
    have e : pub.getD pubDepth 0 - 1 = ((D - 1 : Nat) : F) := by
      obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
      rw [← Fp.cast_toNat (pub.getD pubDepth 0), hD, Lean.Grind.Semiring.natCast_add,
        show D' + 1 - 1 = D' by omega]
      grind
    have := natEq (o5.trans e) (by omega) (by have := Fp.toNat_lt (pub.getD pubDepth 0); omega)
    omega
  rw [hn] at o1 o2 o4
  have hact := SegSha.mp_block_act H (r0 := r0) (n := D) (by omega) ha (fun l hl => hm (r0 + l) (by omega) (by omega))
  have hbit : ∀ l, l < D → mc tr (r0 + l) 3 = 0 ∨ mc tr (r0 + l) 3 = 1 :=
    fun l hl => (mp_bool H (r := r0 + l) (by omega)).2.2.2.1
  -- siblings and leaves are canonical
  have hsib : ∀ l, l < D → Canon (mdig tr (r0 + l) 48) (bytesOf (mdig tr (r0 + l) 48)) ∧
      Canon (mdig tr (r0 + l) 12) (bytesOf (mdig tr (r0 + l) 12)) := by
    intro l hl
    obtain ⟨dl, dr, -, l1, l2, -, w1, w2, -, e1, e2, -⟩ :=
      SegSha.mpath_row_old H hC (r := r0 + l) (by omega) (hact l hl).1
    rcases hbit l hl with b | b
    · obtain ⟨s1, s2⟩ := sel_eq.1 b
      exact ⟨canon_of l2 w2 (s2.symm.trans e2), canon_of l1 w1 (s1.symm.trans e1)⟩
    · obtain ⟨s1, s2⟩ := sel_eq.2 b
      exact ⟨canon_of l1 w1 (s1.symm.trans e1), canon_of l2 w2 (s2.symm.trans e2)⟩
  have hL : ∀ p ∈ mpL tr r0 D, Canon p.1 (bytesOf p.1) := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hp
    exact (hsib l (List.mem_range.mp hl)).1
  have hco : Canon (mdig tr r0 12) (bytesOf (mdig tr r0 12)) := by
    have := (hsib 0 (by omega)).2; simpa using this
  refine ⟨hn, hL, hco, ?_, fun h0 => ?_, o3, ?_, o6, o7, (mp_bool H (r := r0) (by omega)).2.2.2.2⟩
  · rw [o1]; exact mfold_canon _ _ _ hco hL
  · have hcn : Canon (mdig tr r0 30) (bytesOf (mdig tr r0 30)) := by
      obtain ⟨dl, dr, -, l1, l2, -, w1, w2, -, e1, e2, -⟩ :=
        SegSha.mpath_row_new H hC (r := r0) (by omega) ha h0
      rcases hbit 0 (by omega) with b | b
      · have := (sel_eq (base := 30)).1 (by simpa using b)
        exact canon_of l1 w1 (this.1.symm.trans e1)
      · have := (sel_eq (base := 30)).2 (by simpa using b)
        exact canon_of l2 w2 (this.2.symm.trans e2)
    exact ⟨hcn, by rw [o2 h0]; exact mfold_canon _ _ _ hcn hL⟩
  · rw [o4]
    exact bitsum_natOf D (fun l => mc tr (r0 + l) 3) hbit

end blocks

end MemRoot

end WasmBase

#print axioms WasmBase.MemRoot.write_access_pd
#print axioms WasmBase.MemRoot.mfold_canon
#print axioms WasmBase.MemRoot.mp_block_bytes
#print axioms WasmBase.MemRoot.mp_block_unique
#print axioms WasmBase.MemRoot.mp_block_of_bot
#print axioms WasmBase.MemRoot.sidesOk_natOf
