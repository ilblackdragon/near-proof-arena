import StateM5a.TmplWsx
import StateM5a.TmplView
import StateM5a.StateViewParams

/-!
# StateM5a.WsBridge — B-T2: the circuit's working-set tree is the state view's (`Dig` ↔ bytes)

The working-set theorems of the templates (`TmplSeg.m5tSeg_ws`, `TmplWsx.seg_rin_rout`) are stated
over the circuit's digests `Sha512If.Dig` (6 words `< 2^64`) and an abstract compression
`compress : List Nat → List Nat → List Nat` on 16-word blocks; the state view (`StateView.wsRoot`,
the `ws` field of `stD`) is over 48-byte strings with `nodeH l r = sha384 (l ‖ r)` and the leaf
digest `cmp384`. This file closes that gap (B-T1b item 3, "missing: the bridge"):

* **`cW`** — the real compression on a word block (`SHA512.compress h (wbytes b)`), `cW_ok`
  (`CompressOK cW`, no assumption);
* **`toB`** — a digest's 48 big-endian bytes; `toB_inj` (injective on `Dig`);
* **`toB_nodeH`** — `toB (Sha512If.nodeH cW a b) = StateView.nodeH (toB a) (toB b)`: one
  compression of `a ‖ b ‖ padW` from `IV384` is SHA-384 of the 96 bytes (FIPS 180-4 padding);
* **`toB_leaf`** — the circuit's leaf digest of a block is the view's `cmp384`;
* `root_map`, `zd_map`, `extUp_map`, `extUp_shift` (generic Merkle facts);
* **`wsRoot_dig`** — the view's depth-24 working-set root of an entry list is `toB` of the circuit's
  depth-`D` root of its leaf digests extended by `24 − D` zero levels;
* **`ws_moves_seg`** — **the segment template moves the view's root**: from `Holds` of `m5tSeg`
  (with the chip contract and `NodeCR cW`, the same premises as `seg_rin_rout`), for every entry
  list `es` whose view root is the public `R_in` (as bytes), the view root of `upd es` is the
  public `R_out` — given **`SegLeaves`**, the leaf-level content of the segment (each touched
  leaf's new digest is the leaf digest of `upd es`'s entry). `SegLeaves` is the per-template
  restatement of M5b's `StSound.write_sent` / `WsSeg.ws_final` / `StSoundF.final_val` (requests →
  `WRITE` → `WSA` memory chain → `WSL` leaf), **named, open**.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace StateM5a.WsBridge

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.Sha512If
open StateM5a.WsDecode StateM5a.WsDecode2 StateM5a.WsDecode3 StateM5a.WsBus StateM5a.WsRaw StateM5a.Merkle
open StateM5a.TmplSeg StateM5a.TmplWsx NearSpecV3
open StateM5a.StateView (wbytes cmp384 zero48 Entry leafOf StViewParams wsRoot leafD)
open ArenaCore.Bytes (beN beN_length beToNat beToNat_beN)

abbrev Bytes := ArenaCore.Bytes

/-! ## The real compression and the byte form of a digest -/

/-- The real SHA-512 compression on a block given as 16 words. -/
def cW (h b : List Nat) : List Nat := SHA512.compress h (wbytes b)

theorem add64_lt (a b : Nat) : SHA512.add64 a b < 2 ^ 64 := Nat.mod_lt _ (by decide)

theorem compress_w64 (h b : List Nat) : W64 (SHA512.compress h b) := by
  intro w hw
  simp only [SHA512.compress, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact add64_lt _ _

theorem cW_ok : CompressOK cW := fun h b => ⟨rfl, compress_w64 h _⟩

/-- A digest's 48 big-endian bytes. -/
def toB (d : Dig) : Bytes := d.1.flatMap (beN 8)

theorem flatMap_beN_length : ∀ l : List Nat, (l.flatMap (beN 8)).length = 8 * l.length
  | [] => rfl
  | x :: r => by simp [List.flatMap_cons, beN_length, flatMap_beN_length r]; omega

theorem toB_length (d : Dig) : (toB d).length = 48 := by
  rw [toB, flatMap_beN_length, d.2.1]

theorem flatMap_beN_inj : ∀ l l' : List Nat, (∀ w ∈ l, w < 2 ^ 64) → (∀ w ∈ l', w < 2 ^ 64) →
    l.flatMap (beN 8) = l'.flatMap (beN 8) → l = l'
  | [], [], _, _, _ => rfl
  | [], y :: r, _, _, h => by
    have := congrArg List.length h; simp [List.flatMap_cons, beN_length] at this <;> omega
  | x :: r, [], _, _, h => by
    have := congrArg List.length h; simp [List.flatMap_cons, beN_length] at this <;> omega
  | x :: r, y :: r', hl, hl', h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp [beN_length])
    have e := congrArg beToNat h1
    rw [beToNat_beN, beToNat_beN, Nat.mod_eq_of_lt (by have := hl x (by simp); simpa using this),
      Nat.mod_eq_of_lt (by have := hl' y (by simp); simpa using this)] at e
    rw [e, flatMap_beN_inj r r' (fun w hw => hl w (by simp [hw])) (fun w hw => hl' w (by simp [hw])) h2]

theorem toB_inj {a b : Dig} (h : toB a = toB b) : a = b :=
  Subtype.ext (flatMap_beN_inj _ _ a.2.2 b.2.2 h)

theorem map_toB (d : Dig) : (toB d).map UInt8.toNat = wbytes d.1 := by
  simp [toB, wbytes, List.map_flatMap]

/-- The all-zero digest (an unused leaf). -/
def z0 : Dig := ⟨List.replicate 6 0, by simp, by intro w hw; simp at hw; omega⟩

theorem toB_z0 : toB z0 = zero48 := by decide

/-! ## The digest of one compression -/

theorem take_flatMap8 : ∀ (n : Nat) (l : List Nat),
    (l.flatMap (beN 8)).take (8 * n) = (l.take n).flatMap (beN 8)
  | 0, l => by simp
  | n + 1, [] => by simp
  | n + 1, x :: r => by
    rw [List.flatMap_cons, show 8 * (n + 1) = 8 + 8 * n by omega, List.take_append,
      List.take_of_length_le (by simp [beN_length])]
    simp [beN_length, take_flatMap8 n r]

theorem digest6_take (x : List Nat) (hl : x.length = 8) (hw : W64 x) : (digest6 x).1 = x.take 6 := by
  match x, hl with
  | [a, b, c, d, e, f, g, i], _ =>
    have h1 := hw a (by simp); have h2 := hw b (by simp); have h3 := hw c (by simp)
    have h4 := hw d (by simp); have h5 := hw e (by simp); have h6 := hw f (by simp)
    simp [digest6, List.range_succ, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3,
      Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h5, Nat.mod_eq_of_lt h6]

theorem toB_digest6 (h b : List Nat) :
    toB (digest6 (SHA512.compress h b)) = (SHA512.digestBytes (SHA512.compress h b)).take 48 := by
  rw [SHA512.digestBytes, show (48 : Nat) = 8 * 6 from rfl, take_flatMap8, toB,
    digest6_take _ rfl (compress_w64 h b)]

/-- **The circuit's leaf digest is the view's `cmp384`.** -/
theorem toB_leaf (blk : List Nat) : toB (digest6 (cW NearSpecV3.E2E.Bnd.IV384 blk)) = cmp384 blk := by
  rw [cW, toB_digest6]; rfl

/-! ## The node hash -/

theorem wbytes_append (a b : List Nat) : wbytes (a ++ b) = wbytes a ++ wbytes b := by
  simp [wbytes, List.flatMap_append]

theorem wbytes_length (a : List Nat) : (wbytes a).length = 8 * a.length := by
  induction a with
  | nil => rfl
  | cons x r ih => simp only [wbytes, List.flatMap_cons, List.length_append, List.length_map,
      beN_length] at ih ⊢; rw [ih]; simp; omega

/-- SHA-384's padding of a 96-byte message is `wbytes padW`. -/
theorem pad96 (m : List Nat) (hm : m.length = 96) : SHA512.pad m = m ++ wbytes padW := by
  simp only [SHA512.pad, hm, List.append_assoc]
  congr 1

theorem blocks_one (h msg : List Nat) (hl : msg.length = 128) :
    SHA512.blocks 1 h msg = SHA512.compress h msg := by
  match msg, hl with
  | x :: r, hl => simp [SHA512.blocks, List.take_of_length_le (show (x :: r).length ≤ 128 by omega)]

/-- **The node bridge**: the circuit's node hash (one compression of `a ‖ b ‖ padW` from `IV384`)
is SHA-384 of the two digests' 96 bytes. -/
theorem toB_nodeH (a b : Dig) : toB (Sha512If.nodeH cW a b) = StateView.nodeH (toB a) (toB b) := by
  have hm : ((toB a ++ toB b).map UInt8.toNat) = wbytes a.1 ++ wbytes b.1 := by
    rw [List.map_append, map_toB, map_toB]
  have hl : (wbytes a.1 ++ wbytes b.1).length = 96 := by
    rw [List.length_append, wbytes_length, wbytes_length, a.2.1, b.2.1]
  have hp : SHA512.pad ((toB a ++ toB b).map UInt8.toNat) = wbytes (a.1 ++ b.1 ++ padW) := by
    rw [hm, pad96 _ hl, wbytes_append, wbytes_append]
  have hpl : (wbytes (a.1 ++ b.1 ++ padW)).length = 128 := by
    rw [wbytes_length]; simp [a.2.1, b.2.1, padW]
  simp only [StateView.nodeH, NearSpecV3.E2E.Bnd.sha384, hp, hpl, Nat.reduceDiv, blocks_one _ _ hpl]
  rw [Sha512If.nodeH, ← toB_digest6]; rfl

/-! ## Generic Merkle facts -/

section Generic
variable {α β : Type} (H : α → α → α) (G : β → β → β) (f : α → β)

theorem up_map (hf : ∀ a b, f (H a b) = G (f a) (f b)) : ∀ l : List α, up G (l.map f) = (up H l).map f
  | [] => rfl
  | [_] => rfl
  | a :: b :: r => by simp only [List.map_cons, up, hf, up_map hf r]

theorem root_map (hf : ∀ a b, f (H a b) = G (f a) (f b)) :
    ∀ (D : Nat) (l : List α), root G D (l.map f) = (root H D l).map f
  | 0, [] => rfl
  | 0, [_] => rfl
  | 0, _ :: _ :: _ => rfl
  | D + 1, l => by simp only [root, up_map H G f hf, root_map hf D]

theorem zd_map (hf : ∀ a b, f (H a b) = G (f a) (f b)) (z : α) :
    ∀ d, zd G (f z) d = f (zd H z d)
  | 0 => rfl
  | d + 1 => by simp only [zd, zd_map hf z d, hf]

theorem extUp_map (hf : ∀ a b, f (H a b) = G (f a) (f b)) (z : α) (D : Nat) :
    ∀ (k : Nat) (x : α), extUp G (f z) D k (f x) = f (extUp H z D k x)
  | 0, _ => rfl
  | k + 1, x => by simp only [extUp, extUp_map hf z D k x, zd_map H G f hf z, hf]

theorem zd_add (z : α) (D : Nat) : ∀ k, zd H (zd H z D) k = zd H z (D + k)
  | 0 => rfl
  | k + 1 => by simp only [zd, zd_add z D k]; rfl

theorem extUp_shift (z : α) (D : Nat) : ∀ (k : Nat) (x : α),
    extUp H (zd H z D) 0 k x = extUp H z D k x
  | 0, _ => rfl
  | k + 1, x => by simp only [extUp, extUp_shift z D k x, Nat.zero_add, zd_add]

theorem root_some_of_map (hf : ∀ a b, f (H a b) = G (f a) (f b)) (D : Nat) (l : List α) {y : β}
    (h : root G D (l.map f) = some y) : ∃ x, root H D l = some x ∧ f x = y := by
  rw [root_map H G f hf] at h
  cases e : root H D l with
  | none => rw [e] at h; cases h
  | some x => rw [e] at h; exact ⟨x, rfl, Option.some.inj h⟩

end Generic

/-! ## The view's root through the circuit's tree -/

variable (P : StViewParams)

/-- The circuit's leaf digest of an entry. -/
def leafDig (e : Entry) : Dig := digest6 (cW NearSpecV3.E2E.Bnd.IV384 (P.leafBlock (leafOf e)))

/-- The circuit's `2^D` leaf digests of an entry list (zero-padded). -/
def leavesDig (D : Nat) (es : List Entry) : List Dig :=
  es.map (leafDig P) ++ List.replicate (2 ^ D - es.length) z0

theorem leavesDig_length (D : Nat) (es : List Entry) (h : es.length ≤ 2 ^ D) :
    (leavesDig P D es).length = 2 ^ D := by
  simp only [leavesDig, List.length_append, List.length_map, List.length_replicate]; omega

theorem leavesDig_toB (D : Nat) (es : List Entry) :
    (leavesDig P D es).map toB = TmplView.leavesD P D es := by
  simp only [leavesDig, TmplView.leavesD, List.map_append, List.map_map, List.map_replicate, toB_z0]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [Function.comp, leafDig, toB_leaf, leafD]

theorem hnode (a b : Dig) : toB (Sha512If.nodeH cW a b) = StateView.nodeH (toB a) (toB b) := toB_nodeH a b

/-- **The view's working-set root through the circuit's tree.** -/
theorem wsRoot_dig (D : Nat) (hD : D ≤ P.depth) (es : List Entry) (h : es.length ≤ 2 ^ D) :
    ∃ r, root (Sha512If.nodeH cW) D (leavesDig P D es) = some r ∧
      wsRoot P es = toB (extUp (Sha512If.nodeH cW) z0 D (P.depth - D) r) := by
  have e := TmplView.wsRoot_ext P D hD es h
  rw [← leavesDig_toB, root_map _ _ toB hnode] at e
  obtain ⟨x, hx⟩ := StateView.root_some D (TmplView.leavesD P D es) (TmplView.leavesD_length P D es h)
  rw [← leavesDig_toB, root_map _ _ toB hnode] at hx
  cases e2 : root (Sha512If.nodeH cW) D (leavesDig P D es) with
  | none => rw [e2] at hx; cases hx
  | some r =>
    refine ⟨r, rfl, ?_⟩
    rw [e, e2]
    simp only [Option.map_some, Option.getD_some]
    rw [← toB_z0, extUp_map _ _ toB hnode]

/-! ## The segment template moves the view's root -/

/-- **The view's working-set step**: every entry list with `n` entries whose view root is `RIn`
becomes, under `upd`, one whose view root is `ROut`. -/
def WsMoves (n : Nat) (RIn ROut : Bytes) (upd : List Entry → List Entry) : Prop :=
  ∀ es : List Entry, es.length = n → (∀ e ∈ es, e.Ok) → wsRoot P es = RIn → wsRoot P (upd es) = ROut

section Seg
variable {D : Nat} {extra : List Table} {nb np : Nat} {tr : Trace Fp} {pub : List Fp}

/-- **The segment's leaf content** (named premise, open): on the leaves of an entry list with
`wsLen` entries, the segment's touched-leaf replacement (`WsSeg.wsAt`, every touched leaf ↦ its
`WSL` row's new digest) gives the leaves of `upd es`. The per-template restatement of M5b's
`write_sent` (a `WRITE` is a request's key / value hashes), `ws_final` (each closing value is the
latest write) and `final_val` (a `WSL` leaf digest is the compression of its row's leaf block). -/
def SegLeaves (D : Nat) (tr : Trace Fp) (pub : List Fp) (upd : List Entry → List Entry) : Prop :=
  ∀ es : List Entry, es.length = WsLen.wsLen pub → (∀ e ∈ es, e.Ok) →
    WsSeg.wsAt (wsl (trS tr) pub) (leavesDig P D es) (ev tr 7 0 pub (Wsx.c "sb")) = leavesDig P D (upd es)

/-- **The segment template moves the view's root** `R_in → R_out` (public values, as bytes). -/
theorem ws_moves_seg (hH : Holds (segAir D extra nb np) pub tr)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_WM ∧ i.bus ≠ B_PT ∧ i.bus ≠ B_RCH ∧
      i.bus ≠ B_RNG)
    (hC : Sha512IfContract cW ((busList (segAir D extra nb np) tr pub B_IF384 true).map decIf))
    (hD1 : 1 ≤ D) (hD : D ≤ 20) (hCR : NodeCR cW) (hdep : P.depth = 24)
    (hz : toB (zD D) = zd StateView.nodeH zero48 D) (hn : WsLen.wsLen pub ≤ 2 ^ D)
    {upd : List Entry → List Entry} (hupd : ∀ es, (upd es).length = es.length)
    (hSL : SegLeaves P D tr pub upd) :
    WsMoves P (WsLen.wsLen pub) (toB (pubDig pub PUB_WSA)) (toB (pubDig pub PUB_WSB)) upd := by
  intro es hlen hok hroot
  have hle : es.length ≤ 2 ^ D := hlen ▸ hn
  have hDd : D ≤ P.depth := by omega
  obtain ⟨r, hr, he⟩ := wsRoot_dig P D hDd es hle
  have hzD : zD D = zd (Sha512If.nodeH cW) z0 D := by
    apply toB_inj; rw [hz, ← zd_map _ _ toB hnode, toB_z0]
  have hin : extUp (Sha512If.nodeH cW) (zD D) 0 (24 - D) r = pubDig pub PUB_WSA := by
    apply toB_inj
    rw [hzD, extUp_shift, ← hroot, he, hdep]
  obtain ⟨r', hr', hout⟩ := seg_rin_rout hH hx cW_ok hC hD1 hD hCR
    (leavesDig_length P D es hle) hr hin
  rw [hSL es hlen hok] at hr'
  have hle' : (upd es).length ≤ 2 ^ D := by rw [hupd]; exact hle
  obtain ⟨r'', hr'', he'⟩ := wsRoot_dig P D hDd (upd es) hle'
  rw [hr''] at hr'
  cases hr'
  rw [he', ← hout, hzD, extUp_shift, hdep]

end Seg

#print axioms toB_nodeH
#print axioms toB_leaf
#print axioms wsRoot_dig
#print axioms ws_moves_seg

end StateM5a.WsBridge
