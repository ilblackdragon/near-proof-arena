import NearSpecV3.E2E.View

/-!
# E2E-M11f: an injective serialisation of the state component `StV` (lane B's `encE`)

Lane B's `StateM5a.StateViewParams.StViewE` asks lane E for an encoder `encE : StV → Bytes`
that is injective on stripped components (`StV` with the overlay blanked). This file gives a
**prefix-free serialiser of every `StV`** (`encStV`, `encStV_pf`) and its injectivity
`encStV_inj : encStV a = encStV b → a = b` for all `a b`, which implies lane B's `encE_inj` with no
hypothesis on `strip`.

## The encoding

A type class `Ser α` (an encoder `enc : α → Bytes` with `PF enc`: an encoding followed by anything
determines the value and the rest). Instances:

* base: `Nat` (unsigned LEB128, `vnat`), `UInt8` (one byte), `Bool`, `Unit` (empty), `Char` (its
  code point), `String` (its characters), `ByteArray` (its bytes);
* combinators: pairs (concatenation), `Option` (`0` / `1 ‖ value`), `List` (`1 ‖ item` per
  element, then `0`), `Sum` (`0 ‖ left` / `1 ‖ right`), and `Ser.ofInj` (through an injective map);
* `Std.TreeMap` (the recorder's key sets `TTN.BMap Unit`): the **tree itself** — `0` for a leaf,
  `1 ‖ size ‖ key ‖ value ‖ left ‖ right` for an inner node. Two maps with the same contents but
  different balancing are different values of `TreeMap`, so the tree shape must be encoded; the
  well-formedness proof is a `Prop` (proof irrelevance);
* `PTrie`/`Kids` (mutual, as in lane B's `tEnc`), and every spec record of the closure of `StV`
  (computed by a meta-script: 43 types, listed below) through `Ser.ofInj`: a structure maps to the
  tuple of its fields, an inductive to a nested `Sum` of its constructors' field tuples; the maps
  are injective by `cases` (`inj_tac`).

The closure: `StV`, `EngSt`, `EPos`, `Recording` (`TTN.Recorder`, `TTN.Acct`, `Pipeline.Pipe`,
`Pipeline.Task`, `ObsDetail`), `RS` (`Ovl`, `PTrie`, `Kids`, `Slot`, `Limit`, `Meta`,
`Congestion`, `DQ`, `OutD1`, `Outcome`, `OStatus`, `Proposal`, `PublicKey`), `Rcpt` (`RBody`,
`ActionR`, `Act`, `BaseAct`, `Base`, `Delegate`, `AK`, `Perm`, `FcPerm`, `Distribution`, `Gci`,
`GcdMode`, `DeployGlobal`, `UseGlobal`, `Dsi`, `StateInit`), `TxD2`, `MainOutD2` (`BwRequest`).

The serialiser is computable. It is not a protocol format: its only use is the state commitment's
remainder digest (`StateView.commitOf.rest`) and raw form, where only injectivity matters.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace NearSpecV3.E2E.Enc
open NearSpec NearSpecV3 NearSpecV3.D2 NearSpecV3.E2E NearSpecV3.E2E.Bnd
open NearSpecV3.Successor NearSpecV3.Successor.StorageExecution

/-! ## Prefix-free encoders -/

/-- A prefix-free (hence injective) encoder. -/
def PF {α : Type} (f : α → Bytes) : Prop :=
  ∀ a b (r r' : Bytes), f a ++ r = f b ++ r' → a = b ∧ r = r'

theorem PF.inj {α : Type} {f : α → Bytes} (h : PF f) {a b : α} (e : f a = f b) : a = b :=
  (h a b [] [] (by simpa using e)).1

/-- A prefix-free serialiser. -/
class Ser (α : Type) where
  enc : α → Bytes
  pf : PF enc

/-- A serialiser through an injective map. -/
@[instance_reducible] def Ser.ofInj {α β : Type} [Ser β] (g : α → β) (hg : ∀ a b, g a = g b → a = b) : Ser α where
  enc a := Ser.enc (g a)
  pf a b r r' h := by
    obtain ⟨e, hr⟩ := Ser.pf _ _ _ _ h
    exact ⟨hg _ _ e, hr⟩

theorem u8_toNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by
  simp

/-- Unsigned LEB128: 7 bits per byte, high bit = continuation. -/
def vnat (n : Nat) : Bytes :=
  if n < 128 then [UInt8.ofNat n] else UInt8.ofNat (128 + n % 128) :: vnat (n / 128)
termination_by n
decreasing_by omega

theorem vnat_eq (n : Nat) : vnat n =
    if n < 128 then [UInt8.ofNat n] else UInt8.ofNat (128 + n % 128) :: vnat (n / 128) := by
  rw [vnat]

theorem vnat_pf : PF vnat := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro m r r' h
    rw [vnat_eq n, vnat_eq m] at h
    by_cases hn : n < 128 <;> by_cases hm : m < 128 <;>
      simp only [hn, hm, ite_true, ite_false, List.cons_append, List.nil_append,
        List.cons.injEq] at h
    · have := congrArg UInt8.toNat h.1
      rw [u8_toNat, u8_toNat] at this
      exact ⟨by omega, h.2⟩
    · have := congrArg UInt8.toNat h.1
      rw [u8_toNat, u8_toNat] at this
      omega
    · have := congrArg UInt8.toNat h.1
      rw [u8_toNat, u8_toNat] at this
      omega
    · have h1 := congrArg UInt8.toNat h.1
      rw [u8_toNat, u8_toNat] at h1
      obtain ⟨e, hr⟩ := ih (n / 128) (by omega) (m / 128) r r' h.2
      exact ⟨by omega, hr⟩

instance : Ser Nat := ⟨vnat, vnat_pf⟩

instance : Ser UInt8 where
  enc b := [b]
  pf a b r r' h := by simpa using h

instance : Ser Unit where
  enc _ := []
  pf _ _ r r' h := ⟨rfl, by simpa using h⟩

instance {α β : Type} [Ser α] [Ser β] : Ser (α × β) where
  enc p := Ser.enc p.1 ++ Ser.enc p.2
  pf := by
    intro ⟨a, b⟩ ⟨a', b'⟩ r r' h
    simp only [List.append_assoc] at h
    obtain ⟨rfl, h1⟩ := Ser.pf _ _ _ _ h
    obtain ⟨rfl, rfl⟩ := Ser.pf _ _ _ _ h1
    exact ⟨rfl, rfl⟩

instance {α : Type} [Ser α] : Ser (Option α) where
  enc | none => [0] | some a => 1 :: Ser.enc a
  pf := by
    intro a b r r' h
    cases a <;> cases b <;> simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    · exact ⟨rfl, h.2⟩
    · simp at h
    · simp at h
    · obtain ⟨rfl, h1⟩ := Ser.pf _ _ _ _ h.2
      exact ⟨rfl, h1⟩

instance {α β : Type} [Ser α] [Ser β] : Ser (α ⊕ β) where
  enc | .inl a => 0 :: Ser.enc a | .inr b => 1 :: Ser.enc b
  pf := by
    intro a b r r' h
    cases a <;> cases b <;> simp only [List.cons_append, List.cons.injEq] at h
    · obtain ⟨rfl, h1⟩ := Ser.pf _ _ _ _ h.2
      exact ⟨rfl, h1⟩
    · simp at h
    · simp at h
    · obtain ⟨rfl, h1⟩ := Ser.pf _ _ _ _ h.2
      exact ⟨rfl, h1⟩

/-- A list: `1 ‖ item` per element, then `0`. -/
def listEnc {α : Type} [Ser α] : List α → Bytes
  | [] => [0]
  | a :: l => 1 :: (Ser.enc a ++ listEnc l)

theorem listEnc_pf {α : Type} [Ser α] : PF (listEnc (α := α)) := by
  intro l
  induction l with
  | nil =>
    intro l' r r' h
    cases l' with
    | nil => exact ⟨rfl, by simpa [listEnc] using h⟩
    | cons => simp [listEnc] at h
  | cons a l ih =>
    intro l' r r' h
    cases l' with
    | nil => simp [listEnc] at h
    | cons a' l' =>
      simp only [listEnc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨rfl, h1⟩ := Ser.pf _ _ _ _ h
      obtain ⟨rfl, rfl⟩ := ih _ _ _ h1
      exact ⟨rfl, rfl⟩

instance {α : Type} [Ser α] : Ser (List α) := ⟨listEnc, listEnc_pf⟩

/-- Injectivity of a map to a tuple / nested sum, by cases. -/
macro "inj_tac" : tactic => `(tactic| (intro a b h; cases a <;> cases b <;> simp_all))

instance : Ser Bool := Ser.ofInj (fun b : Bool => if b then (1 : Nat) else 0) (by inj_tac)

instance : Ser Char := Ser.ofInj (fun c : Char => c.val.toNat)
  (fun a b h => Char.ext (UInt32.toNat_inj.mp h))

instance : Ser String := Ser.ofInj String.toList (fun _ _ h => String.ext h)

instance : Ser ByteArray := Ser.ofInj (fun b : ByteArray => b.data.toList)
  (fun _ _ h => ByteArray.ext (Array.toList_inj.mp h))

/-! ## Tree maps: the tree itself -/

section Tree
open Std.DTreeMap.Internal

variable {α β : Type} [Ser α] [Ser β]

/-- A balanced tree, node by node (size, key, value, children). -/
def implEnc : Impl α (fun _ => β) → Bytes
  | .leaf => [0]
  | .inner s k v l r => 1 :: (Ser.enc s ++ Ser.enc k ++ Ser.enc v ++ implEnc l ++ implEnc r)

theorem implEnc_pf : PF (implEnc (α := α) (β := β)) := by
  intro t
  induction t with
  | leaf =>
    intro t' r r' h
    cases t' with
    | leaf => exact ⟨rfl, by simpa [implEnc] using h⟩
    | inner => simp [implEnc] at h
  | inner s k v l rt ihl ihr =>
    intro t' r r' h
    cases t' with
    | leaf => simp [implEnc] at h
    | inner s' k' v' l' rt' =>
      simp only [implEnc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨rfl, h1⟩ := Ser.pf _ _ _ _ h
      obtain ⟨rfl, h2⟩ := Ser.pf _ _ _ _ h1
      obtain ⟨rfl, h3⟩ := Ser.pf _ _ _ _ h2
      obtain ⟨rfl, h4⟩ := ihl _ _ _ h3
      obtain ⟨rfl, rfl⟩ := ihr _ _ _ h4
      exact ⟨rfl, rfl⟩

instance : Ser (Impl α (fun _ => β)) := ⟨implEnc, implEnc_pf⟩

instance {cmp : α → α → Ordering} : Ser (Std.DTreeMap α (fun _ => β) cmp) :=
  Ser.ofInj (fun m => m.inner) (by
    intro a b h
    cases a; cases b
    simp only at h
    subst h
    rfl)

instance {cmp : α → α → Ordering} : Ser (Std.TreeMap α β cmp) :=
  Ser.ofInj (fun m => m.inner) (by
    intro a b h
    cases a; cases b
    simp only at h
    subst h
    rfl)

end Tree

/-! ## Partial tries -/

instance : Ser Slot := Ser.ofInj
  (fun | .val v => (.inl v : Bytes ⊕ (Nat × Bytes)) | .ref l h => .inr (l, h)) (by inj_tac)

mutual
/-- Every constructor, key nibble, memory count, hash and value of a partial trie. -/
def tEnc : PTrie → Bytes
  | .hash h => 0 :: Ser.enc h
  | .leaf k s m => 1 :: (Ser.enc k ++ Ser.enc s ++ Ser.enc m)
  | .ext k c m => 2 :: (Ser.enc k ++ tEnc c ++ Ser.enc m)
  | .branch v cs m => 3 :: (Ser.enc v ++ kEnc cs ++ Ser.enc m)
def kEnc : Kids → Bytes
  | .nil => [0]
  | .none r => 1 :: kEnc r
  | .some c r => 2 :: (tEnc c ++ kEnc r)
end

mutual
theorem tEnc_pf : ∀ (t t' : PTrie) (r r' : Bytes), tEnc t ++ r = tEnc t' ++ r' → t = t' ∧ r = r'
  | .hash h, .hash h', r, r', e => by
    simp only [tEnc, List.cons_append, List.cons.injEq, true_and] at e
    obtain ⟨rfl, e1⟩ := Ser.pf _ _ _ _ e
    exact ⟨rfl, e1⟩
  | .leaf k s m, .leaf k' s' m', r, r', e => by
    simp only [tEnc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at e
    obtain ⟨rfl, e1⟩ := Ser.pf _ _ _ _ e
    obtain ⟨rfl, e2⟩ := Ser.pf _ _ _ _ e1
    obtain ⟨rfl, e3⟩ := Ser.pf _ _ _ _ e2
    exact ⟨rfl, e3⟩
  | .ext k c m, .ext k' c' m', r, r', e => by
    simp only [tEnc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at e
    obtain ⟨rfl, e1⟩ := Ser.pf _ _ _ _ e
    obtain ⟨rfl, e2⟩ := tEnc_pf c c' _ _ e1
    obtain ⟨rfl, e3⟩ := Ser.pf _ _ _ _ e2
    exact ⟨rfl, e3⟩
  | .branch v cs m, .branch v' cs' m', r, r', e => by
    simp only [tEnc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at e
    obtain ⟨rfl, e1⟩ := Ser.pf _ _ _ _ e
    obtain ⟨rfl, e2⟩ := kEnc_pf cs cs' _ _ e1
    obtain ⟨rfl, e3⟩ := Ser.pf _ _ _ _ e2
    exact ⟨rfl, e3⟩
  | .hash _, .leaf .., _, _, e | .hash _, .ext .., _, _, e | .hash _, .branch .., _, _, e
  | .leaf .., .hash _, _, _, e | .leaf .., .ext .., _, _, e | .leaf .., .branch .., _, _, e
  | .ext .., .hash _, _, _, e | .ext .., .leaf .., _, _, e | .ext .., .branch .., _, _, e
  | .branch .., .hash _, _, _, e | .branch .., .leaf .., _, _, e
  | .branch .., .ext .., _, _, e => by simp [tEnc] at e
theorem kEnc_pf : ∀ (cs cs' : Kids) (r r' : Bytes), kEnc cs ++ r = kEnc cs' ++ r' →
    cs = cs' ∧ r = r'
  | .nil, .nil, r, r', e => by simpa [kEnc] using e
  | .none c, .none c', r, r', e => by
    simp only [kEnc, List.cons_append, List.cons.injEq, true_and] at e
    obtain ⟨rfl, e1⟩ := kEnc_pf c c' _ _ e
    exact ⟨rfl, e1⟩
  | .some c cs, .some c' cs', r, r', e => by
    simp only [kEnc, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at e
    obtain ⟨rfl, e1⟩ := tEnc_pf c c' _ _ e
    obtain ⟨rfl, e2⟩ := kEnc_pf cs cs' _ _ e1
    exact ⟨rfl, e2⟩
  | .nil, .none _, _, _, e | .nil, .some .., _, _, e | .none _, .nil, _, _, e
  | .none _, .some .., _, _, e | .some .., .nil, _, _, e | .some .., .none _, _, _, e => by
    simp [kEnc] at e
end

instance : Ser PTrie := ⟨tEnc, tEnc_pf⟩

/-! ## The spec records -/

instance : Ser PublicKey := Ser.ofInj (fun (x : PublicKey) => (x.1, x.2)) (by inj_tac)
instance : Ser Outcome := Ser.ofInj (fun (x : Outcome) => (x.1, x.2, x.3, x.4, x.5)) (by inj_tac)
instance : Ser OStatus := Ser.ofInj
  (fun | .value => (.inl () : Unit ⊕ Bytes ⊕ Unit ⊕ Bytes) | .receipt b => .inr (.inl b)
       | .failure => .inr (.inr (.inl ())) | .valueBytes b => .inr (.inr (.inr b))) (by inj_tac)
instance : Ser OutD1 := Ser.ofInj (fun (x : OutD1) => (x.1, x.2, x.3)) (by inj_tac)
instance : Ser Limit := Ser.ofInj (fun (x : Limit) => (x.1, x.2, x.3)) (by inj_tac)
instance : Ser Congestion := Ser.ofInj (fun (x : Congestion) => (x.1, x.2, x.3, x.4)) (by inj_tac)
instance : Ser BwRequest := Ser.ofInj (fun (x : BwRequest) => (x.1, x.2)) (by inj_tac)
instance : Ser Meta := Ser.ofInj (fun (x : Meta) => (x.1, x.2, x.3, x.4, x.5)) (by inj_tac)
instance : Ser DQ := Ser.ofInj (fun (x : DQ) => (x.1, x.2, x.3, x.4, x.5, x.6)) (by inj_tac)
instance : Ser Proposal := Ser.ofInj (fun (x : Proposal) => (x.1, x.2, x.3)) (by inj_tac)
instance : Ser Ovl := Ser.ofInj (fun (x : Ovl) => (x.1, x.2, x.3, x.4)) (by inj_tac)

section L4
open NearSpecV3.D3.L4
instance : Ser Gci := Ser.ofInj
  (fun | .codeHash b => (.inl b : Bytes ⊕ Bytes) | .accountId b => .inr b) (by inj_tac)
instance : Ser GcdMode := Ser.ofInj
  (fun | .codeHash => (.inl () : Unit ⊕ Unit) | .accountId => .inr ()) (by inj_tac)
instance : Ser DeployGlobal := Ser.ofInj (fun (x : DeployGlobal) => (x.1, x.2)) (by inj_tac)
instance : Ser UseGlobal := Ser.ofInj (fun (x : UseGlobal) => x.1) (by inj_tac)
instance : Ser StateInit := Ser.ofInj (fun (x : StateInit) => (x.1, x.2)) (by inj_tac)
instance : Ser Dsi := Ser.ofInj (fun (x : Dsi) => (x.1, x.2)) (by inj_tac)
end L4

instance : Ser FcPerm := Ser.ofInj (fun (x : FcPerm) => (x.1, x.2, x.3)) (by inj_tac)
instance : Ser D2.Perm := Ser.ofInj
  (fun | .fc f => (.inl f : FcPerm ⊕ Unit ⊕ (Nat × Nat × FcPerm) ⊕ (Nat × Nat))
       | .full => .inr (.inl ()) | .gasFc a b f => .inr (.inr (.inl (a, b, f)))
       | .gasFull a b => .inr (.inr (.inr (a, b)))) (by inj_tac)
instance : Ser AK := Ser.ofInj (fun (x : AK) => (x.1, x.2)) (by inj_tac)

/-- The 13 base actions as a nested sum. -/
abbrev BaseS := Unit ⊕ Bytes ⊕ (Bytes × Bytes × Nat × Nat) ⊕ Nat ⊕ (Nat × PublicKey) ⊕
  (PublicKey × AK) ⊕ PublicKey ⊕ Bytes ⊕ (PublicKey × Nat) ⊕ (PublicKey × Nat) ⊕
  D3.L4.DeployGlobal ⊕ D3.L4.UseGlobal ⊕ D3.L4.Dsi

def baseS : Base → BaseS
  | .createAccount => .inl ()
  | .deploy c => .inr (.inl c)
  | .fcall a b c d => .inr (.inr (.inl (a, b, c, d)))
  | .transfer n => .inr (.inr (.inr (.inl n)))
  | .stake n k => .inr (.inr (.inr (.inr (.inl (n, k)))))
  | .addKey k a => .inr (.inr (.inr (.inr (.inr (.inl (k, a))))))
  | .deleteKey k => .inr (.inr (.inr (.inr (.inr (.inr (.inl k))))))
  | .deleteAccount b => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl b)))))))
  | .toGasKey k n => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (k, n)))))))))
  | .fromGasKey k n => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (k, n))))))))))
  | .deployGlobal g => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl g))))))))))
  | .useGlobal g => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl g)))))))))))
  | .stateInit d => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr d)))))))))))

instance : Ser Base := Ser.ofInj baseS (by intro a b h; cases a <;> cases b <;> simp_all [baseS])
instance : Ser BaseAct := Ser.ofInj (fun (x : BaseAct) => (x.1, x.2)) (by inj_tac)
instance : Ser Delegate := Ser.ofInj
  (fun (x : Delegate) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10, x.11)) (by inj_tac)
instance : Ser Act := Ser.ofInj
  (fun | .base b => (.inl b : BaseAct ⊕ (Bytes × Delegate)) | .delegate s d => .inr (s, d))
  (by inj_tac)
instance : Ser ActionR := Ser.ofInj
  (fun (x : ActionR) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8)) (by inj_tac)
instance : Ser Distribution := Ser.ofInj
  (fun (x : Distribution) => (x.1, x.2, x.3, x.4, x.5, x.6)) (by inj_tac)
instance : Ser RBody := Ser.ofInj
  (fun | .action b a => (.inl (b, a) : (Bool × ActionR) ⊕ (Bool × Bytes × Option Bytes) ⊕ Distribution)
       | .data b x y => .inr (.inl (b, x, y)) | .distribution d => .inr (.inr d)) (by inj_tac)
instance : Ser Rcpt := Ser.ofInj (fun (x : Rcpt) => (x.1, x.2, x.3, x.4)) (by inj_tac)
instance : Ser TxD2 := Ser.ofInj
  (fun (x : TxD2) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10, x.11, x.12)) (by inj_tac)

instance : Ser RS := Ser.ofInj
  (fun (x : RS) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10, x.11, x.12, x.13, x.14,
    x.15, x.16, x.17, x.18, x.19)) (by inj_tac)

instance : Ser ObsDetail := Ser.ofInj (fun (x : ObsDetail) => (x.1, x.2, x.3)) (by inj_tac)
instance : Ser MainOutD2 := Ser.ofInj
  (fun (x : MainOutD2) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10, x.11, x.12, x.13))
  (by inj_tac)

instance : Ser Wasm.TTN.Recorder := Ser.ofInj (fun (x : Wasm.TTN.Recorder) => (x.1, x.2)) (by inj_tac)
instance : Ser Wasm.TTN.Acct := Ser.ofInj (fun (x : Wasm.TTN.Acct) => (x.1, x.2, x.3)) (by inj_tac)
instance : Ser Pipeline.Task := Ser.ofInj (fun (x : Pipeline.Task) => (x.1, x.2, x.3, x.4)) (by inj_tac)
instance : Ser Pipeline.Pipe := Ser.ofInj
  (fun (x : Pipeline.Pipe) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10)) (by inj_tac)
instance : Ser Recording := Ser.ofInj
  (fun (x : Recording) => (x.1, x.2, x.3, x.4, x.5, x.6, x.7, x.8, x.9, x.10)) (by inj_tac)

/-- The engine positions as a nested sum. -/
abbrev EPosS := Unit ⊕ (List (TxD2 × Bool) × List Bytes × RS) ⊕ (List Rcpt × RS) ⊕ (Nat × RS) ⊕
  (List Rcpt × RS) ⊕ (Nat × Nat × Nat × Nat × Nat × RS) ⊕ MainOutD2

def eposS : EPos → EPosS
  | .start => .inl ()
  | .txs a b c => .inr (.inl (a, b, c))
  | .locals a b => .inr (.inr (.inl (a, b)))
  | .delayed a b => .inr (.inr (.inr (.inl (a, b))))
  | .incoming a b => .inr (.inr (.inr (.inr (.inl (a, b)))))
  | .yields a b c d e f => .inr (.inr (.inr (.inr (.inr (.inl (a, b, c, d, e, f))))))
  | .done o => .inr (.inr (.inr (.inr (.inr (.inr o)))))

instance : Ser EPos := Ser.ofInj eposS (by intro a b h; cases a <;> cases b <;> simp_all [eposS])
instance : Ser EngSt := Ser.ofInj (fun (x : EngSt) => (x.1, x.2)) (by inj_tac)
instance : Ser StV := Ser.ofInj
  (fun | .none => (.inl () : Unit ⊕ (EPos × EngSt) ⊕ MainOutD2) | .eng p s => .inr (.inl (p, s))
       | .fin o => .inr (.inr o)) (by inj_tac)

/-! ## The state component's encoder -/

/-- **The serialisation of a state component** (lane B's `StViewE.encE`). -/
def encStV (v : StV) : Bytes := Ser.enc v

theorem encStV_pf : PF encStV := Ser.pf

/-- **Injectivity on every state component**; lane B's `encE_inj` (on stripped components) is the
special case `encStV_inj (strip a) (strip b)`. -/
theorem encStV_inj (a b : StV) (h : encStV a = encStV b) : a = b := encStV_pf.inj h

/-- Lane B's `StViewE.encE_inj` shape, for any `strip`. -/
theorem encStV_inj_on (strip : StV → StV) (a b : StV) (h : encStV (strip a) = encStV (strip b)) :
    strip a = strip b := encStV_inj _ _ h

/-! ## The remaining `StViewE` fields -/

/-- The working-set tree depth: `IX_BYTES = 3` in the circuit. -/
def wsDepth : Nat := 24

theorem wsDepth_lt : wsDepth < 64 := by decide

/-- **The change index** at a boundary: `0`. The circuit's change index is the timestamp of the
state lane's offline memory check inside a segment; a boundary commits the working set by its root
(`RCH`), so the timestamps restart at every boundary, and the index carries no information a
boundary must bind. (A running counter across boundaries is not a function of the configuration;
it would have to be carried in `EngSt` like the key list.) -/
def idxOf (_ : StV) : Nat := 0

theorem idxOf_lt (v : StV) : idxOf v < 2 ^ 64 := by simp [idxOf]

#print axioms encStV_inj
#print axioms encStV_inj_on
#print axioms keysOf_stOfK

end NearSpecV3.E2E.Enc
